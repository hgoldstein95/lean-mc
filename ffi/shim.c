/*
 * lean-mc native shim: the only C in the project.
 *
 * Everything here is part of the trusted base. It is deliberately thin: it
 * owns the window, the GPU objects and raw input, and makes no game decisions.
 *
 * ABI notes (Lean 4.34): `IO` externs take no world token and return an IO
 * result object; `Float` is passed as an unboxed double, `UIntN` as uintN_t,
 * and `@&` arguments are borrowed.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "raylib.h"
#include "raymath.h"
#include "rlgl.h"

#define LMC_UNIT lean_io_result_mk_ok(lean_box(0))
#define LMC_BOOL(b) lean_io_result_mk_ok(lean_box((b) ? 1 : 0))
#define LMC_FLOAT(d) lean_io_result_mk_ok(lean_box_float(d))
#define LMC_U32(u) lean_io_result_mk_ok(lean_box_uint32(u))

static inline Color lmc_color(uint32_t rgba) {
    return (Color){(rgba >> 24) & 0xff, (rgba >> 16) & 0xff, (rgba >> 8) & 0xff, rgba & 0xff};
}

/* ---- Window and frame ---------------------------------------------------- */

static Material g_material;
static bool g_has_atlas = false;
static Texture2D g_atlas;

lean_obj_res lmc_init_window(uint32_t width, uint32_t height, b_lean_obj_arg title) {
    SetTraceLogLevel(LOG_WARNING);
    SetConfigFlags(FLAG_VSYNC_HINT | FLAG_WINDOW_RESIZABLE);
    InitWindow((int)width, (int)height, lean_string_cstr(title));
    SetExitKey(KEY_NULL);
    g_material = LoadMaterialDefault();
    return LMC_UNIT;
}

lean_obj_res lmc_close_window(void) {
    CloseWindow();
    return LMC_UNIT;
}

lean_obj_res lmc_window_should_close(void) { return LMC_BOOL(WindowShouldClose()); }
lean_obj_res lmc_screen_width(void) { return LMC_U32((uint32_t)GetScreenWidth()); }
lean_obj_res lmc_screen_height(void) { return LMC_U32((uint32_t)GetScreenHeight()); }
lean_obj_res lmc_frame_time(void) { return LMC_FLOAT((double)GetFrameTime()); }

lean_obj_res lmc_begin_frame(uint32_t rgba) {
    BeginDrawing();
    ClearBackground(lmc_color(rgba));
    return LMC_UNIT;
}

lean_obj_res lmc_end_frame(void) {
    EndDrawing();
    return LMC_UNIT;
}

lean_obj_res lmc_begin_3d(double px, double py, double pz, double tx, double ty, double tz,
                          double fovy) {
    Camera3D cam = {0};
    cam.position = (Vector3){(float)px, (float)py, (float)pz};
    cam.target = (Vector3){(float)tx, (float)ty, (float)tz};
    cam.up = (Vector3){0.0f, 1.0f, 0.0f};
    cam.fovy = (float)fovy;
    cam.projection = CAMERA_PERSPECTIVE;
    BeginMode3D(cam);
    return LMC_UNIT;
}

lean_obj_res lmc_end_3d(void) {
    EndMode3D();
    return LMC_UNIT;
}

lean_obj_res lmc_take_screenshot(b_lean_obj_arg path) {
    rlDrawRenderBatchActive(); /* flush batched 2D so it is in the readback */
    Image img = LoadImageFromScreen();
    ExportImage(img, lean_string_cstr(path));
    UnloadImage(img);
    return LMC_UNIT;
}

/* ---- Input --------------------------------------------------------------- */

lean_obj_res lmc_key_down(uint32_t key) { return LMC_BOOL(IsKeyDown((int)key)); }
lean_obj_res lmc_key_pressed(uint32_t key) { return LMC_BOOL(IsKeyPressed((int)key)); }
lean_obj_res lmc_mouse_down(uint32_t button) { return LMC_BOOL(IsMouseButtonDown((int)button)); }
lean_obj_res lmc_mouse_pressed(uint32_t button) {
    return LMC_BOOL(IsMouseButtonPressed((int)button));
}
lean_obj_res lmc_mouse_dx(void) { return LMC_FLOAT((double)GetMouseDelta().x); }
lean_obj_res lmc_mouse_dy(void) { return LMC_FLOAT((double)GetMouseDelta().y); }
lean_obj_res lmc_mouse_wheel(void) { return LMC_FLOAT((double)GetMouseWheelMove()); }

lean_obj_res lmc_set_cursor_captured(uint8_t captured) {
    if (captured) DisableCursor(); else EnableCursor();
    return LMC_UNIT;
}

/* ---- Meshes --------------------------------------------------------------
 *
 * Lean hands over a byte array of non-indexed triangle vertices, 8 bytes each:
 *
 *   [0] x  [1] y  [2] z   position in whole blocks, chunk-local
 *   [3] u  [4] v          texture corner in atlas tiles (atlas is 16x16 tiles)
 *   [5] shade             brightness, 0..255
 *   [6] normal            face direction 0..5 = +x -x +y -y +z -z
 *   [7] reserved
 *
 * Handle 0 is "no mesh"; drawing or unloading it is a no-op.
 */

#define LMC_VERTEX_BYTES 8
#define LMC_ATLAS_TILES 16.0f
#define LMC_MAX_MESHES 16384

static Mesh g_meshes[LMC_MAX_MESHES];
static bool g_mesh_used[LMC_MAX_MESHES];

static const float g_normals[6][3] = {
    {1, 0, 0}, {-1, 0, 0}, {0, 1, 0}, {0, -1, 0}, {0, 0, 1}, {0, 0, -1},
};

lean_obj_res lmc_upload_mesh(b_lean_obj_arg bytes) {
    size_t n = lean_sarray_size(bytes) / LMC_VERTEX_BYTES;
    n -= n % 3;
    if (n == 0) return LMC_U32(0);

    uint32_t id = 0;
    for (uint32_t i = 1; i < LMC_MAX_MESHES; i++) {
        if (!g_mesh_used[i]) { id = i; break; }
    }
    if (id == 0) return LMC_U32(0);

    const uint8_t *src = lean_sarray_cptr(bytes);
    Mesh mesh = {0};
    mesh.vertexCount = (int)n;
    mesh.triangleCount = (int)(n / 3);
    mesh.vertices = (float *)MemAlloc((unsigned int)(n * 3 * sizeof(float)));
    mesh.texcoords = (float *)MemAlloc((unsigned int)(n * 2 * sizeof(float)));
    mesh.normals = (float *)MemAlloc((unsigned int)(n * 3 * sizeof(float)));
    mesh.colors = (unsigned char *)MemAlloc((unsigned int)(n * 4));

    for (size_t i = 0; i < n; i++) {
        const uint8_t *v = src + i * LMC_VERTEX_BYTES;
        mesh.vertices[i * 3 + 0] = (float)v[0];
        mesh.vertices[i * 3 + 1] = (float)v[1];
        mesh.vertices[i * 3 + 2] = (float)v[2];
        mesh.texcoords[i * 2 + 0] = (float)v[3] / LMC_ATLAS_TILES;
        mesh.texcoords[i * 2 + 1] = (float)v[4] / LMC_ATLAS_TILES;
        const float *nrm = g_normals[v[6] < 6 ? v[6] : 0];
        mesh.normals[i * 3 + 0] = nrm[0];
        mesh.normals[i * 3 + 1] = nrm[1];
        mesh.normals[i * 3 + 2] = nrm[2];
        mesh.colors[i * 4 + 0] = v[5];
        mesh.colors[i * 4 + 1] = v[5];
        mesh.colors[i * 4 + 2] = v[5];
        mesh.colors[i * 4 + 3] = 255;
    }

    UploadMesh(&mesh, false);
    g_meshes[id] = mesh;
    g_mesh_used[id] = true;
    return LMC_U32(id);
}

lean_obj_res lmc_draw_mesh(uint32_t id, double tx, double ty, double tz) {
    if (id == 0 || id >= LMC_MAX_MESHES || !g_mesh_used[id]) return LMC_UNIT;
    DrawMesh(g_meshes[id], g_material, MatrixTranslate((float)tx, (float)ty, (float)tz));
    return LMC_UNIT;
}

lean_obj_res lmc_unload_mesh(uint32_t id) {
    if (id == 0 || id >= LMC_MAX_MESHES || !g_mesh_used[id]) return LMC_UNIT;
    UnloadMesh(g_meshes[id]);
    g_mesh_used[id] = false;
    return LMC_UNIT;
}

/* Replace the block atlas with a width*height RGBA8 image. */
lean_obj_res lmc_set_atlas(uint32_t width, uint32_t height, b_lean_obj_arg rgba) {
    if (lean_sarray_size(rgba) < (size_t)width * height * 4) return LMC_UNIT;
    Image img = {0};
    img.data = lean_sarray_cptr(rgba);
    img.width = (int)width;
    img.height = (int)height;
    img.mipmaps = 1;
    img.format = PIXELFORMAT_UNCOMPRESSED_R8G8B8A8;
    if (g_has_atlas) UnloadTexture(g_atlas);
    g_atlas = LoadTextureFromImage(img);
    SetTextureFilter(g_atlas, TEXTURE_FILTER_POINT);
    SetTextureWrap(g_atlas, TEXTURE_WRAP_CLAMP);
    g_has_atlas = true;
    g_material.maps[MATERIAL_MAP_DIFFUSE].texture = g_atlas;
    return LMC_UNIT;
}

/* ---- 2D overlay ---------------------------------------------------------- */

lean_obj_res lmc_draw_text(b_lean_obj_arg text, uint32_t x, uint32_t y, uint32_t size,
                           uint32_t rgba) {
    DrawText(lean_string_cstr(text), (int)x, (int)y, (int)size, lmc_color(rgba));
    return LMC_UNIT;
}

lean_obj_res lmc_draw_rect(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t rgba) {
    DrawRectangle((int)x, (int)y, (int)w, (int)h, lmc_color(rgba));
    return LMC_UNIT;
}

/* ---- Process entry point ---------------------------------------------------
 *
 * Lean's generated `main` runs the program on a worker thread, but macOS only
 * allows windows and events on the process's main thread. So the root module
 * defines no Lean `main`; it exports `lmc_main` instead, and this `main` does
 * the same runtime setup the generated one would before calling it directly.
 */

char **lean_setup_args(int argc, char **argv);
lean_object *initialize_leanmc_Main(uint8_t builtin);
lean_object *lmc_main(lean_object *args);

int main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_object *res = initialize_leanmc_Main(1);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
        lean_dec_ref(res);
        lean_init_task_manager();
        lean_object *args = lean_box(0);
        for (int i = argc - 1; i >= 1; i--) {
            lean_object *cell = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(cell, 0, lean_mk_string(argv[i]));
            lean_ctor_set(cell, 1, args);
            args = cell;
        }
        res = lmc_main(args);
    }
    lean_finalize_task_manager();
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    int code = (int)lean_unbox_uint32(lean_io_result_get_value(res));
    lean_dec_ref(res);
    return code;
}
