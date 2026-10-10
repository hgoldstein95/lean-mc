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
 * A table of meshes in numbered slots. Lean chooses the slot, so there is no
 * allocation logic here. `LeanMc.Gpu` in Core/Render.lean is the model of this
 * section, and the tests compare the two; keep them in step.
 *
 * A mesh is a byte array of non-indexed triangle vertices, 8 bytes each:
 *
 *   [0] x  [1] y  [2] z   position in whole blocks, chunk-local
 *   [3] u  [4] v          texture corner in atlas tiles (atlas is 16x16 tiles)
 *   [5] shade             brightness, 0..255
 *   [6] normal            face direction 0..5 = +x -x +y -y +z -z
 *   [7] reserved
 *
 * A misuse (a bad slot, a malformed mesh, drawing or emptying an empty slot)
 * does nothing except set the fault flag.
 */

#define LMC_VERTEX_BYTES 8
#define LMC_TRIANGLE_BYTES 24
#define LMC_ATLAS_TILES 16.0f
#define LMC_MAX_MESHES 16384
#define LMC_SCENE_LOG 8192

static Mesh g_meshes[LMC_MAX_MESHES];
static bool g_mesh_live[LMC_MAX_MESHES];
static bool g_fault = false;

/*
 * The draws made since the scene began, for the tests to read back. The log
 * holds the first LMC_SCENE_LOG of them; the total counts them all.
 */
static double g_scene[LMC_SCENE_LOG][4];
static size_t g_scene_count = 0;
static uint32_t g_scene_total = 0;

static const float g_normals[6][3] = {
    {1, 0, 0}, {-1, 0, 0}, {0, 1, 0}, {0, -1, 0}, {0, 0, 1}, {0, 0, -1},
};

/* What one packed vertex means. Everything that reads a vertex goes through here. */
static void lmc_decode_vertex(const uint8_t *v, float *pos, float *uv, float *nrm,
                              unsigned char *col) {
    pos[0] = (float)v[0];
    pos[1] = (float)v[1];
    pos[2] = (float)v[2];
    uv[0] = (float)v[3] / LMC_ATLAS_TILES;
    uv[1] = (float)v[4] / LMC_ATLAS_TILES;
    const float *n = g_normals[v[6] < 6 ? v[6] : 0];
    nrm[0] = n[0];
    nrm[1] = n[1];
    nrm[2] = n[2];
    col[0] = v[5];
    col[1] = v[5];
    col[2] = v[5];
    col[3] = 255;
}

lean_obj_res lmc_mesh_upload(uint32_t slot, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    if (slot == 0 || slot >= LMC_MAX_MESHES || size == 0 || size % LMC_TRIANGLE_BYTES != 0) {
        g_fault = true;
        return LMC_UNIT;
    }
    if (g_mesh_live[slot]) UnloadMesh(g_meshes[slot]);

    size_t n = size / LMC_VERTEX_BYTES;
    const uint8_t *src = lean_sarray_cptr(bytes);
    Mesh mesh = {0};
    mesh.vertexCount = (int)n;
    mesh.triangleCount = (int)(n / 3);
    mesh.vertices = (float *)MemAlloc((unsigned int)(n * 3 * sizeof(float)));
    mesh.texcoords = (float *)MemAlloc((unsigned int)(n * 2 * sizeof(float)));
    mesh.normals = (float *)MemAlloc((unsigned int)(n * 3 * sizeof(float)));
    mesh.colors = (unsigned char *)MemAlloc((unsigned int)(n * 4));
    for (size_t i = 0; i < n; i++) {
        lmc_decode_vertex(src + i * LMC_VERTEX_BYTES, mesh.vertices + i * 3,
                          mesh.texcoords + i * 2, mesh.normals + i * 3, mesh.colors + i * 4);
    }
    UploadMesh(&mesh, false);
    g_meshes[slot] = mesh;
    g_mesh_live[slot] = true;
    return LMC_UNIT;
}

lean_obj_res lmc_mesh_unload(uint32_t slot) {
    if (slot >= LMC_MAX_MESHES || !g_mesh_live[slot]) {
        g_fault = true;
        return LMC_UNIT;
    }
    UnloadMesh(g_meshes[slot]);
    g_mesh_live[slot] = false;
    return LMC_UNIT;
}

/* Start a scene with nothing drawn. */
lean_obj_res lmc_scene_begin(void) {
    g_scene_count = 0;
    g_scene_total = 0;
    return LMC_UNIT;
}

lean_obj_res lmc_mesh_draw(uint32_t slot, double tx, double ty, double tz) {
    if (slot >= LMC_MAX_MESHES || !g_mesh_live[slot]) {
        g_fault = true;
        return LMC_UNIT;
    }
    DrawMesh(g_meshes[slot], g_material, MatrixTranslate((float)tx, (float)ty, (float)tz));
    if (g_scene_count < LMC_SCENE_LOG) {
        g_scene[g_scene_count][0] = (double)slot;
        g_scene[g_scene_count][1] = tx;
        g_scene[g_scene_count][2] = ty;
        g_scene[g_scene_count][3] = tz;
        g_scene_count++;
    }
    g_scene_total++;
    return LMC_UNIT;
}

/* ---- Read-back, for tests ------------------------------------------------ */

static lean_obj_res lmc_float_array(size_t n) {
    lean_object *arr = lean_alloc_sarray(sizeof(double), n, n);
    return arr;
}

/* Twelve numbers per vertex: position, texture coordinate, normal, colour. */
static void lmc_write_vertex(double *out, const float *pos, const float *uv, const float *nrm,
                             const unsigned char *col) {
    out[0] = pos[0]; out[1] = pos[1]; out[2] = pos[2];
    out[3] = uv[0];  out[4] = uv[1];
    out[5] = nrm[0]; out[6] = nrm[1]; out[7] = nrm[2];
    out[8] = col[0]; out[9] = col[1]; out[10] = col[2]; out[11] = col[3];
}

/* How this shim reads packed vertices, without touching the graphics card. */
lean_obj_res lmc_debug_decode(b_lean_obj_arg bytes) {
    size_t n = lean_sarray_size(bytes) / LMC_VERTEX_BYTES;
    const uint8_t *src = lean_sarray_cptr(bytes);
    lean_object *arr = lmc_float_array(n * 12);
    double *out = (double *)lean_sarray_cptr(arr);
    for (size_t i = 0; i < n; i++) {
        float pos[3], uv[2], nrm[3];
        unsigned char col[4];
        lmc_decode_vertex(src + i * LMC_VERTEX_BYTES, pos, uv, nrm, col);
        lmc_write_vertex(out + i * 12, pos, uv, nrm, col);
    }
    return lean_io_result_mk_ok(arr);
}

/* The vertices a slot holds, as uploaded; empty if the slot is empty. */
lean_obj_res lmc_debug_mesh(uint32_t slot) {
    if (slot >= LMC_MAX_MESHES || !g_mesh_live[slot]) {
        return lean_io_result_mk_ok(lmc_float_array(0));
    }
    Mesh *m = &g_meshes[slot];
    size_t n = (size_t)m->vertexCount;
    lean_object *arr = lmc_float_array(n * 12);
    double *out = (double *)lean_sarray_cptr(arr);
    for (size_t i = 0; i < n; i++) {
        lmc_write_vertex(out + i * 12, m->vertices + i * 3, m->texcoords + i * 2,
                         m->normals + i * 3, m->colors + i * 4);
    }
    return lean_io_result_mk_ok(arr);
}

lean_obj_res lmc_debug_mesh_live(uint32_t slot) {
    return LMC_BOOL(slot < LMC_MAX_MESHES && g_mesh_live[slot]);
}

/* How many slots hold a mesh. */
lean_obj_res lmc_debug_live_count(void) {
    uint32_t n = 0;
    for (uint32_t i = 0; i < LMC_MAX_MESHES; i++) {
        if (g_mesh_live[i]) n++;
    }
    return LMC_U32(n);
}

/* How many draws there have been since the scene began, logged or not. */
lean_obj_res lmc_debug_scene_total(void) { return LMC_U32(g_scene_total); }

/* The first LMC_SCENE_LOG draws since the scene began: four numbers each, slot then offset. */
lean_obj_res lmc_debug_scene(void) {
    lean_object *arr = lmc_float_array(g_scene_count * 4);
    double *out = (double *)lean_sarray_cptr(arr);
    for (size_t i = 0; i < g_scene_count; i++) {
        for (int k = 0; k < 4; k++) out[i * 4 + k] = g_scene[i][k];
    }
    return lean_io_result_mk_ok(arr);
}

lean_obj_res lmc_debug_fault(void) { return LMC_BOOL(g_fault); }

/*
 * The colour, as 0xRRGGBBAA, of the frame being drawn at the point (fx, fy),
 * given as fractions of the screen's width and height from its top left.
 */
lean_obj_res lmc_debug_pixel(double fx, double fy) {
    rlDrawRenderBatchActive(); /* flush batched drawing so it is in the readback */
    Image img = LoadImageFromScreen();
    int x = (int)(fx * img.width);
    int y = (int)(fy * img.height);
    if (x < 0) x = 0;
    if (y < 0) y = 0;
    if (x >= img.width) x = img.width - 1;
    if (y >= img.height) y = img.height - 1;
    Color c = GetImageColor(img, x, y);
    UnloadImage(img);
    return LMC_U32(((uint32_t)c.r << 24) | ((uint32_t)c.g << 16) | ((uint32_t)c.b << 8) | c.a);
}

/* Empty every slot and clear the scene and the fault flag. */
lean_obj_res lmc_debug_reset(void) {
    for (uint32_t i = 0; i < LMC_MAX_MESHES; i++) {
        if (g_mesh_live[i]) {
            UnloadMesh(g_meshes[i]);
            g_mesh_live[i] = false;
        }
    }
    g_scene_count = 0;
    g_scene_total = 0;
    g_fault = false;
    return LMC_UNIT;
}

/* Outline the box with minimum corner (x, y, z) and the given size; call in 3D mode. */
lean_obj_res lmc_draw_box_wires(double x, double y, double z, double sx, double sy, double sz,
                                uint32_t rgba) {
    Vector3 centre = {(float)(x + sx / 2), (float)(y + sy / 2), (float)(z + sz / 2)};
    DrawCubeWires(centre, (float)sx, (float)sy, (float)sz, lmc_color(rgba));
    return LMC_UNIT;
}

/*
 * Draw a solid box in 3D mode, as part of a creature. The box has minimum
 * corner (x, y, z) and the given size in a frame that is turned by `turn`
 * degrees about the vertical axis and then moved to (px, py, pz). Each face is
 * shaded by the way it points, more gently than the faces of blocks are.
 */
lean_obj_res lmc_draw_box(double px, double py, double pz, double turn, double x, double y,
                          double z, double sx, double sy, double sz, uint32_t rgba) {
    /* The corners of each face, counter-clockwise seen from outside; bit 0 is x, 1 is y, 2 is z. */
    static const int faces[6][4] = {
        {1, 3, 7, 5}, {0, 4, 6, 2}, {2, 6, 7, 3}, {0, 1, 5, 4}, {4, 5, 7, 6}, {0, 2, 3, 1},
    };
    /* The two triangles of a face, and the brightness of each face. */
    static const int order[6] = {0, 1, 2, 0, 2, 3};
    static const int shades[6] = {225, 225, 255, 160, 205, 205};
    Color c = lmc_color(rgba);
    float lo[3] = {(float)x, (float)y, (float)z};
    float hi[3] = {(float)(x + sx), (float)(y + sy), (float)(z + sz)};
    rlPushMatrix();
    rlTranslatef((float)px, (float)py, (float)pz);
    rlRotatef((float)turn, 0.0f, 1.0f, 0.0f);
    rlBegin(RL_TRIANGLES);
    for (int f = 0; f < 6; f++) {
        rlColor4ub((unsigned char)(c.r * shades[f] / 255), (unsigned char)(c.g * shades[f] / 255),
                   (unsigned char)(c.b * shades[f] / 255), c.a);
        rlNormal3f(g_normals[f][0], g_normals[f][1], g_normals[f][2]);
        for (int i = 0; i < 6; i++) {
            int corner = faces[f][order[i]];
            rlVertex3f(corner & 1 ? hi[0] : lo[0], corner & 2 ? hi[1] : lo[1],
                       corner & 4 ? hi[2] : lo[2]);
        }
    }
    rlEnd();
    rlPopMatrix();
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

/* Draw one tile of the block atlas as a square, for the hotbar. */
lean_obj_res lmc_draw_tile(uint32_t tile, uint32_t x, uint32_t y, uint32_t size) {
    if (!g_has_atlas) return LMC_UNIT;
    float t = (float)g_atlas.width / LMC_ATLAS_TILES;
    Rectangle src = {(float)(tile % 16) * t, (float)(tile / 16) * t, t, t};
    Rectangle dst = {(float)x, (float)y, (float)size, (float)size};
    DrawTexturePro(g_atlas, src, dst, (Vector2){0, 0}, 0.0f, WHITE);
    return LMC_UNIT;
}

lean_obj_res lmc_draw_rect(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t rgba) {
    DrawRectangle((int)x, (int)y, (int)w, (int)h, lmc_color(rgba));
    return LMC_UNIT;
}
