/*
 * Process entry point.
 *
 * Lean's generated `main` runs the program on a worker thread, but macOS only
 * allows windows and events on the process's main thread. So a program that
 * opens a window defines no Lean `main`; it exports an entry function instead,
 * and this `main` does the same runtime setup the generated one would before
 * calling it directly.
 *
 * Compile with -DLMC_INIT=<root module initialiser> -DLMC_ENTRY=<exported entry>.
 */
#include <lean/lean.h>

char **lean_setup_args(int argc, char **argv);
lean_object *LMC_INIT(uint8_t builtin);
lean_object *LMC_ENTRY(lean_object *args);

int main(int argc, char **argv) {
    argv = lean_setup_args(argc, argv);
    lean_object *res = LMC_INIT(1);
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
        res = LMC_ENTRY(args);
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
