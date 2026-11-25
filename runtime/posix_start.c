#include <errno.h>
#include <lean/lean.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

extern int lojita_posix_prepare_signals(void);
extern int __real_main(int argc, char **argv);
extern lean_obj_res lean_internal_set_thread_stack_size(size_t bytes);

/* Lean 4.36 initializes worker threads during module initialization, before
   lean_run_main reads its environment. Apply the caller's stack size before
   initialization. Only the verified POSIX executable links this entry point. */
int __wrap_main(int argc, char **argv) {
    if (lojita_posix_prepare_signals() < 0) return 125;
    const char *setting = getenv("LEAN_STACK_SIZE_KB");
    if (setting && *setting >= '0' && *setting <= '9') {
        char *end;
        errno = 0;
        unsigned long kb = strtoul(setting, &end, 10);
        if (!errno && !*end && kb && kb <= SIZE_MAX / 1024)
            lean_dec(lean_internal_set_thread_stack_size(kb * 1024));
    }
    /* The generated Lean main accepts UTF-8 strings. Carry arbitrary Linux
       argv bytes across that interface without mutating the process argv. */
    char **encoded = calloc((size_t)argc + 1, sizeof *encoded);
    if (!encoded) return 125;
    encoded[0] = argv[0];
    int result = 125;
    for (int i = 1; i < argc; ++i) {
        size_t n = strlen(argv[i]);
        if (n > (SIZE_MAX - 1) / 2) goto cleanup;
        encoded[i] = malloc(2*n + 1);
        if (!encoded[i]) goto cleanup;
        for (size_t j = 0; j < n; ++j) {
            unsigned char b = (unsigned char)argv[i][j];
            encoded[i][2*j] = "0123456789abcdef"[b >> 4];
            encoded[i][2*j+1] = "0123456789abcdef"[b & 15];
        }
        encoded[i][2*n] = 0;
    }
    result = __real_main(argc, encoded);
cleanup:
    for (int i = 1; i < argc; ++i) free(encoded[i]);
    free(encoded);
    return result;
}
