#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <unistd.h>
#include <lean/lean.h>

static lean_obj_res syscall_error(void) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(strerror(errno))));
}

LEAN_EXPORT lean_obj_res lojita_protect_check_worker(void) {
    // RLIMIT_CORE alone does not disable piped crash handlers on Linux.
    if (prctl(PR_SET_DUMPABLE, 0L, 0L, 0L, 0L) < 0)
        return syscall_error();

    // The Lean toolchain maps modules and reserves large thread arenas.
    // VmRSS is monitored separately by the parent. Preserve stricter soft limits.
    struct rlimit limit;
    const rlim_t ceiling = UINT64_C(6) << 30;
    if (getrlimit(RLIMIT_AS, &limit) < 0)
        return syscall_error();
    if (limit.rlim_cur > ceiling)
        limit.rlim_cur = ceiling;
    limit.rlim_max = limit.rlim_cur;
    if (setrlimit(RLIMIT_AS, &limit) < 0)
        return syscall_error();
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lojita_kill_check_worker(uint32_t pid) {
    if (kill((pid_t)pid, SIGKILL) < 0 && errno != ESRCH)
        return syscall_error();
    return lean_io_result_mk_ok(lean_box(0));
}
