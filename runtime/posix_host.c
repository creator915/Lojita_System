#define _GNU_SOURCE
#include "posix_host.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

static lean_object *buffer(size_t n) { return lean_alloc_sarray(1, n, n); }
static lean_object *copy_bytes(const void *src, size_t n) {
    lean_object *out = buffer(n);
    if (n) memcpy(lean_sarray_cptr(out), src, n);
    return out;
}
static lean_object *reply(int error, uint64_t value, lean_object *data) {
    lean_object *out = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(out, 0, lean_unsigned_to_nat(error));
    lean_ctor_set(out, 1, lean_uint64_to_nat(value));
    lean_ctor_set(out, 2, data ? data : buffer(0));
    return lean_io_result_mk_ok(out);
}
static lean_object *status(int64_t rc) {
    return rc < 0 ? reply(errno, 0, NULL) : reply(0, (uint64_t)rc, NULL);
}
static lean_object *read_result(lean_object *out, ssize_t count) {
    if (count < 0) {
        int e = errno;
        lean_dec(out);
        return reply(e, 0, NULL);
    }
    lean_sarray_set_size(out, count);
    return reply(0, count, out);
}
static lean_object *stat_result(const struct stat *st) {
    uint64_t v[] = {st->st_ino, st->st_mode & S_IFMT, st->st_mode & 07777,
                    st->st_nlink, st->st_size};
    return reply(0, 0, copy_bytes(v, sizeof v));
}
static void set_bit(tcflag_t *value, tcflag_t bit, int on) {
    if (on) *value |= bit; else *value &= ~bit;
}
static void wake_poll(int sig) { (void)sig; }

static int prepared;
static sigset_t entry_mask;
static struct sigaction entry_interrupt;

static int thread_mask(int how, const sigset_t *set, sigset_t *old) {
    int error = pthread_sigmask(how, set, old);
    if (error) { errno = error; return -1; }
    return 0;
}

/* Called by the verified ELF entry before Lean starts any runtime workers.
   All workers inherit the blocked mask. Only the object program thread waits. */
int lojita_posix_prepare_signals(void) {
    sigset_t set;
    sigemptyset(&set); sigaddset(&set, SIGINT); sigaddset(&set, SIGWINCH);
    if (thread_mask(SIG_BLOCK, &set, &entry_mask) < 0 ||
        sigaction(SIGINT, NULL, &entry_interrupt) < 0) return -1;
    struct sigaction resize = {.sa_handler = wake_poll};
    sigemptyset(&resize.sa_mask);
    if (sigaction(SIGWINCH, &resize, NULL) < 0) return -1;
    prepared = 1;
    return 0;
}

static int enter_program(void) {
    sigset_t one;
    sigemptyset(&one); sigaddset(&one, SIGWINCH);
    if (thread_mask(SIG_BLOCK, &one, NULL) < 0) return -1;
    struct sigaction resize = {.sa_handler = wake_poll};
    sigemptyset(&resize.sa_mask);
    if (sigaction(SIGWINCH, &resize, NULL) < 0) return -1;
    if (!prepared) return 0;
    if (sigaction(SIGINT, &entry_interrupt, NULL) < 0) return -1;
    sigemptyset(&one); sigaddset(&one, SIGINT);
    return thread_mask(sigismember(&entry_mask,SIGINT) ? SIG_BLOCK : SIG_UNBLOCK, &one, NULL);
}

static int poll_signals(struct pollfd *fds, size_t n, const struct timespec *timeout, int catch) {
    if (!catch) {
        sigset_t mask;
        if (thread_mask(SIG_SETMASK,NULL,&mask) < 0) return -1;
        sigaddset(&mask,SIGWINCH);
        return ppoll(fds,n,timeout,&mask);
    }
    sigset_t block, saved, wait_mask;
    sigemptyset(&block); sigaddset(&block,SIGINT); sigaddset(&block,SIGWINCH);
    if (thread_mask(SIG_BLOCK,&block,&saved) < 0) return -1;
    struct sigaction wake = {.sa_handler = wake_poll}, previous;
    sigemptyset(&wake.sa_mask);
    int rc = sigaction(SIGINT,&wake,&previous), error = errno;
    if (!rc) {
        wait_mask = saved;
        sigdelset(&wait_mask,SIGINT); sigdelset(&wait_mask,SIGWINCH);
        rc = ppoll(fds,n,timeout,&wait_mask);
        error = errno;
        if (sigaction(SIGINT,&previous,NULL) < 0) { rc = -1; error = errno; }
    }
    if (thread_mask(SIG_SETMASK,&saved,NULL) < 0) return -1;
    errno = error;
    return rc;
}

/* Byte arrays containing path arguments include a trailing zero supplied by the
   trusted marshaller. No path traversal, retries or event loop run here.
   The wire layout uses the target Ubuntu amd64 little-endian ABI. */
LEAN_EXPORT lean_obj_res lojita_posix_call(uint32_t code, uint64_t a, uint64_t b,
        uint64_t c, b_lean_obj_arg x, b_lean_obj_arg y) {
    const char *p = (const char *)lean_sarray_cptr(x);
    const char *q = (const char *)lean_sarray_cptr(y);
    const size_t nx = lean_sarray_size(x);
    int fd = (int)a, pair[2];
    struct stat st;
    struct winsize ws = {0};
    struct termios t;
    struct timespec ts;
    switch (code) {
    case 0: case 2: {
        size_t n = b > 0x7ffff000 ? 0x7ffff000 : (size_t)b;
        lean_object *out = buffer(n);
        ssize_t k = code == 0 ? read(fd, lean_sarray_cptr(out), n) :
                               pread(fd, lean_sarray_cptr(out), n, (off_t)c);
        return read_result(out, k);
    }
    case 1: return status(write(fd, p, nx));
    case 3: return status(pwrite(fd, p, nx, (off_t)c));
    case 4: return status(lseek(fd, (off_t)b, (int)c));
    case 5: return status(close(fd));
    case 6: return status(dup2(fd, (int)b));
    case 7: return status(fcntl(fd, F_GETFL));
    case 8: return status(fcntl(fd, F_SETFL, (int)b));
    case 9: return status(fcntl(fd, F_SETFD, b ? FD_CLOEXEC : 0));
    case 10:
        if (pipe2(pair, (a ? O_NONBLOCK : 0) | (b ? O_CLOEXEC : 0)) < 0) return status(-1);
        return reply(0, pair[0], copy_bytes(&pair[1], sizeof(int)));
    case 11: {
        if (nx % 8) return reply(EINVAL, 0, NULL);
        size_t n = nx / 8;
        struct pollfd *fds = calloc(n ? n : 1, sizeof *fds);
        if (!fds) return reply(ENOMEM, 0, NULL);
        for (size_t i = 0; i < n; ++i) {
            memcpy(&fds[i].fd, p + 8*i, 4);
            memcpy(&fds[i].events, p + 8*i + 4, 2);
        }
        ts = (struct timespec){a / 1000, (a % 1000) * 1000000};
        int rc = poll_signals(fds,n,b ? &ts : NULL,c != 0);
        int e = rc < 0 ? errno : 0;
        lean_object *out = buffer(e ? 0 : 2*n);
        if (!e) for (size_t i = 0; i < n; ++i)
            memcpy(lean_sarray_cptr(out) + 2*i, &fds[i].revents, 2);
        free(fds);
        return reply(e, 0, out);
    }
    case 12: if (fstat(fd, &st)) return status(-1); return stat_result(&st);
    case 13: return status(openat(fd, p, (int)b, (mode_t)c));
    case 14: return status(mkdirat(fd, p, (mode_t)b));
    case 15: return status(unlinkat(fd, p, b ? AT_REMOVEDIR : 0));
    case 16: return status(symlinkat(q, fd, p));
    case 17: return status(renameat(fd, p, (int)b, q));
    case 18: {
        lean_object *out = buffer(PATH_MAX);
        return read_result(out, readlinkat(fd, p, (char *)lean_sarray_cptr(out), PATH_MAX));
    }
    case 19:
        if (fstatat(fd, p, &st, b ? 0 : AT_SYMLINK_NOFOLLOW)) return status(-1);
        return stat_result(&st);
    case 20: return status(chdir(p));
    case 21: {
        char *cwd = getcwd(NULL, 0);
        if (!cwd) return status(-1);
        lean_object *out = copy_bytes(cwd, strlen(cwd));
        free(cwd);
        return reply(0, 0, out);
    }
    case 22:
        if (tcgetattr(fd, &t)) return status(-1);
        return reply(0, !!(t.c_lflag & ICANON) + 2*!!(t.c_lflag & ECHO) +
            4*!!(t.c_lflag & ISIG) + 8*!!(t.c_iflag & ICRNL) +
            16*!!(t.c_oflag & OPOST), copy_bytes(&t, sizeof t));
    case 23:
        if (nx != sizeof t) return reply(EINVAL, 0, NULL);
        memcpy(&t, p, sizeof t);
        if (!b) cfmakeraw(&t);
        set_bit(&t.c_lflag, ICANON, b & 1);
        set_bit(&t.c_lflag, ECHO, b & 2);
        set_bit(&t.c_lflag, ISIG, b & 4);
        set_bit(&t.c_iflag, ICRNL, b & 8);
        set_bit(&t.c_oflag, OPOST, b & 16);
        return status(tcsetattr(fd, TCSANOW, &t));
    case 24:
        if (ioctl(fd, TIOCGWINSZ, &ws)) return status(-1);
        return reply(0, ws.ws_row, copy_bytes(&ws.ws_col, sizeof ws.ws_col));
    case 25:
        ws.ws_row = (unsigned short)b; ws.ws_col = (unsigned short)c;
        return status(ioctl(fd, TIOCSWINSZ, &ws));
    case 26:
        if (isatty(fd)) return status(1);
        return errno == ENOTTY ? status(0) : status(-1);
    case 27: return status(socket(AF_INET, SOCK_STREAM | (a ? SOCK_NONBLOCK : 0) |
                                      (b ? SOCK_CLOEXEC : 0), 0));
    case 28: {
        struct sockaddr_in addr = {.sin_family = AF_INET, .sin_port = htons((uint16_t)b),
                                   .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
        return status(connect(fd, (struct sockaddr *)&addr, sizeof addr));
    }
    case 29: return status(shutdown(fd, (int)b));
    case 30:
        if (clock_gettime(CLOCK_MONOTONIC, &ts)) return status(-1);
        return reply(0, (uint64_t)ts.tv_sec * 1000000000 + ts.tv_nsec, NULL);
    case 31:
        ts = (struct timespec){a / 1000000000, a % 1000000000};
        return status(nanosleep(&ts, NULL));
    case 32: {
        const char *value = getenv(p);
        return reply(0, value != NULL, value ? copy_bytes(value, strlen(value)) : NULL);
    }
    case 33: {
        if (a) return status(enter_program());
        struct sigaction action = {.sa_handler = SIG_IGN};
        sigemptyset(&action.sa_mask);
        return status(sigaction(SIGPIPE,&action,NULL));
    }
    default: return reply(ENOSYS, 0, NULL);
    }
}
