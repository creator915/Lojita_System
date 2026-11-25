#define _GNU_SOURCE
#include "cli_host.h"

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <poll.h>
#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

#ifdef CT_HAVE_OPENSSL
typedef struct ssl_method_st SSL_METHOD;
typedef struct ssl_ctx_st SSL_CTX;
typedef struct ssl_st SSL;
typedef struct x509_store_ctx_st X509_STORE_CTX;
typedef struct X509_VERIFY_PARAM_st X509_VERIFY_PARAM;

extern const SSL_METHOD *TLS_client_method(void);
extern SSL_CTX *SSL_CTX_new(const SSL_METHOD *meth);
extern void SSL_CTX_free(SSL_CTX *ctx);
extern int SSL_CTX_set_default_verify_paths(SSL_CTX *ctx);
extern int SSL_CTX_load_verify_locations(SSL_CTX *ctx, const char *CAfile, const char *CApath);
extern void SSL_CTX_set_verify(SSL_CTX *ctx, int mode, int (*cb)(int, X509_STORE_CTX *));
extern SSL *SSL_new(SSL_CTX *ctx);
extern void SSL_free(SSL *ssl);
extern int SSL_set_fd(SSL *s, int fd);
extern long SSL_ctrl(SSL *ssl, int cmd, long larg, void *parg);
extern int SSL_set1_host(SSL *s, const char *hostname);
extern X509_VERIFY_PARAM *SSL_get0_param(SSL *ssl);
extern int X509_VERIFY_PARAM_set1_ip_asc(X509_VERIFY_PARAM *param, const char *ipasc);
extern int SSL_connect(SSL *ssl);
extern int SSL_write(SSL *ssl, const void *buf, int num);
extern int SSL_read(SSL *ssl, void *buf, int num);
extern int SSL_shutdown(SSL *ssl);
extern int SSL_get_error(const SSL *s, int ret_code);
extern long SSL_get_verify_result(const SSL *ssl);
extern const char *X509_verify_cert_error_string(long n);
extern unsigned long ERR_get_error(void);
extern void ERR_error_string_n(unsigned long e, char *buf, size_t len);

#define CT_SSL_VERIFY_NONE 0x00
#define CT_SSL_VERIFY_PEER 0x01
#define CT_SSL_CTRL_SET_TLSEXT_HOSTNAME 55
#define CT_SSL_ERROR_NONE 0
#define CT_SSL_ERROR_WANT_READ 2
#define CT_SSL_ERROR_WANT_WRITE 3
#define CT_SSL_ERROR_SYSCALL 5
#define CT_SSL_ERROR_ZERO_RETURN 6
#endif

static char *saved_prog_name = NULL;
static char **saved_args = NULL;
static int saved_argc = 0;
static int args_initialized = 0;
static int64_t boot_mono_ms = -1;

static int64_t ct_raw_mono_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static char *dup_cstr(const char *s) {
    if (!s) s = "";
    size_t n = strlen(s);
    char *p = (char *)malloc(n + 1);
    if (!p) return NULL;
    memcpy(p, s, n + 1);
    return p;
}

static void init_from_proc_cmdline(void) {
    if (args_initialized) return;
    args_initialized = 1;
    int fd = open("/proc/self/cmdline", O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        saved_prog_name = dup_cstr("");
        return;
    }
    size_t cap = 4096, len = 0;
    char *buf = (char *)malloc(cap);
    if (!buf) {
        close(fd);
        saved_prog_name = dup_cstr("");
        return;
    }
    for (;;) {
        if (len == cap) {
            cap *= 2;
            char *nb = (char *)realloc(buf, cap);
            if (!nb) { free(buf); close(fd); saved_prog_name = dup_cstr(""); return; }
            buf = nb;
        }
        ssize_t n = read(fd, buf + len, cap - len);
        if (n > 0) len += (size_t)n;
        else if (n == 0) break;
        else if (errno == EINTR) continue;
        else break;
    }
    close(fd);
    if (len == 0) {
        free(buf);
        saved_prog_name = dup_cstr("");
        return;
    }
    int total = 0;
    size_t pos = 0;
    while (pos < len) {
        size_t slen = strnlen(buf + pos, len - pos);
        total++;
        pos += slen + 1;
    }
    pos = 0;
    size_t slen0 = strnlen(buf, len);
    char *p0 = (char *)malloc(slen0 + 1);
    if (p0) {
        memcpy(p0, buf, slen0);
        p0[slen0] = '\0';
    }
    saved_prog_name = p0 ? p0 : dup_cstr("");
    pos = slen0 + 1;
    if (total > 1) {
        saved_argc = total - 1;
        saved_args = (char **)calloc((size_t)saved_argc, sizeof(char *));
        int idx = 0;
        while (pos < len && idx < saved_argc) {
            size_t sl = strnlen(buf + pos, len - pos);
            char *a = (char *)malloc(sl + 1);
            if (a) {
                memcpy(a, buf + pos, sl);
                a[sl] = '\0';
            }
            if (saved_args) saved_args[idx] = a ? a : dup_cstr("");
            idx++;
            pos += sl + 1;
        }
    }
    free(buf);
}

/* On Linux glibc (.init_array), constructors receive (argc, argv, envp)
 * directly from the process entry stack before main() runs, preserving exact
 * symlink argv[0] even in minimal containers without /proc mounted. */
__attribute__((constructor))
static void ct_capture_argv(int argc, char **argv, char **envp) {
    (void)envp;
    signal(SIGPIPE, SIG_IGN);
    if (boot_mono_ms < 0) boot_mono_ms = ct_raw_mono_ms();
    if (argc > 0 && argv && argv[0]) {
        args_initialized = 1;
        saved_prog_name = dup_cstr(argv[0]);
        if (argc > 1) {
            saved_argc = argc - 1;
            saved_args = (char **)calloc((size_t)saved_argc, sizeof(char *));
            if (saved_args) {
                for (int i = 0; i < saved_argc; ++i) {
                    saved_args[i] = dup_cstr(argv[i + 1] ? argv[i + 1] : "");
                }
            }
        }
    } else {
        init_from_proc_cmdline();
    }
}

/* --------------------------------------------------------------------------
 * §1 Clock Primitives (`clockCap`)
 * -------------------------------------------------------------------------- */

uint64_t ct_now_mono_ms(void) {
    if (boot_mono_ms < 0) boot_mono_ms = ct_raw_mono_ms();
    int64_t d = ct_raw_mono_ms() - boot_mono_ms;
    return d < 0 ? 0 : (uint64_t)d;
}

uint64_t ct_now_wall_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return 0;
    int64_t ms = (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
    return ms < 0 ? 0 : (uint64_t)ms;
}

void ct_sleep_ms(uint32_t ms) {
    if (ms == 0) return;
    struct timespec req, rem;
    req.tv_sec = (time_t)(ms / 1000);
    req.tv_nsec = (long)(ms % 1000) * 1000000L;
    while (nanosleep(&req, &rem) != 0) {
        if (errno != EINTR) break;
        req = rem;
    }
}

/* --------------------------------------------------------------------------
 * §2 Process environment (`envCap`)
 * -------------------------------------------------------------------------- */

const char *ct_get_prog_name(void) {
    if (!args_initialized) init_from_proc_cmdline();
    return saved_prog_name ? saved_prog_name : "";
}

int ct_get_argc(void) {
    if (!args_initialized) init_from_proc_cmdline();
    return saved_argc;
}

const char *ct_get_arg(int idx) {
    if (!args_initialized) init_from_proc_cmdline();
    if (idx < 0 || idx >= saved_argc || !saved_args || !saved_args[idx]) return "";
    return saved_args[idx];
}

const char *ct_lookup_env_n(const char *key, size_t key_len) {
    if (!key || key_len == 0 || memchr(key, '\0', key_len) != NULL || memchr(key, '=', key_len) != NULL) {
        return NULL;
    }
    char stack_k[256];
    char *heap_k = NULL;
    const char *k_cstr = stack_k;
    if (key_len < sizeof(stack_k)) {
        memcpy(stack_k, key, key_len);
        stack_k[key_len] = '\0';
    } else {
        heap_k = (char *)malloc(key_len + 1);
        if (!heap_k) return NULL;
        memcpy(heap_k, key, key_len);
        heap_k[key_len] = '\0';
        k_cstr = heap_k;
    }
    const char *val = getenv(k_cstr);
    if (heap_k) free(heap_k);
    return val;
}

/* --------------------------------------------------------------------------
 * §3 Standard streams, controlling terminal and reactive polling
 * -------------------------------------------------------------------------- */

int ct_is_tty(int fd) {
    return isatty(fd) ? 1 : 0;
}

static int tty_initialized = 0;
static int tty_rfd = -1;
static int tty_wfd = -1;
static struct termios saved_termios;
static int saved_termios_valid = 0;

static int same_chr_dev(int fd1, int fd2) {
    struct stat a, b;
    return fd1 >= 0 && fd2 >= 0 && fstat(fd1, &a) == 0 && fstat(fd2, &b) == 0 &&
           S_ISCHR(a.st_mode) && S_ISCHR(b.st_mode) && a.st_rdev == b.st_rdev;
}

static int open_tty(int mode) {
    int fd = open("/dev/tty", mode | O_NOCTTY | O_CLOEXEC);
    if (fd < 0 || fd > STDERR_FILENO) return fd;
    /* Keep a closed standard stream closed even if open() picked its number. */
    int tty_fd = fcntl(fd, F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
    int err = errno;
    close(fd);
    if (tty_fd < 0) errno = err;
    return tty_fd;
}

static int tty_missing(int err) {
    return err == ENOENT || err == ENXIO;
}

static void init_tty(void) {
    if (tty_initialized) return;
    tty_initialized = 1;
    tty_rfd = open_tty(O_RDWR);
    if (tty_rfd >= 0) {
        tty_wfd = tty_rfd;
        return;
    }
    int missing = tty_missing(errno);
    tty_rfd = open_tty(O_RDONLY);
    missing = missing && tty_rfd < 0 && tty_missing(errno);
    tty_wfd = open_tty(O_WRONLY);
    if (missing && tty_wfd < 0 && tty_missing(errno) && isatty(STDIN_FILENO)) {
        tty_rfd = STDIN_FILENO;
        if (isatty(STDOUT_FILENO) && same_chr_dev(STDIN_FILENO, STDOUT_FILENO)) {
            tty_wfd = STDOUT_FILENO;
        }
    }
}

int ct_has_tty(void) {
    init_tty();
    return tty_rfd >= 0 || tty_wfd >= 0;
}

static void ct_restore_tty_termios(void) {
    if (saved_termios_valid) {
        int fd = tty_rfd >= 0 ? tty_rfd : tty_wfd;
        (void)tcsetattr(fd, TCSANOW, &saved_termios);
    }
}

int ct_set_tty_raw(int enable) {
    init_tty();
    int fd = tty_rfd >= 0 ? tty_rfd : tty_wfd;
    if (fd < 0) return 0;
    if (!saved_termios_valid) {
        if (tcgetattr(fd, &saved_termios) != 0 || atexit(ct_restore_tty_termios) != 0) return 0;
        saved_termios_valid = 1;
    }
    if (enable) {
        struct termios raw = saved_termios;
        cfmakeraw(&raw);
        return tcsetattr(fd, TCSANOW, &raw) == 0;
    }
    return tcsetattr(fd, TCSANOW, &saved_termios) == 0;
}

void ct_term_size(uint32_t *out_rows, uint32_t *out_cols) {
    init_tty();
    int fds[] = {tty_rfd, tty_wfd, STDOUT_FILENO, STDIN_FILENO, STDERR_FILENO};
    uint32_t rows = 24, cols = 80;
    for (size_t i = 0; i < sizeof(fds) / sizeof(fds[0]); ++i) {
        struct winsize ws;
        if (fds[i] >= 0 && ioctl(fds[i], TIOCGWINSZ, &ws) == 0 && ws.ws_row > 0 && ws.ws_col > 0) {
            rows = ws.ws_row;
            cols = ws.ws_col;
            break;
        }
    }
    if (out_rows) *out_rows = rows;
    if (out_cols) *out_cols = cols;
}

int ct_write_fd_all(int fd, const uint8_t *buf, size_t len) {
    size_t off = 0;
    while (off < len) {
        ssize_t n = write(fd, buf + off, len - off);
        if (n > 0) {
            off += (size_t)n;
        } else if (n < 0 && errno == EINTR) {
            continue;
        } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            struct pollfd pfd = { .fd = fd, .events = POLLOUT, .revents = 0 };
            (void)poll(&pfd, 1, 50);
        } else {
            return -1;
        }
    }
    return 0;
}

int ct_write_tty_all(const uint8_t *buf, size_t len) {
    init_tty();
    if (tty_wfd < 0) return 0;
    if (len == 0) return 1;
    return ct_write_fd_all(tty_wfd, buf, len) == 0;
}

/* Only async-signal-safe transport lives here. Lean determines capabilities,
 * event priority, EOF state, chunk sizes, and timing through POSIX ppoll. */
static const int watched[] = {SIGINT, SIGTERM, SIGHUP, SIGQUIT, SIGWINCH};
static struct sigaction previous[sizeof watched / sizeof *watched];
/* One notification per distinct pending signal keeps the nonblocking pipe
 * bounded to five bytes, even if the application is busy processing input. */
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signals require lock-free host integers");
static pthread_mutex_t signal_lock = PTHREAD_MUTEX_INITIALIZER;
static int signal_input = -1;
static _Atomic int signal_output = -1;
static _Atomic unsigned active_handlers, queued_signals;

static void enqueue_signal(int signo) {
    int saved = errno;
    atomic_fetch_add(&active_handlers, 1);
    int fd = atomic_load(&signal_output);
    unsigned bit = 1u << signo;
    if (fd >= 0 && !(atomic_fetch_or(&queued_signals, bit) & bit)) {
        unsigned char byte = (unsigned char)signo;
        ssize_t n;
        do { n = write(fd, &byte, 1); } while (n < 0 && errno == EINTR);
    }
    atomic_fetch_sub(&active_handlers, 1);
    errno = saved;
}

/* A worker thread may still be returning from a signal handler after
 * sigaction restores the original disposition. Wait before recycling its fd. */
static void close_signals(int rd, int wr) {
    atomic_store(&signal_output, -1);
    while (atomic_load(&active_handlers)) sched_yield();
    close(wr);
    close(rd);
    signal_input = -1;
}

static int above_stdio(int fd) {
    if (fd > STDERR_FILENO) return fd;
    int result = fcntl(fd, F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
    int saved = errno;
    close(fd);
    errno = saved;
    return result;
}

static int begin_signals_locked(void) {
    if (signal_input >= 0) { errno = EBUSY; return -1; }
    int fds[2];
    if (pipe2(fds, O_NONBLOCK | O_CLOEXEC) < 0) return -1;
    int rd = above_stdio(fds[0]), wr = above_stdio(fds[1]);
    if (rd < 0 || wr < 0) {
        if (rd >= 0) close(rd);
        if (wr >= 0) close(wr);
        return -1;
    }
    signal_input = rd;
    atomic_store(&queued_signals, 0);
    atomic_store(&signal_output, wr);
    struct sigaction action = {0};
    action.sa_handler = enqueue_signal;
    sigemptyset(&action.sa_mask);
    for (size_t i = 0; i < sizeof watched / sizeof *watched; i++) {
        if (sigaction(watched[i], &action, &previous[i]) < 0) {
            int saved = errno;
            while (i > 0) { --i; (void)sigaction(watched[i], &previous[i], NULL); }
            close_signals(rd, wr);
            errno = saved;
            return -1;
        }
    }
    return rd;
}

static int begin_signals(void) {
    pthread_mutex_lock(&signal_lock);
    int fd = begin_signals_locked();
    pthread_mutex_unlock(&signal_lock);
    return fd;
}

static void end_signals(void) {
    pthread_mutex_lock(&signal_lock);
    if (signal_input >= 0) {
        for (size_t i = 0; i < sizeof watched / sizeof *watched; i++)
            (void)sigaction(watched[i], &previous[i], NULL);
        close_signals(signal_input, atomic_load(&signal_output));
    }
    pthread_mutex_unlock(&signal_lock);
}

/* --------------------------------------------------------------------------
 * §4 Deterministic Sandboxed Relative Filesystem (`fsCap`, 1-to-1 with `VirtualFs`)
 * -------------------------------------------------------------------------- */

static int ct_errno_to_fs_err(int e) {
    switch (e) {
        case ENOENT:  return CT_FS_NOT_FOUND;
        case EISDIR:  return CT_FS_IS_DIRECTORY;
        case ENOTDIR: return CT_FS_NOT_DIRECTORY;
        case EEXIST:  return CT_FS_ALREADY_EXISTS;
        case EACCES:
        case EPERM:
        case EROFS:   return CT_FS_PERMISSION_DENIED;
        case ELOOP:   return CT_FS_SYMLINK_LOOP;
        case EINVAL:
        case ENAMETOOLONG:
                      return CT_FS_INVALID_PATH;
        default:      return CT_FS_IO_ERROR;
    }
}

/* Matches Context.World.normalizeRelPath + Context.Tools.FsSandbox.validRelPath */
static int ct_normalize_and_validate_rel(
    const char *raw_p,
    size_t raw_len,
    char *norm_out,
    size_t norm_cap,
    int *out_is_dot)
{
    if (out_is_dot) *out_is_dot = 0;
    if (!raw_p || memchr(raw_p, '\0', raw_len) != NULL) {
        return CT_FS_INVALID_PATH;
    }
    size_t off = 0;
    while (raw_len - off >= 2 && raw_p[off] == '.' && raw_p[off + 1] == '/') {
        off += 2;
    }
    size_t nlen = raw_len - off;
    if (nlen + 1 > norm_cap) {
        return CT_FS_INVALID_PATH;
    }
    memcpy(norm_out, raw_p + off, nlen);
    norm_out[nlen] = '\0';

    if (nlen == 1 && norm_out[0] == '.') {
        if (out_is_dot) *out_is_dot = 1;
        return CT_FS_OK;
    }
    if (nlen == 0) {
        return CT_FS_INVALID_PATH;
    }
    /* Every '/' segment must be non-empty, != ".", and != ".." */
    size_t seg_start = 0;
    for (size_t i = 0; i <= nlen; ++i) {
        if (i == nlen || norm_out[i] == '/') {
            size_t slen = i - seg_start;
            if (slen == 0) return CT_FS_INVALID_PATH;
            if (slen == 1 && norm_out[seg_start] == '.') return CT_FS_INVALID_PATH;
            if (slen == 2 && norm_out[seg_start] == '.' && norm_out[seg_start + 1] == '.') {
                return CT_FS_INVALID_PATH;
            }
            seg_start = i + 1;
        }
    }
    return CT_FS_OK;
}

/* Mirrors `ensureParents create (parentPaths p) v`:
 * intermediate segments must be real directories (never symlinks or regular files). */
static int ct_ensure_parents(const char *norm, int create_dirs) {
    char tmp[4096];
    size_t n = strlen(norm);
    if (n + 1 > sizeof(tmp)) return CT_FS_INVALID_PATH;
    memcpy(tmp, norm, n + 1);

    for (size_t i = 0; i < n; ++i) {
        if (tmp[i] == '/') {
            tmp[i] = '\0';
            struct stat st;
            if (lstat(tmp, &st) == 0) {
                if (!S_ISDIR(st.st_mode)) {
                    return CT_FS_NOT_DIRECTORY;
                }
            } else if (errno == ENOENT) {
                if (!create_dirs) {
                    return CT_FS_NOT_DIRECTORY;
                }
                if (mkdir(tmp, 0755) != 0) {
                    return ct_errno_to_fs_err(errno);
                }
                (void)chmod(tmp, 0755);
            } else {
                return ct_errno_to_fs_err(errno);
            }
            tmp[i] = '/';
        }
    }
    return CT_FS_OK;
}

/* For `readVirtualFile` / `statVirtual`: all parent prefixes must exist as real `dirNode`,
 * otherwise `lookupEntry p (fsEntries v)` is `nothing` (`CT_FS_NOT_FOUND`). */
static int ct_parents_are_real_dirs(const char *norm) {
    char tmp[4096];
    size_t n = strlen(norm);
    if (n + 1 > sizeof(tmp)) return 0;
    memcpy(tmp, norm, n + 1);
    for (size_t i = 0; i < n; ++i) {
        if (tmp[i] == '/') {
            tmp[i] = '\0';
            struct stat st;
            if (lstat(tmp, &st) != 0 || !S_ISDIR(st.st_mode)) {
                return 0;
            }
            tmp[i] = '/';
        }
    }
    return 1;
}

static int ct_fs_read_file_fuel(int fuel, const char *raw_p, size_t raw_len, uint8_t **out_buf, size_t *out_len) {
    if (fuel <= 0) return CT_FS_SYMLINK_LOOP;
    char norm[4096];
    int is_dot = 0;
    int vrc = ct_normalize_and_validate_rel(raw_p, raw_len, norm, sizeof(norm), &is_dot);
    if (vrc != CT_FS_OK) return vrc;
    if (is_dot) return CT_FS_IS_DIRECTORY;
    if (!ct_parents_are_real_dirs(norm)) return CT_FS_NOT_FOUND;

    struct stat st;
    if (lstat(norm, &st) != 0) {
        return ct_errno_to_fs_err(errno);
    }
    if (S_ISDIR(st.st_mode)) {
        return CT_FS_IS_DIRECTORY;
    }
    if (S_ISLNK(st.st_mode)) {
        char link_dst[4096];
        ssize_t llen = readlink(norm, link_dst, sizeof(link_dst) - 1);
        if (llen < 0) return ct_errno_to_fs_err(errno);
        link_dst[llen] = '\0';
        return ct_fs_read_file_fuel(fuel - 1, link_dst, (size_t)llen, out_buf, out_len);
    }
    if (!S_ISREG(st.st_mode)) {
        return CT_FS_IO_ERROR;
    }

    int fd = open(norm, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) return ct_errno_to_fs_err(errno);

    size_t cap = (st.st_size > 0 && st.st_size < (1 << 26)) ? (size_t)st.st_size + 16 : 4096;
    size_t len = 0;
    uint8_t *buf = (uint8_t *)malloc(cap);
    if (!buf) {
        close(fd);
        return CT_FS_IO_ERROR;
    }
    for (;;) {
        if (len == cap) {
            cap *= 2;
            uint8_t *nb = (uint8_t *)realloc(buf, cap);
            if (!nb) { free(buf); close(fd); return CT_FS_IO_ERROR; }
            buf = nb;
        }
        ssize_t n = read(fd, buf + len, cap - len);
        if (n > 0) len += (size_t)n;
        else if (n == 0) break;
        else if (errno == EINTR) continue;
        else { int e = errno; free(buf); close(fd); return ct_errno_to_fs_err(e); }
    }
    close(fd);
    if (out_buf) *out_buf = buf; else free(buf);
    if (out_len) *out_len = len;
    return CT_FS_OK;
}

int ct_fs_read_file(const char *path, size_t path_len, uint8_t **out_buf, size_t *out_len) {
    if (out_buf) *out_buf = NULL;
    if (out_len) *out_len = 0;
    return ct_fs_read_file_fuel(8, path, path_len, out_buf, out_len);
}

static int ct_fs_write_file_fuel(int fuel, const char *raw_p, size_t raw_len, const uint8_t *buf, size_t len) {
    if (fuel <= 0) return CT_FS_SYMLINK_LOOP;
    char norm[4096];
    int is_dot = 0;
    int vrc = ct_normalize_and_validate_rel(raw_p, raw_len, norm, sizeof(norm), &is_dot);
    if (vrc != CT_FS_OK) return vrc;
    if (is_dot) return CT_FS_IS_DIRECTORY;

    /* If all parents currently exist as real dirs, inspect leaf first before mutating parents */
    if (ct_parents_are_real_dirs(norm)) {
        struct stat st;
        if (lstat(norm, &st) == 0) {
            if (S_ISDIR(st.st_mode)) return CT_FS_IS_DIRECTORY;
            if (S_ISLNK(st.st_mode)) {
                char link_dst[4096];
                ssize_t llen = readlink(norm, link_dst, sizeof(link_dst) - 1);
                if (llen < 0) return ct_errno_to_fs_err(errno);
                link_dst[llen] = '\0';
                return ct_fs_write_file_fuel(fuel - 1, link_dst, (size_t)llen, buf, len);
            }
        }
    }

    int prc = ct_ensure_parents(norm, 1);
    if (prc != CT_FS_OK) return prc;

    struct stat st;
    int existed = (lstat(norm, &st) == 0);
    mode_t target_mode = 0644;
    if (existed) {
        if (S_ISDIR(st.st_mode)) return CT_FS_IS_DIRECTORY;
        if (S_ISLNK(st.st_mode)) {
            char link_dst[4096];
            ssize_t llen = readlink(norm, link_dst, sizeof(link_dst) - 1);
            if (llen < 0) return ct_errno_to_fs_err(errno);
            link_dst[llen] = '\0';
            return ct_fs_write_file_fuel(fuel - 1, link_dst, (size_t)llen, buf, len);
        }
        target_mode = st.st_mode & 0777;
    }

    int fd = open(norm, O_WRONLY | O_CREAT | O_TRUNC | O_NOFOLLOW | O_CLOEXEC, 0644);
    if (fd < 0) return ct_errno_to_fs_err(errno);
    if (len > 0 && buf) {
        if (ct_write_fd_all(fd, buf, len) != 0) {
            int e = errno;
            close(fd);
            return ct_errno_to_fs_err(e);
        }
    }
    (void)fchmod(fd, target_mode);
    if (close(fd) != 0) return ct_errno_to_fs_err(errno);
    return CT_FS_OK;
}

int ct_fs_write_file(const char *path, size_t path_len, const uint8_t *buf, size_t len) {
    return ct_fs_write_file_fuel(8, path, path_len, buf, len);
}

int ct_fs_mkdir(const char *path, size_t path_len, uint32_t mode) {
    char norm[4096];
    int is_dot = 0;
    int vrc = ct_normalize_and_validate_rel(path, path_len, norm, sizeof(norm), &is_dot);
    if (vrc != CT_FS_OK) return vrc;
    if (is_dot) return CT_FS_OK;

    mode_t m = (mode_t)(mode & 0777);
    if (ct_parents_are_real_dirs(norm)) {
        struct stat st;
        if (lstat(norm, &st) == 0) {
            if (S_ISDIR(st.st_mode)) {
                (void)chmod(norm, m);
                return CT_FS_OK;
            }
            return CT_FS_ALREADY_EXISTS;
        }
    }

    int prc = ct_ensure_parents(norm, 1);
    if (prc != CT_FS_OK) return prc;

    struct stat st;
    if (lstat(norm, &st) == 0) {
        if (S_ISDIR(st.st_mode)) {
            (void)chmod(norm, m);
            return CT_FS_OK;
        }
        return CT_FS_ALREADY_EXISTS;
    }
    if (mkdir(norm, m) != 0) return ct_errno_to_fs_err(errno);
    (void)chmod(norm, m);
    return CT_FS_OK;
}

int ct_fs_symlink(const char *path, size_t path_len, const char *dest, size_t dest_len) {
    if (!dest || dest_len == 0 || memchr(dest, '\0', dest_len) != NULL || dest_len >= 4096) {
        return CT_FS_INVALID_PATH;
    }
    char norm[4096];
    int is_dot = 0;
    int vrc = ct_normalize_and_validate_rel(path, path_len, norm, sizeof(norm), &is_dot);
    if (vrc != CT_FS_OK) return vrc;
    if (is_dot) return CT_FS_INVALID_PATH;

    char dst_cstr[4096];
    memcpy(dst_cstr, dest, dest_len);
    dst_cstr[dest_len] = '\0';

    if (ct_parents_are_real_dirs(norm)) {
        struct stat st;
        if (lstat(norm, &st) == 0) {
            if (S_ISDIR(st.st_mode)) return CT_FS_IS_DIRECTORY;
            if (unlink(norm) != 0) return ct_errno_to_fs_err(errno);
            if (symlink(dst_cstr, norm) != 0) return ct_errno_to_fs_err(errno);
            return CT_FS_OK;
        }
    }

    int prc = ct_ensure_parents(norm, 1);
    if (prc != CT_FS_OK) return prc;

    struct stat st;
    if (lstat(norm, &st) == 0) {
        if (S_ISDIR(st.st_mode)) return CT_FS_IS_DIRECTORY;
        if (unlink(norm) != 0) return ct_errno_to_fs_err(errno);
    }
    if (symlink(dst_cstr, norm) != 0) return ct_errno_to_fs_err(errno);
    return CT_FS_OK;
}

int ct_fs_unlink(const char *path, size_t path_len) {
    char norm[4096];
    int is_dot = 0;
    int vrc = ct_normalize_and_validate_rel(path, path_len, norm, sizeof(norm), &is_dot);
    if (vrc != CT_FS_OK) return vrc;
    if (is_dot) return CT_FS_INVALID_PATH;

    int prc = ct_ensure_parents(norm, 0);
    if (prc != CT_FS_OK) return prc;

    struct stat st;
    if (lstat(norm, &st) != 0) {
        return ct_errno_to_fs_err(errno);
    }
    if (S_ISDIR(st.st_mode)) {
        if (rmdir(norm) == 0) return CT_FS_OK;
        if (errno == ENOTEMPTY || errno == EEXIST) return CT_FS_IS_DIRECTORY;
        return ct_errno_to_fs_err(errno);
    }
    if (unlink(norm) != 0) return ct_errno_to_fs_err(errno);
    return CT_FS_OK;
}

int ct_fs_stat(const char *path, size_t path_len, int *out_kind) {
    if (out_kind) *out_kind = CT_NODE_REGULAR;
    char norm[4096];
    int is_dot = 0;
    int vrc = ct_normalize_and_validate_rel(path, path_len, norm, sizeof(norm), &is_dot);
    if (vrc != CT_FS_OK) return vrc;
    if (is_dot) {
        if (out_kind) *out_kind = CT_NODE_DIR;
        return CT_FS_OK;
    }
    if (!ct_parents_are_real_dirs(norm)) return CT_FS_NOT_FOUND;

    struct stat st;
    if (lstat(norm, &st) != 0) {
        return ct_errno_to_fs_err(errno);
    }
    if (S_ISREG(st.st_mode)) {
        if (out_kind) *out_kind = CT_NODE_REGULAR;
        return CT_FS_OK;
    }
    if (S_ISDIR(st.st_mode)) {
        if (out_kind) *out_kind = CT_NODE_DIR;
        return CT_FS_OK;
    }
    if (S_ISLNK(st.st_mode)) {
        if (out_kind) *out_kind = CT_NODE_SYMLINK;
        return CT_FS_OK;
    }
    return CT_FS_IO_ERROR;
}

/* --------------------------------------------------------------------------
 * §5 Bounded Non-Blocking TCP & TLS Exchange (`netCap`)
 * -------------------------------------------------------------------------- */

static void set_err(char *err_buf, size_t err_cap, const char *msg) {
    if (!err_buf || err_cap == 0) return;
    snprintf(err_buf, err_cap, "%s", msg ? msg : "io error");
}

static void strip_brackets(const char *in, char *out, size_t out_cap) {
    if (!in || out_cap == 0) {
        if (out && out_cap > 0) out[0] = '\0';
        return;
    }
    size_t n = strlen(in);
    if (n >= 2 && in[0] == '[' && in[n - 1] == ']') {
        size_t inner = n - 2;
        if (inner >= out_cap) inner = out_cap - 1;
        memcpy(out, in + 1, inner);
        out[inner] = '\0';
    } else {
        snprintf(out, out_cap, "%s", in);
    }
}

static int ct_wait_fd(int fd, short events, int64_t deadline, const char *timeout_msg,
                      char *err_buf, size_t err_cap, int *out_err_code)
{
    for (;;) {
        int64_t rem = deadline - ct_raw_mono_ms();
        if (rem <= 0) {
            set_err(err_buf, err_cap, timeout_msg);
            if (out_err_code) *out_err_code = CT_NET_TIMED_OUT;
            return -1;
        }
        struct pollfd pfd = { .fd = fd, .events = events, .revents = 0 };
        int pr = poll(&pfd, 1, (int)(rem > 1000 ? 1000 : rem));
        if (pr < 0) {
            if (errno == EINTR) continue;
            set_err(err_buf, err_cap, strerror(errno));
            if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
            return -1;
        }
        if (pr > 0) return 0;
    }
}

static int ct_errno_to_net_err(int e) {
    if (e == ETIMEDOUT) return CT_NET_TIMED_OUT;
    if (e == ECONNREFUSED || e == ECONNRESET || e == ENETUNREACH || e == EHOSTUNREACH) {
        return CT_NET_CONN_REFUSED;
    }
    return CT_NET_IO_ERROR;
}

static int ct_connect_nonblocking(const char *raw_host, uint32_t port, int64_t deadline,
                                  char *err_buf, size_t err_cap, int *out_err_code)
{
    if (!raw_host || !*raw_host || port == 0 || port > 65535) {
        set_err(err_buf, err_cap, "invalid host or port");
        if (out_err_code) *out_err_code = CT_NET_INVALID_ENDPOINT;
        return -1;
    }
    char host[256];
    strip_brackets(raw_host, host, sizeof(host));
    if (!host[0]) {
        set_err(err_buf, err_cap, "invalid host");
        if (out_err_code) *out_err_code = CT_NET_INVALID_ENDPOINT;
        return -1;
    }

    struct sockaddr_in v4;
    memset(&v4, 0, sizeof(v4));
    int have_v4 = inet_pton(AF_INET, host, &v4.sin_addr) == 1;
    if (!have_v4 && !strcmp(host, "localhost")) {
        have_v4 = 1;
        v4.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    }
    if (have_v4) {
        v4.sin_family = AF_INET;
        v4.sin_port = htons((uint16_t)port);
        int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
        if (fd < 0) {
            int e = errno;
            set_err(err_buf, err_cap, strerror(e));
            if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
            return -1;
        }
        if (connect(fd, (struct sockaddr *)&v4, sizeof(v4)) != 0) {
            if (errno != EINPROGRESS) {
                int e = errno;
                close(fd);
                set_err(err_buf, err_cap, strerror(e));
                if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
                return -1;
            }
            if (ct_wait_fd(fd, POLLOUT, deadline, "connection timed out", err_buf, err_cap, out_err_code) != 0) {
                close(fd);
                return -1;
            }
            int so_err = 0;
            socklen_t slen = sizeof(so_err);
            if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &so_err, &slen) != 0 || so_err != 0) {
                int e = so_err ? so_err : ECONNREFUSED;
                close(fd);
                set_err(err_buf, err_cap, strerror(e));
                if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
                return -1;
            }
        }
        return fd;
    }

    struct sockaddr_in6 v6;
    memset(&v6, 0, sizeof(v6));
    if (inet_pton(AF_INET6, host, &v6.sin6_addr) == 1) {
        v6.sin6_family = AF_INET6;
        v6.sin6_port = htons((uint16_t)port);
        int fd = socket(AF_INET6, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
        if (fd < 0) {
            int e = errno;
            set_err(err_buf, err_cap, strerror(e));
            if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
            return -1;
        }
        if (connect(fd, (struct sockaddr *)&v6, sizeof(v6)) != 0) {
            if (errno != EINPROGRESS) {
                int e = errno;
                close(fd);
                set_err(err_buf, err_cap, strerror(e));
                if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
                return -1;
            }
            if (ct_wait_fd(fd, POLLOUT, deadline, "connection timed out", err_buf, err_cap, out_err_code) != 0) {
                close(fd);
                return -1;
            }
            int so_err = 0;
            socklen_t slen = sizeof(so_err);
            if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &so_err, &slen) != 0 || so_err != 0) {
                int e = so_err ? so_err : ECONNREFUSED;
                close(fd);
                set_err(err_buf, err_cap, strerror(e));
                if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
                return -1;
            }
        }
        return fd;
    }

    char port_str[16];
    snprintf(port_str, sizeof(port_str), "%u", (unsigned)port);
    struct addrinfo hints;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    struct addrinfo *res = NULL;
    int gai_rc = getaddrinfo(host, port_str, &hints, &res);
    if (gai_rc != 0 || !res) {
        set_err(err_buf, err_cap, gai_rc ? gai_strerror(gai_rc) : "no such host");
        if (out_err_code) *out_err_code = CT_NET_CONN_REFUSED;
        return -1;
    }

    int fd = -1;
    int last_err = ECONNREFUSED;
    for (struct addrinfo *ai = res; ai != NULL; ai = ai->ai_next) {
        int s = socket(ai->ai_family, ai->ai_socktype | SOCK_NONBLOCK | SOCK_CLOEXEC, ai->ai_protocol);
        if (s < 0) { last_err = errno; continue; }
        if (connect(s, ai->ai_addr, ai->ai_addrlen) == 0) {
            fd = s;
            break;
        }
        if (errno != EINPROGRESS) {
            last_err = errno;
            close(s);
            continue;
        }
        if (ct_wait_fd(s, POLLOUT, deadline, "connection timed out", err_buf, err_cap, out_err_code) != 0) {
            close(s);
            freeaddrinfo(res);
            return -1;
        }
        int so_err = 0;
        socklen_t slen = sizeof(so_err);
        if (getsockopt(s, SOL_SOCKET, SO_ERROR, &so_err, &slen) == 0 && so_err == 0) {
            fd = s;
            break;
        }
        last_err = so_err ? so_err : ECONNREFUSED;
        close(s);
    }
    freeaddrinfo(res);
    if (fd < 0) {
        set_err(err_buf, err_cap, strerror(last_err));
        if (out_err_code) *out_err_code = ct_errno_to_net_err(last_err);
        return -1;
    }
    return fd;
}

static int ct_send_all_fd(int fd, const uint8_t *req, size_t req_len, int64_t deadline,
                          char *err_buf, size_t err_cap, int *out_err_code)
{
    size_t sent = 0;
    while (sent < req_len) {
        if (ct_raw_mono_ms() >= deadline) {
            set_err(err_buf, err_cap, "request write timed out");
            if (out_err_code) *out_err_code = CT_NET_TIMED_OUT;
            return -1;
        }
        ssize_t n = send(fd, req + sent, req_len - sent, MSG_NOSIGNAL);
        if (n > 0) {
            sent += (size_t)n;
        } else if (n < 0 && errno == EINTR) {
            continue;
        } else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            if (ct_wait_fd(fd, POLLOUT, deadline, "request write timed out", err_buf, err_cap, out_err_code) != 0) {
                return -1;
            }
        } else {
            int e = errno ? errno : EPIPE;
            set_err(err_buf, err_cap, strerror(e));
            if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
            return -1;
        }
    }
    return 0;
}

static int ct_tcp_exchange_impl(
    const char *host,
    uint32_t port,
    const uint8_t *req,
    size_t req_len,
    int half_close,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    char *err_buf,
    size_t err_cap,
    int *out_err_code)
{
    if (out_buf) *out_buf = NULL;
    if (out_len) *out_len = 0;
    if (out_err_code) *out_err_code = CT_NET_OK;

    uint32_t eff_timeout = timeout_ms == 0 ? 30000 : timeout_ms;
    int64_t deadline = ct_raw_mono_ms() + (int64_t)eff_timeout;

    int fd = ct_connect_nonblocking(host, port, deadline, err_buf, err_cap, out_err_code);
    if (fd < 0) return -1;

    if (ct_send_all_fd(fd, req, req_len, deadline, err_buf, err_cap, out_err_code) != 0) {
        close(fd);
        return -1;
    }

    if (half_close) {
        (void)shutdown(fd, SHUT_WR);
    }

    size_t cap = 8192, len = 0;
    uint8_t *buf = (uint8_t *)malloc(cap);
    if (!buf) {
        close(fd);
        set_err(err_buf, err_cap, "out of memory");
        if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
        return -1;
    }

    for (;;) {
        if (ct_raw_mono_ms() >= deadline) {
            free(buf);
            close(fd);
            set_err(err_buf, err_cap, "response timed out");
            if (out_err_code) *out_err_code = CT_NET_TIMED_OUT;
            return -1;
        }
        if (len == cap) {
            if (cap > (1u << 28)) {
                free(buf);
                close(fd);
                set_err(err_buf, err_cap, "response exceeds maximum buffer size");
                if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
                return -1;
            }
            cap *= 2;
            uint8_t *nb = (uint8_t *)realloc(buf, cap);
            if (!nb) {
                free(buf);
                close(fd);
                set_err(err_buf, err_cap, "out of memory");
                if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
                return -1;
            }
            buf = nb;
        }
        ssize_t n = recv(fd, buf + len, cap - len, 0);
        if (n > 0) {
            len += (size_t)n;
        } else if (n == 0) {
            break;
        } else if (errno == EINTR) {
            continue;
        } else if (errno == EAGAIN || errno == EWOULDBLOCK) {
            if (ct_wait_fd(fd, POLLIN, deadline, "response timed out", err_buf, err_cap, out_err_code) != 0) {
                free(buf);
                close(fd);
                return -1;
            }
        } else {
            int e = errno;
            free(buf);
            close(fd);
            set_err(err_buf, err_cap, strerror(e));
            if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
            return -1;
        }
    }

    close(fd);
    if (out_buf) *out_buf = buf; else free(buf);
    if (out_len) *out_len = len;
    return 0;
}

int ct_tcp_exchange(
    const char *host,
    uint32_t port,
    const uint8_t *req,
    size_t req_len,
    int half_close,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    char *err_buf,
    size_t err_cap)
{
    int code = 0;
    return ct_tcp_exchange_impl(host, port, req, req_len, half_close, timeout_ms, out_buf, out_len, err_buf, err_cap, &code);
}

int ct_tcp_exchange_code(
    const char *host,
    size_t host_len,
    uint32_t port,
    const uint8_t *req,
    size_t req_len,
    int half_close,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    int *out_err_code)
{
    if (!host || host_len == 0 || host_len >= 256 || memchr(host, '\0', host_len) != NULL) {
        if (out_buf) *out_buf = NULL;
        if (out_len) *out_len = 0;
        if (out_err_code) *out_err_code = CT_NET_INVALID_ENDPOINT;
        return -1;
    }
    char host_cstr[256];
    memcpy(host_cstr, host, host_len);
    host_cstr[host_len] = '\0';
    char err_buf[256];
    err_buf[0] = '\0';
    return ct_tcp_exchange_impl(host_cstr, port, req, req_len, half_close, timeout_ms,
                                out_buf, out_len, err_buf, sizeof(err_buf), out_err_code);
}

static int ct_tls_exchange_impl(
    const char *host,
    uint32_t port,
    const char *sni_host,
    int insecure_skip_verify,
    const uint8_t *tunnel_req,
    size_t tunnel_req_len,
    const uint8_t *req,
    size_t req_len,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    char *err_buf,
    size_t err_cap,
    int *out_err_code)
{
    if (out_buf) *out_buf = NULL;
    if (out_len) *out_len = 0;
    if (out_err_code) *out_err_code = CT_NET_OK;

    if (!host || !*host || port == 0 || port > 65535) {
        set_err(err_buf, err_cap, "invalid host or port");
        if (out_err_code) *out_err_code = CT_NET_INVALID_ENDPOINT;
        return -1;
    }
#ifndef CT_HAVE_OPENSSL
    (void)sni_host; (void)insecure_skip_verify;
    (void)tunnel_req; (void)tunnel_req_len; (void)req; (void)req_len; (void)timeout_ms;
    set_err(err_buf, err_cap, "tls requires static Lean OpenSSL build");
    if (out_err_code) *out_err_code = CT_NET_TLS_ERROR;
    return -1;
#else
    uint32_t eff_timeout = timeout_ms == 0 ? 30000 : timeout_ms;
    int64_t deadline = ct_raw_mono_ms() + (int64_t)eff_timeout;

    int fd = ct_connect_nonblocking(host, port, deadline, err_buf, err_cap, out_err_code);
    if (fd < 0) return -1;

    if (tunnel_req && tunnel_req_len > 0) {
        if (ct_send_all_fd(fd, tunnel_req, tunnel_req_len, deadline, err_buf, err_cap, out_err_code) != 0) {
            close(fd);
            return -1;
        }
        char hdr[16384];
        size_t hlen = 0;
        int got_end = 0;
        while (hlen + 1 < sizeof(hdr)) {
            if (ct_raw_mono_ms() >= deadline) {
                close(fd);
                set_err(err_buf, err_cap, "proxy CONNECT timed out");
                if (out_err_code) *out_err_code = CT_NET_TIMED_OUT;
                return -1;
            }
            ssize_t n = recv(fd, hdr + hlen, 1, 0);
            if (n == 1) {
                hlen++;
                hdr[hlen] = '\0';
                if ((hlen >= 4 && !memcmp(hdr + hlen - 4, "\r\n\r\n", 4)) ||
                    (hlen >= 2 && !memcmp(hdr + hlen - 2, "\n\n", 2))) {
                    got_end = 1;
                    break;
                }
            } else if (n == 0) {
                break;
            } else if (errno == EINTR) {
                continue;
            } else if (errno == EAGAIN || errno == EWOULDBLOCK) {
                if (ct_wait_fd(fd, POLLIN, deadline, "proxy CONNECT timed out", err_buf, err_cap, out_err_code) != 0) {
                    close(fd);
                    return -1;
                }
            } else {
                int e = errno;
                close(fd);
                set_err(err_buf, err_cap, strerror(e));
                if (out_err_code) *out_err_code = ct_errno_to_net_err(e);
                return -1;
            }
        }
        if (!got_end || strncmp(hdr, "HTTP/1.", 7) != 0 ||
            !(strstr(hdr, " 200 ") == hdr + 8 || strstr(hdr, " 200\r") == hdr + 8 || strstr(hdr, " 200\n") == hdr + 8)) {
            close(fd);
            set_err(err_buf, err_cap, "proxy CONNECT rejected");
            if (out_err_code) *out_err_code = CT_NET_TLS_ERROR;
            return -1;
        }
    }

    SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
    if (!ctx) {
        close(fd);
        set_err(err_buf, err_cap, "SSL_CTX_new failed");
        if (out_err_code) *out_err_code = CT_NET_TLS_ERROR;
        return -1;
    }

    if (!insecure_skip_verify) {
        (void)SSL_CTX_set_default_verify_paths(ctx);
        const char *env_file = getenv("SSL_CERT_FILE");
        const char *env_dir  = getenv("SSL_CERT_DIR");
        if ((env_file && *env_file) || (env_dir && *env_dir)) {
            (void)SSL_CTX_load_verify_locations(ctx, (env_file && *env_file) ? env_file : NULL,
                                                     (env_dir && *env_dir) ? env_dir : NULL);
        }
        if (access("/etc/ssl/certs/ca-certificates.crt", R_OK) == 0) {
            (void)SSL_CTX_load_verify_locations(ctx, "/etc/ssl/certs/ca-certificates.crt", "/etc/ssl/certs");
        } else if (access("/etc/ssl/cert.pem", R_OK) == 0) {
            (void)SSL_CTX_load_verify_locations(ctx, "/etc/ssl/cert.pem", NULL);
        }
        SSL_CTX_set_verify(ctx, CT_SSL_VERIFY_PEER, NULL);
    } else {
        SSL_CTX_set_verify(ctx, CT_SSL_VERIFY_NONE, NULL);
    }

    SSL *ssl = SSL_new(ctx);
    if (!ssl) {
        SSL_CTX_free(ctx);
        close(fd);
        set_err(err_buf, err_cap, "SSL_new failed");
        if (out_err_code) *out_err_code = CT_NET_TLS_ERROR;
        return -1;
    }

    char clean_sni[256];
    strip_brackets((sni_host && *sni_host) ? sni_host : host, clean_sni, sizeof(clean_sni));
    struct in_addr tmp4;
    struct in6_addr tmp6;
    int is_ip = (inet_pton(AF_INET, clean_sni, &tmp4) == 1) || (inet_pton(AF_INET6, clean_sni, &tmp6) == 1);
    if (clean_sni[0] && !is_ip) {
        (void)SSL_ctrl(ssl, CT_SSL_CTRL_SET_TLSEXT_HOSTNAME, 0, (void *)clean_sni);
    }
    if (!insecure_skip_verify && clean_sni[0]) {
        if (is_ip) {
            X509_VERIFY_PARAM *pm = SSL_get0_param(ssl);
            if (pm) (void)X509_VERIFY_PARAM_set1_ip_asc(pm, clean_sni);
        } else {
            (void)SSL_set1_host(ssl, clean_sni);
        }
    }

    SSL_set_fd(ssl, fd);

    for (;;) {
        int rc = SSL_connect(ssl);
        if (rc == 1) break;
        int serr = SSL_get_error(ssl, rc);
        if (serr == CT_SSL_ERROR_WANT_READ) {
            if (ct_wait_fd(fd, POLLIN, deadline, "tls handshake timed out", err_buf, err_cap, out_err_code) != 0) {
                SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
            }
        } else if (serr == CT_SSL_ERROR_WANT_WRITE) {
            if (ct_wait_fd(fd, POLLOUT, deadline, "tls handshake timed out", err_buf, err_cap, out_err_code) != 0) {
                SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
            }
        } else {
            set_err(err_buf, err_cap, "tls handshake failed");
            if (out_err_code) *out_err_code = CT_NET_TLS_ERROR;
            SSL_free(ssl);
            SSL_CTX_free(ctx);
            close(fd);
            return -1;
        }
    }

    size_t sent = 0;
    while (sent < req_len) {
        if (ct_raw_mono_ms() >= deadline) {
            SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
            set_err(err_buf, err_cap, "tls write timed out");
            if (out_err_code) *out_err_code = CT_NET_TIMED_OUT;
            return -1;
        }
        int chunk = (req_len - sent) > 65536 ? 65536 : (int)(req_len - sent);
        int n = SSL_write(ssl, req + sent, chunk);
        if (n > 0) {
            sent += (size_t)n;
        } else {
            int serr = SSL_get_error(ssl, n);
            if (serr == CT_SSL_ERROR_WANT_READ) {
                if (ct_wait_fd(fd, POLLIN, deadline, "tls write timed out", err_buf, err_cap, out_err_code) != 0) {
                    SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
                }
            } else if (serr == CT_SSL_ERROR_WANT_WRITE) {
                if (ct_wait_fd(fd, POLLOUT, deadline, "tls write timed out", err_buf, err_cap, out_err_code) != 0) {
                    SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
                }
            } else {
                SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
                set_err(err_buf, err_cap, "tls write error");
                if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
                return -1;
            }
        }
    }

    size_t cap = 8192, len = 0;
    uint8_t *buf = (uint8_t *)malloc(cap);
    if (!buf) {
        SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
        set_err(err_buf, err_cap, "out of memory");
        if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
        return -1;
    }

    for (;;) {
        if (ct_raw_mono_ms() >= deadline) {
            free(buf); SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
            set_err(err_buf, err_cap, "tls response timed out");
            if (out_err_code) *out_err_code = CT_NET_TIMED_OUT;
            return -1;
        }
        if (len == cap) {
            if (cap > (1u << 28)) {
                free(buf); SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
                set_err(err_buf, err_cap, "response exceeds maximum buffer size");
                if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
                return -1;
            }
            cap *= 2;
            uint8_t *nb = (uint8_t *)realloc(buf, cap);
            if (!nb) {
                free(buf); SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
                set_err(err_buf, err_cap, "out of memory");
                if (out_err_code) *out_err_code = CT_NET_IO_ERROR;
                return -1;
            }
            buf = nb;
        }
        int max_r = (cap - len) > 65536 ? 65536 : (int)(cap - len);
        int n = SSL_read(ssl, buf + len, max_r);
        if (n > 0) {
            len += (size_t)n;
        } else {
            int serr = SSL_get_error(ssl, n);
            if (serr == CT_SSL_ERROR_ZERO_RETURN || (serr == CT_SSL_ERROR_SYSCALL && errno == 0)) {
                break;
            } else if (serr == CT_SSL_ERROR_WANT_READ) {
                if (ct_wait_fd(fd, POLLIN, deadline, "tls response timed out", err_buf, err_cap, out_err_code) != 0) {
                    free(buf); SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
                }
            } else if (serr == CT_SSL_ERROR_WANT_WRITE) {
                if (ct_wait_fd(fd, POLLOUT, deadline, "tls response timed out", err_buf, err_cap, out_err_code) != 0) {
                    free(buf); SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
                }
            } else if (len > 0) {
                break;
            } else {
                set_err(err_buf, err_cap, "tls read error");
                if (out_err_code) *out_err_code = CT_NET_TLS_ERROR;
                free(buf); SSL_free(ssl); SSL_CTX_free(ctx); close(fd); return -1;
            }
        }
    }

    (void)SSL_shutdown(ssl);
    SSL_free(ssl);
    SSL_CTX_free(ctx);
    close(fd);
    if (out_buf) *out_buf = buf; else free(buf);
    if (out_len) *out_len = len;
    return 0;
#endif
}

int ct_tls_exchange(
    const char *host,
    uint32_t port,
    const char *sni_host,
    int insecure_skip_verify,
    const uint8_t *tunnel_req,
    size_t tunnel_req_len,
    const uint8_t *req,
    size_t req_len,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    char *err_buf,
    size_t err_cap)
{
    int code = 0;
    return ct_tls_exchange_impl(host, port, sni_host, insecure_skip_verify,
                                tunnel_req, tunnel_req_len, req, req_len, timeout_ms,
                                out_buf, out_len, err_buf, err_cap, &code);
}

int ct_tls_exchange_code(
    const char *host,
    size_t host_len,
    uint32_t port,
    const char *sni_host,
    size_t sni_len,
    int insecure_skip_verify,
    const uint8_t *tunnel_req,
    size_t tunnel_req_len,
    const uint8_t *req,
    size_t req_len,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    int *out_err_code)
{
    if (!host || host_len == 0 || host_len >= 256 || memchr(host, '\0', host_len) != NULL ||
        sni_len >= 256 || (sni_host && sni_len > 0 && memchr(sni_host, '\0', sni_len) != NULL)) {
        if (out_buf) *out_buf = NULL;
        if (out_len) *out_len = 0;
        if (out_err_code) *out_err_code = CT_NET_INVALID_ENDPOINT;
        return -1;
    }
    char host_cstr[256];
    memcpy(host_cstr, host, host_len);
    host_cstr[host_len] = '\0';
    char sni_cstr[256];
    if (sni_host && sni_len > 0) {
        memcpy(sni_cstr, sni_host, sni_len);
        sni_cstr[sni_len] = '\0';
    } else {
        sni_cstr[0] = '\0';
    }
    char err_buf[256];
    err_buf[0] = '\0';
    return ct_tls_exchange_impl(host_cstr, port, sni_cstr, insecure_skip_verify,
                                tunnel_req, tunnel_req_len, req, req_len, timeout_ms,
                                out_buf, out_len, err_buf, sizeof(err_buf), out_err_code);
}

void ct_free_buf(void *p) {
    free(p);
}

void ct_exit_code(uint32_t code) {
    fflush(NULL);
    ct_restore_tty_termios();
    _exit((int)(code & 0xFFu));
}
