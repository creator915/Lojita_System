/* Raw POSIX transport. No terminal language, key tables or screen model here.
 * Protocol: W/T hex, C, S ms, R rows cols, K signal, D, Q.
 * Replies: O <tty-hex|-> <stdout-hex|-> <stderr-hex|-> <exit|-1>.
 * D waits for 25 ms of quiet, bounded by 250 ms; S pumps for the full duration.
 * All byte values, including NUL and 0xff, are hex framed on the control pipe.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

struct buffer { unsigned char *data; size_t size, capacity; } output[3];
static int channels[3] = {-1, -1, -1}, input_fd = -1, exit_code = -1;
static int slave_keeper = -1;
static pid_t child = -1;

static void die(const char *what) { perror(what); exit(125); }
static int64_t millis(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) die("clock_gettime");
    return (int64_t)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}
static void nonblock(int fd) {
    int f = fcntl(fd, F_GETFL);
    if (f < 0 || fcntl(fd, F_SETFL, f | O_NONBLOCK) < 0) die("nonblock");
}
static void append(struct buffer *b, const void *p, size_t n) {
    if (n > SIZE_MAX - b->size) die("output overflow");
    if (b->size + n > b->capacity) {
        size_t cap = b->size + n + 4096;
        void *q = realloc(b->data, cap);
        if (!q) die("realloc");
        b->data = q; b->capacity = cap;
    }
    memcpy(b->data + b->size, p, n); b->size += n;
}
static void reap(void) {
    if (child <= 0 || exit_code >= 0) return;
    int s;
    pid_t p = waitpid(child, &s, WNOHANG);
    if (p == child) {
        exit_code = WIFEXITED(s) ? WEXITSTATUS(s) : 128 + WTERMSIG(s);
        if (slave_keeper >= 0) { close(slave_keeper); slave_keeper = -1; }
    }
}
static int collect(int timeout) {
    struct pollfd p[3];
    for (int i = 0; i < 3; ++i) p[i] = (struct pollfd){channels[i], POLLIN, 0};
    int rc = poll(p, 3, timeout);
    if (rc < 0 && errno != EINTR) die("poll");
    int got = 0;
    for (int i = 0; i < 3; ++i) if (p[i].revents) {
        /* Bound a single pass so a continuously writing child cannot starve
         * deadlines, the other streams, or protocol commands. */
        for (int batch = 0; batch < 64; ++batch) {
            unsigned char bytes[4096];
            ssize_t n = read(channels[i], bytes, sizeof bytes);
            if (n > 0) { append(&output[i], bytes, (size_t)n); got = 1; }
            else if (n == 0 || (n < 0 && errno == EIO)) {
                close(channels[i]); channels[i] = -1; break;
            } else if (errno == EINTR) continue;
            else if (errno == EAGAIN || errno == EWOULDBLOCK) break;
            else die("read output");
        }
    }
    reap(); return got;
}
static void pump(long duration, int quiet) {
    int64_t end = millis() + duration, last = millis();
    do {
        int64_t now = millis();
        int64_t remaining = end - now;
        if (remaining <= 0) break;
        int wait = (int)(remaining < 10 ? remaining : 10);
        if (collect(wait)) last = millis();
        if (quiet && millis() - last >= 25) break;
    } while (millis() < end);
    collect(0);
}
static void stop_child(void) {
    if (child <= 0) return;
    /* The group may still contain descendants after the leader exits. */
    kill(-child, SIGTERM);
    pump(100, 0);
    kill(-child, SIGKILL);
    if (exit_code < 0) {
        int s; pid_t p;
        do { p = waitpid(child, &s, 0); } while (p < 0 && errno == EINTR);
        if (p == child) exit_code = WIFEXITED(s) ? WEXITSTATUS(s) : 128 + WTERMSIG(s);
    }
    while (waitpid(-1, NULL, WNOHANG) > 0) {}
    if (slave_keeper >= 0) { close(slave_keeper); slave_keeper = -1; }
    collect(0); child = -1;
}
static void hexout(struct buffer *b) {
    static const char digits[] = "0123456789abcdef";
    if (!b->size) putchar('-');
    for (size_t i = 0; i < b->size; ++i) {
        putchar(digits[b->data[i] >> 4]); putchar(digits[b->data[i] & 15]);
    }
    b->size = 0;
}
static void reply(void) {
    collect(0); fputs("O ", stdout);
    for (int i = 0; i < 3; ++i) { hexout(&output[i]); putchar(' '); }
    printf("%d\n", exit_code); fflush(stdout);
}
static int nibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}
static int write_hex(int fd, const char *s) {
    size_t n = strlen(s);
    if (n && s[n-1] == '\n') --n;
    if (n == 1 && *s == '-') return 0;
    if (n % 2 || fd < 0) return -1;
    unsigned char *buf = malloc(n / 2 + 1);
    if (!buf) die("malloc");
    for (size_t i = 0; i < n; i += 2) {
        int a = nibble(s[i]), b = nibble(s[i+1]);
        if (a < 0 || b < 0) { free(buf); return -1; }
        buf[i/2] = (unsigned char)((a << 4) | b);
    }
    size_t sent = 0; int64_t limit = millis() + 30000;
    while (sent < n / 2) {
        ssize_t k = write(fd, buf + sent, n/2 - sent);
        if (k > 0) sent += (size_t)k;
        else if (k < 0 && errno == EINTR) continue;
        else if (k < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
            collect(1);
            if (millis() >= limit) { free(buf); return -1; }
        } else { free(buf); return -1; }
    }
    free(buf); return 0;
}
static long number(const char *s, long max) {
    char *end; errno = 0; long n = strtol(s, &end, 10);
    if (errno || end == s || (*end && *end != '\n') || n < 0 || n > max) return -1;
    return n;
}
int main(int argc, char **argv) {
    /* relay topology rows cols env-count [NAME=VALUE ...] command [args ...] */
    if (argc < 6) return 125;
    int tty_mode = !strcmp(argv[1], "tty");
    int pipe_tty_mode = !strcmp(argv[1], "pipe");
    int stdio_only_mode = !strcmp(argv[1], "stdio");
    if (!tty_mode && !pipe_tty_mode && !stdio_only_mode) return 125;
    int pipe_mode = pipe_tty_mode || stdio_only_mode;
    int has_pty = tty_mode || pipe_tty_mode;
    long rows = number(argv[2], 65535), cols = number(argv[3], 65535);
    int min_dimension = has_pty ? 1 : 0;
    long envc = number(argv[4], argc);
    if (rows < min_dimension || cols < min_dimension || envc < 0 || argc <= 5 + envc) return 125;
    char **child_env = calloc((size_t)envc + 1, sizeof(char *));
    if (!child_env) die("calloc");
    for (long i = 0; i < envc; ++i) child_env[i] = argv[5+i];
    signal(SIGPIPE, SIG_IGN);
    if (prctl(PR_SET_CHILD_SUBREAPER, 1)) die("subreaper");
    int master = -1, slave = -1;
    struct winsize size = {.ws_row = (unsigned short)rows, .ws_col = (unsigned short)cols};
    if (has_pty) {
        master = posix_openpt(O_RDWR | O_NOCTTY | O_CLOEXEC);
        if (master < 0 || grantpt(master) || unlockpt(master)) die("openpt");
        char *slave_name = ptsname(master);
        if (!slave_name) die("ptsname");
        slave = open(slave_name, O_RDWR | O_NOCTTY | O_CLOEXEC);
        if (slave < 0) die("open slave");
        struct termios attr;
        if (tcgetattr(slave, &attr)) die("tcgetattr");
        cfmakeraw(&attr);
        if (tcsetattr(slave, TCSANOW, &attr)) die("tcsetattr");
        if (ioctl(slave, TIOCSWINSZ, &size)) die("initial winsize");
    }
    int in[2], out[2], err[2], ready[2];
    if (pipe2(ready, O_CLOEXEC)) die("ready pipe");
    if (pipe_mode && (pipe2(in, O_CLOEXEC) || pipe2(out, O_CLOEXEC) || pipe2(err, O_CLOEXEC))) die("stdio pipes");
    child = fork();
    if (child < 0) die("fork");
    if (!child) {
        close(ready[0]);
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) || setsid() < 0) goto child_fail;
        if (has_pty && (ioctl(slave, TIOCSCTTY, 0) || ioctl(slave, TIOCSWINSZ, &size))) goto child_fail;
        if (dup2(pipe_mode ? in[0] : slave, 0) < 0 || dup2(pipe_mode ? out[1] : slave, 1) < 0 ||
            dup2(pipe_mode ? err[1] : slave, 2) < 0) goto child_fail;
        if (has_pty) { close(master); close(slave); }
        if (pipe_mode) { close(in[0]); close(in[1]); close(out[0]); close(out[1]); close(err[0]); close(err[1]); }
        signal(SIGPIPE, SIG_DFL);
        /* execvpe uses PATH from the caller environment, so replace environ too.
         * This is env -i even when a Docker image declares its own ENV values. */
        environ = child_env;
        execvpe(argv[5+envc], argv + 5 + envc, child_env);
child_fail: {
            int e = errno; (void)!write(ready[1], &e, sizeof e); _exit(127);
        }
    }
    atexit(stop_child);
    /* With piped stdio and a controlling PTY, the child has no open slave between
     * exec and opening /dev/tty. Keep one in the relay to prevent master EIO
     * and hangup during that interval. It is released when the child exits. */
    if (pipe_tty_mode) slave_keeper = slave;
    else if (tty_mode) close(slave);
    close(ready[1]);
    channels[0] = master;
    if (pipe_mode) {
        close(in[0]); close(out[1]); close(err[1]);
        input_fd = in[1]; channels[1] = out[0]; channels[2] = err[0];
    } else input_fd = dup(master);
    nonblock(input_fd);
    for (int i = 0; i < 3; ++i) if (channels[i] >= 0) nonblock(channels[i]);
    int e; ssize_t n;
    do { n = read(ready[0], &e, sizeof e); } while (n < 0 && errno == EINTR);
    close(ready[0]);
    if (n != 0) { errno = n > 0 ? e : errno; die("child setup/exec"); }
    setvbuf(stdin, NULL, _IONBF, 0);
    puts("READY"); fflush(stdout);
    char *line = NULL; size_t cap = 0;
    for (;;) {
        struct pollfd p[4] = {{0, POLLIN, 0}, {channels[0], POLLIN, 0},
            {channels[1], POLLIN, 0}, {channels[2], POLLIN, 0}};
        if (poll(p, 4, -1) < 0) { if (errno == EINTR) continue; die("control poll"); }
        collect(0);
        if (!p[0].revents) continue;
        if (getline(&line, &cap, stdin) < 0) break;
        int bad = 0, quitting = 0;
        if (line[0] == 'W' && line[1] == ' ') bad = write_hex(input_fd, line+2);
        else if (line[0] == 'T' && line[1] == ' ') bad = has_pty ? write_hex(channels[0], line+2) : -1;
        else if (!strcmp(line, "C\n")) {
            /* A PTY has no independent write-half EOF. Do not invent an EOF key. */
            if (!pipe_mode) bad = -1;
            else if (input_fd >= 0) { close(input_fd); input_fd = -1; }
        } else if (line[0] == 'S' && line[1] == ' ') {
            long ms = number(line+2, 86400000);
            if (ms < 0) bad = -1; else pump(ms, 0);
        } else if (line[0] == 'R' && line[1] == ' ') {
            unsigned int r, c; char extra;
            if (!has_pty || sscanf(line+2, "%u %u %c", &r, &c, &extra) != 2 ||
                !r || !c || r > 65535 || c > 65535) bad = -1;
            else { size.ws_row = (unsigned short)r; size.ws_col = (unsigned short)c;
                bad = ioctl(channels[0], TIOCSWINSZ, &size); }
        } else if (line[0] == 'K' && line[1] == ' ') {
            long sig = number(line+2, 64);
            if (sig <= 0) bad = -1;
            else if (kill(-child, (int)sig) && errno != ESRCH) bad = -1;
        } else if (!strcmp(line, "D\n")) pump(250, 1);
        else if (!strcmp(line, "Q\n")) { stop_child(); quitting = 1; }
        else bad = -1;
        if (bad) { puts("ERROR transport command failed"); fflush(stdout); break; }
        reply(); if (quitting) break;
    }
    free(line); stop_child();
    for (int i = 0; i < 3; ++i) free(output[i].data);
    free(child_env);
    return 0;
}
