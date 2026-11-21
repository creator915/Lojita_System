/* Binary filesystem control relay. All strings and payloads use hex tokens;
 * '-' denotes empty bytes. Commands: E env, W path bytes, D path mode,
 * L path target, M path mode, U path, S, R ms exe argc args... stdin, Q.
 * Response: O stdout stderr status timedOut entryCount, followed by
 * F path kind(0=file,1=directory,2=link) mode contents for each snapshot entry.
 * Paths are relative, and no filesystem operation follows a symbolic link.
 */
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

struct buffer { unsigned char *data; size_t size, capacity; };
struct entry { char *path; unsigned kind, mode; struct buffer bytes; };
struct entries { struct entry *items; size_t size, capacity; };
struct permission { char *path; mode_t mode; };
struct permissions { struct permission *items; size_t size; };
static char **child_env;
static size_t env_count;
static pid_t active_child = -1;

static void die(const char *s) { perror(s); exit(125); }
static void *allocate(size_t size) {
    void *p = malloc(size ? size : 1);
    if (!p) die("malloc");
    return p;
}
static void append(struct buffer *b, const void *data, size_t size) {
    if (size > SIZE_MAX - b->size) die("buffer overflow");
    size_t total = b->size + size;
    if (total > b->capacity) {
        size_t cap = total <= SIZE_MAX / 2 ? total * 2 : total;
        void *p = realloc(b->data, cap);
        if (!p) die("realloc");
        b->data = p; b->capacity = cap;
    }
    if (size) memcpy(b->data + b->size, data, size);
    b->size = total;
}
static void release(struct buffer *b) {
    free(b->data); *b = (struct buffer){0};
}
static int64_t millis(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) die("clock_gettime");
    return (int64_t)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}
static void nonblock(int fd) {
    int flags = fcntl(fd, F_GETFL);
    if (flags < 0 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) < 0) die("fcntl");
}
static int nibble(unsigned char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}
static int decode(const char *s, struct buffer *b) {
    if (!s) return -1;
    if (!strcmp(s, "-")) return 0;
    size_t size = strlen(s);
    if (!size || size % 2) return -1;
    b->data = allocate(size / 2 + 1); b->capacity = size / 2 + 1;
    for (size_t i = 0; i < size; i += 2) {
        int a = nibble((unsigned char)s[i]), c = nibble((unsigned char)s[i+1]);
        if (a < 0 || c < 0) { release(b); return -1; }
        b->data[b->size++] = (unsigned char)(a * 16 + c);
    }
    b->data[b->size] = 0;
    return 0;
}
static char *decode_string(const char *s) {
    struct buffer b = {0};
    if (decode(s, &b)) return NULL;
    if (b.size && memchr(b.data, 0, b.size)) { release(&b); return NULL; }
    if (!b.data) { b.data = allocate(1); b.data[0] = 0; }
    return (char *)b.data;
}
static int number(const char *s, uint64_t *result) {
    if (!s || !*s) return -1;
    uint64_t n = 0;
    for (; *s; ++s) {
        if (*s < '0' || *s > '9' || n > (UINT64_MAX - (unsigned)(*s-'0')) / 10) return -1;
        n = 10 * n + (unsigned)(*s-'0');
    }
    *result = n; return 0;
}
static void hex(const void *ptr, size_t size) {
    const unsigned char *p = ptr;
    const char digits[] = "0123456789abcdef";
    if (!size) putchar('-');
    for (size_t i = 0; i < size; ++i) {
        putchar(digits[p[i] >> 4]); putchar(digits[p[i] & 15]);
    }
}
static void reply(const struct buffer *out, const struct buffer *err, int status,
                  int timed_out, const struct entries *es) {
    fputs("O ", stdout); hex(out->data, out->size); putchar(' ');
    hex(err->data, err->size);
    printf(" %d %d %zu\n", status, timed_out, es->size);
    for (size_t i = 0; i < es->size; ++i) {
        const struct entry *e = &es->items[i];
        fputs("F ", stdout); hex(e->path, strlen(e->path));
        printf(" %u %u ", e->kind, e->mode);
        hex(e->bytes.data, e->bytes.size); putchar('\n');
    }
    if (fflush(stdout)) exit(0);
}
static int valid_path(const char *p) {
    if (!p || !*p || *p == '/') return 0;
    const char *part = p;
    for (;;) {
        const char *end = strchr(part, '/');
        size_t len = end ? (size_t)(end-part) : strlen(part);
        if (!len || (len == 1 && part[0] == '.') ||
            (len == 2 && part[0] == '.' && part[1] == '.')) return 0;
        if (!end) return 1;
        part = end + 1;
    }
}
/* Explicit filesystem operations have authority over the owned tree even
 * when stored permission bits deny owner access. Temporarily grant only real
 * ancestor directories access, restoring in reverse order before replying.
 * runCmd is separate and sees exactly the configured POSIX modes. */
static int restore_permissions(struct permissions *ps) {
    int result = 0;
    while (ps->size) {
        struct permission *p = &ps->items[--ps->size];
        if (chmod(p->path, p->mode)) result = -1;
        free(p->path);
    }
    free(ps->items); ps->items = NULL;
    return result;
}
static int access_ancestors(const char *path, struct permissions *ps) {
    char *p = strdup(path);
    if (!p) die("strdup");
    int result = 0;
    for (char *s = p; *s; ++s) if (*s == '/') {
        *s = 0;
        struct stat st;
        if (lstat(p, &st)) {
            if (errno != ENOENT) result = -1;
            *s = '/'; break;
        }
        if (!S_ISDIR(st.st_mode)) { result = -1; *s = '/'; break; }
        mode_t mode = st.st_mode & 07777;
        if ((mode & 0700) != 0700) {
            char *saved = strdup(p);
            if (!saved) die("strdup");
            void *q = realloc(ps->items, (ps->size + 1) * sizeof *ps->items);
            if (!q) die("realloc");
            ps->items = q;
            if (chmod(p, mode | 0700)) { free(saved); result = -1; *s = '/'; break; }
            ps->items[ps->size++] = (struct permission){saved, mode};
        }
        *s = '/';
    }
    free(p); return result;
}
/* First inspect all ancestors, before creating any. A planted link causes an
 * immediate failure without materializing part of the requested path. */
static int ancestors(const char *path, int create) {
    char *p = strdup(path);
    if (!p) die("strdup");
    int missing = 0, result = 0;
    for (char *s = p; *s; ++s) if (*s == '/') {
        *s = 0;
        struct stat st;
        if (!missing && lstat(p, &st)) {
            if (errno != ENOENT || !create) { result = -1; *s = '/'; break; }
            missing = 1;
        } else if (!missing && !S_ISDIR(st.st_mode)) { result = -1; *s = '/'; break; }
        *s = '/';
    }
    if (!result && create) for (char *s = p; *s; ++s) if (*s == '/') {
        *s = 0;
        struct stat st;
        if (lstat(p, &st)) {
            if (errno != ENOENT || mkdir(p, 0755)) result = -1;
        } else if (!S_ISDIR(st.st_mode)) result = -1;
        *s = '/';
        if (result) break;
    }
    free(p); return result;
}
static int write_all(int fd, const unsigned char *data, size_t size) {
    size_t offset = 0;
    while (offset < size) {
        ssize_t n = write(fd, data + offset, size - offset);
        if (n > 0) offset += (size_t)n;
        else if (n < 0 && errno == EINTR) continue;
        else return -1;
    }
    return 0;
}
static int write_file(const char *path, const struct buffer *data) {
    if (!valid_path(path) || ancestors(path, 1)) return -1;
    struct stat st;
    int exists = !lstat(path, &st);
    if ((!exists && errno != ENOENT) || (exists && !S_ISREG(st.st_mode))) return -1;
    mode_t mode = exists ? st.st_mode & 0777 : 0644;
    /* Explicit writes are model operations, independent of read-only mode bits.
     * Restore the original permission bits even when an OS write fails. */
    if (exists && chmod(path, mode | 0200)) return -1;
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC | O_NOFOLLOW, 0644);
    int result = fd < 0 ? -1 : write_all(fd, data->data, data->size);
    if (fd >= 0 && close(fd)) result = -1;
    if (chmod(path, mode)) result = -1;
    return result;
}
static int make_directory(const char *path, unsigned mode) {
    if (!valid_path(path) || ancestors(path, 1)) return -1;
    struct stat st;
    if (lstat(path, &st)) {
        if (errno != ENOENT || mkdir(path, mode & 0777)) return -1;
    } else if (!S_ISDIR(st.st_mode)) return -1;
    return chmod(path, mode & 0777);
}
static int make_link(const char *path, const char *target) {
    if (!valid_path(path) || !target || !*target || ancestors(path, 1)) return -1;
    struct stat st;
    if (!lstat(path, &st)) {
        if (S_ISDIR(st.st_mode) || unlink(path)) return -1;
    } else if (errno != ENOENT) return -1;
    return symlink(target, path);
}
static int change_mode(const char *path, unsigned mode) {
    if (!valid_path(path) || ancestors(path, 0)) return -1;
    struct stat st;
    if (lstat(path, &st) || (!S_ISREG(st.st_mode) && !S_ISDIR(st.st_mode))) return -1;
    return chmod(path, mode & 0777);
}
static int remove_entry(const char *path) {
    if (!valid_path(path) || ancestors(path, 0)) return -1;
    struct stat st;
    if (lstat(path, &st)) return -1;
    return S_ISDIR(st.st_mode) ? rmdir(path) : unlink(path);
}
static int read_file(const char *path, struct buffer *b) {
    struct stat original;
    if (lstat(path, &original) || !S_ISREG(original.st_mode)) return -1;
    mode_t mode = original.st_mode & 07777;
    int changed = !(mode & 0400);
    if (changed && chmod(path, mode | 0400)) return -1;
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    struct stat st;
    int result = fd < 0 || fstat(fd, &st) || !S_ISREG(st.st_mode) ? -1 : 0;
    while (!result) {
        unsigned char data[8192];
        ssize_t n = read(fd, data, sizeof data);
        if (n > 0) append(b, data, (size_t)n);
        else if (!n) break;
        else if (errno != EINTR) result = -1;
    }
    if (fd >= 0) close(fd);
    if (changed && chmod(path, mode)) result = -1;
    return result;
}
static int read_link(const char *path, struct buffer *b) {
    size_t cap = 256;
    for (;;) {
        unsigned char *p = allocate(cap);
        ssize_t n = readlink(path, (char *)p, cap);
        if (n < 0) { free(p); return -1; }
        if ((size_t)n < cap) { b->data = p; b->size = (size_t)n; b->capacity = cap; return 0; }
        free(p);
        if (cap > SIZE_MAX / 2) return -1;
        cap *= 2;
    }
}
static int snapshot(const char *base, struct entries *es) {
    const char *path_base = *base ? base : ".";
    struct stat original;
    if (lstat(path_base, &original) || !S_ISDIR(original.st_mode)) return -1;
    mode_t mode = original.st_mode & 07777;
    int changed = (mode & 0500) != 0500;
    if (changed && chmod(path_base, mode | 0500)) return -1;
    DIR *dir = opendir(path_base);
    if (!dir) { if (changed) (void)chmod(path_base, mode); return -1; }
    int result = 0;
    for (;;) {
        errno = 0;
        struct dirent *de = readdir(dir);
        if (!de) { if (errno) result = -1; break; }
        if (!strcmp(de->d_name, ".") || !strcmp(de->d_name, "..")) continue;
        size_t a = strlen(base), b = strlen(de->d_name);
        char *path = allocate(a + b + 2);
        if (a) { memcpy(path, base, a); path[a] = '/'; }
        memcpy(path + a + (a != 0), de->d_name, b + 1);
        struct stat st;
        if (lstat(path, &st)) { free(path); result = -1; break; }
        struct entry e = { .path = path, .mode = (unsigned)(st.st_mode & 0777) };
        if (S_ISREG(st.st_mode)) { e.kind = 0; result = read_file(path, &e.bytes); }
        else if (S_ISDIR(st.st_mode)) e.kind = 1;
        else if (S_ISLNK(st.st_mode)) { e.kind = 2; e.mode = 0777; result = read_link(path, &e.bytes); }
        else result = -1;
        if (result) { free(path); release(&e.bytes); break; }
        if (es->size == es->capacity) {
            size_t cap = es->capacity ? es->capacity * 2 : 32;
            if (cap > SIZE_MAX / sizeof e) die("snapshot overflow");
            void *p = realloc(es->items, cap * sizeof e);
            if (!p) die("realloc");
            es->items = p; es->capacity = cap;
        }
        es->items[es->size++] = e;
        if (e.kind == 1 && snapshot(path, es)) { result = -1; break; }
    }
    closedir(dir);
    if (changed && chmod(path_base, mode)) result = -1;
    return result;
}
static int entry_compare(const void *a, const void *b) {
    return strcmp(((const struct entry *)a)->path, ((const struct entry *)b)->path);
}
static void free_entries(struct entries *es) {
    for (size_t i = 0; i < es->size; ++i) {
        free(es->items[i].path); release(&es->items[i].bytes);
    }
    free(es->items); *es = (struct entries){0};
}
static int valid_env(const char *s) {
    if (!s || !((*s >= 'A' && *s <= 'Z') || (*s >= 'a' && *s <= 'z') || *s == '_')) return 0;
    const char *eq = strchr(s, '=');
    if (!eq) return 0;
    for (const char *p = s; p < eq; ++p) if (!((*p >= 'A' && *p <= 'Z') ||
        (*p >= 'a' && *p <= 'z') || (*p >= '0' && *p <= '9') || *p == '_')) return 0;
    size_t len = (size_t)(eq - s);
    for (size_t i = 0; i < env_count; ++i)
        if (!strncmp(child_env[i], s, len) && child_env[i][len] == '=') return 0;
    return 1;
}
/* As a subreaper we also own descendants that detach from the original group.
 * Linux exposes adopted direct children here; kill them before returning from
 * the call so neither inherited pipe descriptors nor background jobs survive. */
static void kill_adopted(void) {
    char path[96];
    snprintf(path, sizeof path, "/proc/self/task/%ld/children", (long)getpid());
    FILE *f = fopen(path, "r");
    if (!f) return;
    long pid;
    while (fscanf(f, "%ld", &pid) == 1) if (pid > 0) kill((pid_t)pid, SIGKILL);
    fclose(f);
}
static void emergency_cleanup(void) {
    if (active_child <= 0) return;
    kill(-active_child, SIGKILL); kill(active_child, SIGKILL);
    for (;;) {
        kill_adopted();
        pid_t p = waitpid(-1, NULL, 0);
        if (p < 0 && errno == EINTR) continue;
        if (p < 0) break;
    }
    active_child = -1;
}
static void drain(int *fd, struct buffer *b) {
    if (*fd < 0) return;
    for (int batch = 0; batch < 16; ++batch) {
        unsigned char data[8192];
        ssize_t n = read(*fd, data, sizeof data);
        if (n > 0) append(b, data, (size_t)n);
        else if (!n) { close(*fd); *fd = -1; break; }
        else if (errno == EINTR) continue;
        else if (errno == EAGAIN || errno == EWOULDBLOCK) break;
        else die("read child pipe");
    }
}
static int run_command(char **args, const struct buffer *input, uint64_t timeout,
                       struct buffer *out, struct buffer *err, int *timed_out) {
    int in[2], output[2], error[2], ready[2];
    if (pipe2(in, O_CLOEXEC) || pipe2(output, O_CLOEXEC) || pipe2(error, O_CLOEXEC) || pipe2(ready, O_CLOEXEC)) die("pipe2");
    pid_t parent = getpid();
    active_child = fork();
    if (active_child < 0) die("fork");
    if (!active_child) {
        close(ready[0]);
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) || getppid() != parent || setsid() < 0) _exit(127);
        if (dup2(in[0], 0) < 0 || dup2(output[1], 1) < 0 || dup2(error[1], 2) < 0) _exit(127);
        close(in[0]); close(in[1]); close(output[0]); close(output[1]); close(error[0]); close(error[1]);
        signal(SIGPIPE, SIG_DFL);
        char marker = 'R';
        if (write(ready[1], &marker, 1) != 1) _exit(127);
        close(ready[1]);
        environ = child_env;
        execvpe(args[0], args, child_env);
        _exit(127);
    }
    close(in[0]); close(output[1]); close(error[1]); close(ready[1]);
    char marker;
    while (read(ready[0], &marker, 1) < 0 && errno == EINTR) {}
    close(ready[0]);
    int writer = in[1], reader = output[0], errors = error[0];
    nonblock(writer); nonblock(reader); nonblock(errors);
    size_t sent = 0;
    int exited = 0, all_reaped = 0, status = 127, killed = 0;
    int64_t start = millis();
    while (!all_reaped || reader >= 0 || errors >= 0) {
        int64_t now = millis();
        if (!exited && timeout && (uint64_t)(now - start) >= timeout) {
            *timed_out = 1; killed = 1;
            kill(-active_child, SIGKILL); kill(active_child, SIGKILL);
        }
        if (writer >= 0 && (sent == input->size || exited || killed)) { close(writer); writer = -1; }
        struct pollfd fds[4] = {{writer, POLLOUT, 0}, {reader, POLLIN, 0},
                              {errors, POLLIN, 0}, {STDIN_FILENO, 0, 0}};
        int wait = 10;
        if (!exited && timeout && (uint64_t)(now - start) < timeout) {
            uint64_t remain = timeout - (uint64_t)(now - start);
            if (remain < (uint64_t)wait) wait = (int)remain;
        }
        if (poll(fds, 4, wait) < 0 && errno != EINTR) die("poll");
        if (fds[3].revents & (POLLHUP | POLLERR)) {
            killed = 1; kill(-active_child, SIGKILL); kill(active_child, SIGKILL);
        }
        if (writer >= 0 && fds[0].revents) {
            size_t size = input->size - sent;
            if (size > 65536) size = 65536;
            ssize_t n = write(writer, input->data + sent, size);
            if (n > 0) sent += (size_t)n;
            else if (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) {
                close(writer); writer = -1;
            }
        }
        if (fds[1].revents) drain(&reader, out);
        if (fds[2].revents) drain(&errors, err);
        if (!exited) {
            int child_status;
            pid_t p = waitpid(active_child, &child_status, WNOHANG);
            if (p == active_child) {
                exited = 1;
                status = WIFEXITED(child_status) ? WEXITSTATUS(child_status) : 128 + WTERMSIG(child_status);
                kill(-active_child, SIGKILL);
            } else if (p < 0 && errno != EINTR) die("waitpid");
        }
        if (exited) {
            kill_adopted();
            for (;;) {
                pid_t p = waitpid(-1, NULL, WNOHANG);
                if (p > 0) continue;
                if (p < 0 && errno == EINTR) continue;
                if (p < 0 && errno == ECHILD) all_reaped = 1;
                break;
            }
        }
    }
    if (writer >= 0) close(writer);
    active_child = -1;
    return *timed_out ? 124 : status;
}
static char **tokens(char *line, size_t *count) {
    char **parts = NULL, *save = NULL;
    *count = 0;
    for (char *p = strtok_r(line, " \t\r\n", &save); p; p = strtok_r(NULL, " \t\r\n", &save)) {
        void *q = realloc(parts, (*count + 1) * sizeof *parts);
        if (!q) die("realloc");
        parts = q; parts[(*count)++] = p;
    }
    return parts;
}
int main(void) {
    umask(0);
    signal(SIGPIPE, SIG_IGN);
    if (prctl(PR_SET_CHILD_SUBREAPER, 1)) die("subreaper");
    if (atexit(emergency_cleanup)) die("atexit");
    child_env = calloc(1, sizeof *child_env);
    if (!child_env) die("calloc");
    setvbuf(stdin, NULL, _IONBF, 0);
    puts("READY"); fflush(stdout);
    char *line = NULL; size_t capacity = 0;
    for (;;) {
        ssize_t line_size = getline(&line, &capacity, stdin);
        if (line_size < 0) break;
        int bad = memchr(line, 0, (size_t)line_size) != NULL, quitting = 0;
        size_t count = 0;
        char **t = tokens(line, &count);
        struct buffer out = {0}, err = {0};
        struct entries es = {0};
        int status = -1, timed_out = 0;
        if (!count || strlen(t[0]) != 1) bad = 1;
        if (!bad && !strcmp(t[0], "Q") && count == 1) quitting = 1;
        else if (!bad && !strcmp(t[0], "S") && count == 1) {
            bad = snapshot("", &es);
            if (!bad && es.size > 1) qsort(es.items, es.size, sizeof *es.items, entry_compare);
        } else if (!bad && !strcmp(t[0], "E") && count == 2) {
            char *value = decode_string(t[1]);
            if (!valid_env(value)) { free(value); bad = 1; }
            else {
                void *p = realloc(child_env, (env_count + 2) * sizeof *child_env);
                if (!p) die("realloc");
                child_env = p; child_env[env_count++] = value; child_env[env_count] = NULL;
            }
        } else if (!bad && !strcmp(t[0], "R") && count >= 5) {
            uint64_t timeout, argc;
            bad = number(t[1], &timeout) || number(t[3], &argc) || argc > count || argc != count - 5;
            char **args = NULL;
            struct buffer input = {0};
            if (!bad) {
                args = calloc((size_t)argc + 2, sizeof *args);
                if (!args) die("calloc");
                args[0] = decode_string(t[2]);
                bad = !args[0] || !*args[0];
                for (size_t i = 0; i < argc; ++i) {
                    args[i+1] = decode_string(t[i+4]);
                    if (!args[i+1]) bad = 1;
                }
                if (decode(t[count-1], &input)) bad = 1;
                if (!bad) status = run_command(args, &input, timeout, &out, &err, &timed_out);
            }
            if (args) { for (size_t i = 0; i <= argc; ++i) free(args[i]); free(args); }
            release(&input);
        } else if (!bad && count >= 2 && strchr("WDLMU", t[0][0])) {
            char *path = decode_string(t[1]);
            char op = t[0][0];
            struct permissions permissions = {0};
            if (!valid_path(path) || access_ancestors(path, &permissions)) bad = 1;
            else if (op == 'U' && count == 2) bad = remove_entry(path);
            else if (count == 3) {
                uint64_t mode;
                if (op == 'D' || op == 'M') {
                    bad = number(t[2], &mode);
                    if (!bad) bad = op == 'D' ? make_directory(path, (unsigned)(mode % 512)) : change_mode(path, (unsigned)(mode % 512));
                } else if (op == 'L') {
                    char *target = decode_string(t[2]);
                    bad = make_link(path, target); free(target);
                } else if (op == 'W') {
                    struct buffer data = {0};
                    bad = decode(t[2], &data);
                    if (!bad) bad = write_file(path, &data);
                    release(&data);
                } else bad = 1;
            } else bad = 1;
            if (restore_permissions(&permissions)) bad = 1;
            free(path);
        } else if (!quitting) bad = 1;
        if (bad) {
            static const char message[] = "filesystem operation rejected";
            release(&out); release(&err); free_entries(&es);
            append(&err, message, sizeof message - 1); status = 1; timed_out = 0;
        }
        reply(&out, &err, status, timed_out, &es);
        free(t); release(&out); release(&err); free_entries(&es);
        if (quitting) break;
    }
    free(line);
    for (size_t i = 0; i < env_count; ++i) free(child_env[i]);
    free(child_env);
    return 0;
}
