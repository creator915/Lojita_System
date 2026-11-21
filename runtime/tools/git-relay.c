/* Git fixture relay. Binary data and UTF-8 strings use hex tokens, '-' empty.
 * I branch author email epoch; E env; W path bytes; U path; A; P n paths;
 * C offset message; B create branch; T tag; S; R ms exe argc args stdin;
 * F path (owned-file readback); Q. O out err exit timeout oid hasSummary,
 * followed by S branch commits branchN tagN stagedN modifiedN untrackedN
 * and N name records for each list. Git and target environments are separate.
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
struct strings { char **items; size_t size; };
struct summary { char *branch; uint64_t commits; struct strings lists[5]; int present; };
static char **child_env;
static size_t env_count;
static pid_t active_child = -1;
static char *author_name, *author_email;
static uint64_t base_epoch;
static int initialized, root_fd = -1;
static volatile sig_atomic_t stopping;
static void request_stop(int signal_number) { (void)signal_number; stopping = 1; }
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
                       struct buffer *out, struct buffer *err, int *timed_out, char **environment) {
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
        environ = environment;
        execvpe(args[0], args, environment);
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
        if (stopping && !exited) {
            killed = 1; kill(-active_child, SIGKILL); kill(active_child, SIGKILL);
        }
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
static char *copy_string(const char *s) {
    char *p = strdup(s);
    if (!p) die("strdup");
    return p;
}
static int valid_path(const char *p) {
    if (!p || !*p || *p == '/') return 0;
    if (!strncmp(p, ".git", 4) && (!p[4] || p[4] == '/')) return 0;
    for (const char *part = p;;) {
        const char *end = strchr(part, '/');
        size_t n = end ? (size_t)(end - part) : strlen(part);
        if (!n || (n == 1 && *part == '.') ||
            (n == 2 && part[0] == '.' && part[1] == '.')) return 0;
        if (!end) return 1;
        part = end + 1;
    }
}
static int valid_ref(const char *p, int branch) {
    if (!p || !*p || *p == '-' || (branch && !strcmp(p, "HEAD")) || strstr(p, "..")) return 0;
    const char *part = p;
    for (const char *c = p;; ++c) {
        if (!*c || *c == '/') {
            size_t n = (size_t)(c - part);
            if (!n || *part == '.' || c[-1] == '.' ||
                (n >= 5 && !memcmp(c - 5, ".lock", 5))) return 0;
            if (!*c) return 1;
            part = c + 1;
        } else if (!((*c >= 'a' && *c <= 'z') || (*c >= 'A' && *c <= 'Z') ||
                     (*c >= '0' && *c <= '9') || *c == '_' || *c == '-' || *c == '.')) return 0;
    }
}
/* Resolve all components relative to a retained worktree descriptor. The
 * O_NOFOLLOW checks apply to ancestors as well as leaves, including readback. */
static int parent_fd(const char *path, int create, char **leaf) {
    if (!valid_path(path)) return -1;
    char *copy = copy_string(path), *save = NULL;
    int fd = dup(root_fd);
    if (fd < 0) { free(copy); return -1; }
    char *part = strtok_r(copy, "/", &save);
    for (;;) {
        char *next = strtok_r(NULL, "/", &save);
        if (!next) { *leaf = copy_string(part); free(copy); return fd; }
        int child = openat(fd, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (child < 0 && errno == ENOENT && create) {
            if (mkdirat(fd, part, 0755) && errno != EEXIST) { close(fd); free(copy); return -1; }
            child = openat(fd, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        }
        close(fd);
        if (child < 0) { free(copy); return -1; }
        fd = child; part = next;
    }
}
static int write_file(const char *path, const struct buffer *b) {
    char *leaf = NULL;
    int parent = parent_fd(path, 1, &leaf);
    if (parent < 0) return -1;
    int fd = openat(parent, leaf, O_WRONLY | O_CREAT | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK, 0644);
    struct stat st;
    int bad = fd < 0 || fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_nlink != 1;
    if (!bad && ftruncate(fd, 0)) bad = 1;
    size_t pos = 0;
    while (!bad && pos < b->size) {
        ssize_t n = write(fd, b->data + pos, b->size - pos);
        if (n > 0) pos += (size_t)n;
        else if (n < 0 && errno == EINTR) continue;
        else bad = 1;
    }
    if (fd >= 0 && close(fd)) bad = 1;
    close(parent); free(leaf); return bad ? -1 : 0;
}
/* Directories are implicit in the byte-tree model. Remove only empty real
 * parents after deleting a leaf; never traverse a symlink or the work root. */
static void prune_empty_parents(const char *path) {
    char *prefix = copy_string(path);
    for (;;) {
        char *slash = strrchr(prefix, '/');
        if (!slash) break;
        *slash = 0;
        char *leaf = NULL;
        int parent = parent_fd(prefix, 0, &leaf);
        if (parent < 0) break;
        int result = unlinkat(parent, leaf, AT_REMOVEDIR);
        close(parent); free(leaf);
        if (result) break;
    }
    free(prefix);
}
static int remove_file(const char *path) {
    char *leaf = NULL;
    int parent = parent_fd(path, 0, &leaf);
    if (parent < 0) return -1;
    struct stat st;
    int bad = fstatat(parent, leaf, &st, AT_SYMLINK_NOFOLLOW) || !S_ISREG(st.st_mode);
    if (!bad) bad = unlinkat(parent, leaf, 0);
    close(parent); free(leaf);
    if (!bad) prune_empty_parents(path);
    return bad ? -1 : 0;
}
static int read_file(const char *path, struct buffer *b) {
    char *leaf = NULL;
    int parent = parent_fd(path, 0, &leaf);
    if (parent < 0) return -1;
    int fd = openat(parent, leaf, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK);
    struct stat st;
    int bad = fd < 0 || fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_nlink != 1;
    while (!bad) {
        unsigned char data[8192];
        ssize_t n = read(fd, data, sizeof data);
        if (n > 0) append(b, data, (size_t)n);
        else if (!n) break;
        else if (errno != EINTR) bad = 1;
    }
    if (fd >= 0) close(fd);
    close(parent); free(leaf); return bad ? -1 : 0;
}
static char *env_value(const char *key, const char *value) {
    size_t a = strlen(key), b = strlen(value);
    char *s = allocate(a + b + 2);
    memcpy(s, key, a); s[a] = '='; memcpy(s + a + 1, value, b + 1);
    return s;
}
static int git(char **args, uint64_t epoch, struct buffer *out, struct buffer *err) {
    char date[64];
    snprintf(date, sizeof date, "@%llu +0000", (unsigned long long)epoch);
    char *env[] = {"HOME=/tmp", "PATH=/usr/bin:/bin", "LC_ALL=C.UTF-8", "TZ=UTC",
        "GIT_CONFIG_NOSYSTEM=1", "GIT_CONFIG_GLOBAL=/dev/null", "GIT_TERMINAL_PROMPT=0",
        NULL, NULL, NULL, NULL, NULL, NULL, NULL};
    env[7] = env_value("GIT_AUTHOR_NAME", author_name);
    env[8] = env_value("GIT_AUTHOR_EMAIL", author_email);
    env[9] = env_value("GIT_COMMITTER_NAME", author_name);
    env[10] = env_value("GIT_COMMITTER_EMAIL", author_email);
    env[11] = env_value("GIT_AUTHOR_DATE", date);
    env[12] = env_value("GIT_COMMITTER_DATE", date);
    size_t n = 0;
    while (args[n]) ++n;
    char *prefix[] = {"/usr/bin/git", "--literal-pathspecs", "-c", "commit.gpgsign=false",
        "-c", "core.autocrlf=false", "-c", "core.filemode=false", "-c", "core.hooksPath=/dev/null",
        "-c", "core.warnAmbiguousRefs=false", "-c", "status.renames=false", "-c", "tag.gpgsign=false"};
    size_t p = sizeof prefix / sizeof prefix[0];
    char **argv = allocate((p + n + 1) * sizeof *argv);
    memcpy(argv, prefix, p * sizeof *argv); memcpy(argv + p, args, (n + 1) * sizeof *argv);
    int timed_out = 0;
    struct buffer input = {0};
    int status = run_command(argv, &input, 30000, out, err, &timed_out, env);
    for (size_t i = 7; i < 13; ++i) free(env[i]);
    free(argv); return status;
}
static void strings_add(struct strings *s, const char *p, size_t n) {
    char *v = allocate(n + 1); memcpy(v, p, n); v[n] = 0;
    void *q = realloc(s->items, (s->size + 1) * sizeof *s->items);
    if (!q) die("realloc");
    s->items = q; s->items[s->size++] = v;
}
static int string_compare(const void *a, const void *b) {
    return strcmp(*(const char *const *)a, *(const char *const *)b);
}
static void sort_strings(struct strings *s) {
    if (s->size > 1) qsort(s->items, s->size, sizeof *s->items, string_compare);
    size_t count = 0;
    for (size_t i = 0; i < s->size; ++i) {
        if (count && !strcmp(s->items[count-1], s->items[i])) free(s->items[i]);
        else s->items[count++] = s->items[i];
    }
    s->size = count;
}
static void free_summary(struct summary *s) {
    free(s->branch);
    for (size_t i = 0; i < 5; ++i) {
        for (size_t j = 0; j < s->lists[i].size; ++j) free(s->lists[i].items[j]);
        free(s->lists[i].items);
    }
    *s = (struct summary){0};
}
static char *text_output(struct buffer *out) {
    size_t n = out->size;
    while (n && out->data[n-1] == '\n') --n;
    char *p = allocate(n + 1); if (n) memcpy(p, out->data, n); p[n] = 0; return p;
}
static char *head_oid(void) {
    struct buffer out = {0}, err = {0};
    char *args[] = {"rev-parse", "--verify", "HEAD", NULL};
    int status = git(args, base_epoch, &out, &err);
    char *oid = status ? copy_string("") : text_output(&out);
    release(&out); release(&err); return oid;
}
static int status_summary(struct buffer *out, struct buffer *err, struct summary *summary, char **oid) {
    struct buffer q = {0}, e = {0};
    char *branch[] = {"symbolic-ref", "--short", "HEAD", NULL};
    int bad = git(branch, base_epoch, &q, &e);
    if (!bad) summary->branch = text_output(&q);
    release(&q); release(&e);
    if (bad) return -1;
    *oid = head_oid();
    if (**oid) {
        char *count[] = {"rev-list", "--count", "HEAD", NULL};
        bad = git(count, base_epoch, &q, &e);
        char *value = text_output(&q);
        if (!bad) bad = number(value, &summary->commits);
        free(value); release(&q); release(&e);
        if (bad) return -1;
    }
    for (size_t i = 0; i < 2; ++i) {
        char *args[] = {"for-each-ref", "--format=%(refname:short)", i ? "refs/tags" : "refs/heads", NULL};
        bad = git(args, base_epoch, &q, &e);
        if (!bad) {
            size_t start = 0;
            for (size_t j = 0; j < q.size; ++j) if (q.data[j] == '\n') {
                strings_add(&summary->lists[i], (char *)q.data + start, j - start); start = j + 1;
            }
        }
        release(&q); release(&e);
        if (bad) return -1;
    }
    char *status[] = {"status", "--porcelain=v1", "-z", "--untracked-files=all", NULL};
    bad = git(status, base_epoch, out, err);
    if (bad) return -1;
    size_t pos = 0;
    while (pos < out->size) {
        unsigned char *p = out->data + pos;
        unsigned char *end = memchr(p, 0, out->size - pos);
        if (!end || end - p < 3 || p[2] != ' ') return -1;
        size_t n = (size_t)(end - p - 3);
        if (p[0] == '?' && p[1] == '?') strings_add(&summary->lists[4], (char *)p + 3, n);
        else {
            if (p[0] != ' ' && p[0] != '!') strings_add(&summary->lists[2], (char *)p + 3, n);
            if (p[1] != ' ' && p[1] != '!') strings_add(&summary->lists[3], (char *)p + 3, n);
        }
        pos = (size_t)(end - out->data) + 1;
    }
    for (size_t i = 0; i < 5; ++i) sort_strings(&summary->lists[i]);
    summary->present = 1; return 0;
}
static void reply(const struct buffer *out, const struct buffer *err, int status,
                  int timed_out, const char *oid, const struct summary *summary) {
    fputs("O ", stdout); hex(out->data, out->size); putchar(' '); hex(err->data, err->size);
    printf(" %d %d ", status, timed_out); hex(oid, strlen(oid)); printf(" %d\n", summary->present);
    if (summary->present) {
        fputs("S ", stdout); hex(summary->branch, strlen(summary->branch));
        printf(" %llu", (unsigned long long)summary->commits);
        for (size_t i = 0; i < 5; ++i) printf(" %zu", summary->lists[i].size);
        putchar('\n');
        for (size_t i = 0; i < 5; ++i) for (size_t j = 0; j < summary->lists[i].size; ++j) {
            char *name = summary->lists[i].items[j];
            fputs("N ", stdout); hex(name, strlen(name)); putchar('\n');
        }
    }
    if (fflush(stdout)) exit(0);
}
static int valid_identity(const char *p) {
    return p && *p && !strchr(p, '\n') && !strchr(p, '\r') && !strchr(p, '<') && !strchr(p, '>');
}
int main(void) {
    umask(0); signal(SIGPIPE, SIG_IGN);
    struct sigaction stop_action = {0};
    stop_action.sa_handler = request_stop;
    if (sigemptyset(&stop_action.sa_mask) || sigaction(SIGTERM, &stop_action, NULL) ||
        sigaction(SIGINT, &stop_action, NULL) || sigaction(SIGHUP, &stop_action, NULL)) die("sigaction");
    if (prctl(PR_SET_CHILD_SUBREAPER, 1)) die("subreaper");
    if (atexit(emergency_cleanup)) die("atexit");
    root_fd = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (root_fd < 0) die("worktree");
    child_env = calloc(1, sizeof *child_env);
    if (!child_env) die("calloc");
    setvbuf(stdin, NULL, _IONBF, 0);
    puts("READY"); fflush(stdout);
    char *line = NULL; size_t capacity = 0;
    for (;;) {
        if (stopping) break;
        ssize_t line_size = getline(&line, &capacity, stdin);
        if (line_size < 0) break;
        int bad = memchr(line, 0, (size_t)line_size) != NULL, quitting = 0;
        size_t count = 0;
        char **t = tokens(line, &count);
        struct buffer out = {0}, err = {0};
        struct summary summary = {0};
        char *oid = NULL;
        int status = -1, timed_out = 0;
        if (!count || strlen(t[0]) != 1) bad = 1;
        if (!bad && !strcmp(t[0], "Q") && count == 1) quitting = 1;
        else if (!bad && !strcmp(t[0], "E") && count == 2) {
            char *value = decode_string(t[1]);
            if (!valid_env(value)) { free(value); bad = 1; }
            else {
                void *p = realloc(child_env, (env_count + 2) * sizeof *child_env);
                if (!p) die("realloc");
                child_env = p; child_env[env_count++] = value; child_env[env_count] = NULL;
            }
        } else if (!bad && !strcmp(t[0], "I") && count == 5 && !initialized) {
            char *branch = decode_string(t[1]), *name = decode_string(t[2]), *email = decode_string(t[3]);
            uint64_t epoch;
            bad = !valid_ref(branch, 1) || !valid_identity(name) || !valid_identity(email) || number(t[4], &epoch);
            if (!bad) {
                author_name = name; author_email = email; name = NULL; email = NULL; base_epoch = epoch;
                char *setting = env_value("init.defaultBranch", branch);
                char *args[] = {"-c", setting, "init", "-q", "--object-format=sha1", "--template=", NULL};
                status = git(args, base_epoch, &out, &err); initialized = status == 0;
                free(setting);
            }
            free(branch); free(name); free(email);
        } else if (!bad && !initialized) bad = 1;
        else if (!bad && !strcmp(t[0], "S") && count == 1) {
            bad = status_summary(&out, &err, &summary, &oid); status = 0;
        } else if (!bad && !strcmp(t[0], "R") && count >= 5) {
            uint64_t timeout = 0, argc = 0;
            bad = number(t[1], &timeout) || number(t[3], &argc) || argc > count || argc != count - 5;
            char **args = NULL; struct buffer input = {0};
            if (!bad) {
                args = calloc((size_t)argc + 2, sizeof *args);
                if (!args) die("calloc");
                args[0] = decode_string(t[2]); bad = !args[0] || !*args[0];
                for (size_t i = 0; i < argc; ++i) { args[i+1] = decode_string(t[i+4]); if (!args[i+1]) bad = 1; }
                if (decode(t[count-1], &input)) bad = 1;
                if (!bad) status = run_command(args, &input, timeout, &out, &err, &timed_out, child_env);
            }
            if (args) { for (size_t i = 0; i <= argc; ++i) free(args[i]); free(args); }
            release(&input);
        } else if (!bad && !strcmp(t[0], "W") && count == 3) {
            char *path = decode_string(t[1]); struct buffer content = {0};
            bad = decode(t[2], &content) || write_file(path, &content);
            free(path); release(&content);
        } else if (!bad && !strcmp(t[0], "U") && count == 2) {
            char *path = decode_string(t[1]); bad = remove_file(path); free(path);
        } else if (!bad && !strcmp(t[0], "F") && count == 2) {
            char *path = decode_string(t[1]); bad = read_file(path, &out); free(path);
        } else if (!bad && !strcmp(t[0], "A") && count == 1) {
            char *args[] = {"add", "-A", NULL}; status = git(args, base_epoch, &out, &err);
        } else if (!bad && !strcmp(t[0], "P") && count >= 2) {
            uint64_t n = 0;
            bad = number(t[1], &n) || n != count - 2;
            if (!bad) {
                char **args = calloc((size_t)n + 3, sizeof *args);
                if (!args) die("calloc");
                args[0] = "add"; args[1] = "--";
                for (size_t i = 0; i < n; ++i) { args[i+2] = decode_string(t[i+2]); if (!valid_path(args[i+2])) bad = 1; }
                if (!bad && n) status = git(args, base_epoch, &out, &err);
                for (size_t i = 0; i < n; ++i) free(args[i+2]);
                free(args);
            }
        } else if (!bad && !strcmp(t[0], "C") && count == 3) {
            uint64_t offset = 0; char *message = decode_string(t[2]);
            bad = number(t[1], &offset) || offset > UINT64_MAX - base_epoch || !message;
            if (!bad) {
                char *args[] = {"commit", "-q", "--cleanup=verbatim", "-m", message, NULL};
                status = git(args, base_epoch + offset, &out, &err);
                oid = head_oid();
            }
            free(message);
        } else if (!bad && !strcmp(t[0], "B") && count == 3) {
            char *branch = decode_string(t[2]);
            bad = !valid_ref(branch, 1) || (strcmp(t[1], "0") && strcmp(t[1], "1"));
            if (!bad) {
                char *create[] = {"checkout", "-q", "-b", branch, NULL};
                char *existing[] = {"checkout", "-q", branch, "--", NULL};
                status = git(!strcmp(t[1], "1") ? create : existing, base_epoch, &out, &err);
            }
            free(branch);
        } else if (!bad && !strcmp(t[0], "T") && count == 2) {
            char *tag = decode_string(t[1]); bad = !valid_ref(tag, 0);
            if (!bad) { char *args[] = {"tag", "--", tag, NULL}; status = git(args, base_epoch, &out, &err); }
            free(tag);
        } else if (!quitting) bad = 1;
        if (bad) {
            static const char message[] = "git operation rejected";
            release(&out); release(&err); free_summary(&summary); free(oid); oid = NULL;
            append(&err, message, sizeof message - 1); status = 1; timed_out = 0;
        }
        reply(&out, &err, status, timed_out, oid ? oid : "", &summary);
        free(t); release(&out); release(&err); free_summary(&summary); free(oid);
        if (quitting) break;
    }
    free(line); free(author_name); free(author_email);
    for (size_t i = 0; i < env_count; ++i) free(child_env[i]);
    free(child_env); close(root_fd); return 0;
}
