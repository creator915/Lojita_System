/* Loopback-only network relay. Control tokens are hex ('-' is empty).
 * Responses: O stdout stderr wire status timed captureCount, then C hex.
 * HTTP responses, including the fallback, are supplied verbatim by the Lean host. */
#define _GNU_SOURCE
#include <arpa/inet.h>
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
#include <strings.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

struct buffer { unsigned char *data; size_t size, capacity; };
struct captures { struct buffer *items; size_t size; };
struct process { pid_t pid; int input, output, error, exited, status; };
struct rule { char *method, *target; struct buffer prefix, reply; };
struct connection { int fd, replying; int64_t touched, reply_at; size_t sent; struct buffer request; const struct buffer *reply; };
static struct process daemon_proc = { .pid = -1, .input = -1, .output = -1, .error = -1 };
static struct process client_proc = { .pid = -1, .input = -1, .output = -1, .error = -1 };
static struct buffer daemon_out, daemon_err, fallback;
static int daemon_status = -1, listener = -1, mode;
static uint64_t stub_delay_ms = 0;
static unsigned port;
static char **child_env;
static size_t env_count, rule_count, connection_count;
static struct rule *rules;
static struct connection *connections;
static volatile sig_atomic_t interrupted;

static void cleanup(void);
static void die(const char *s) { perror(s); exit(125); }
static void *allocate(size_t n) { void *p = malloc(n ? n : 1); if (!p) die("malloc"); return p; }
static void *resize(void *p, size_t n) { void *q = realloc(p, n ? n : 1); if (!q) die("realloc"); return q; }
static void append(struct buffer *b, const void *p, size_t n) {
    if (n > SIZE_MAX - b->size) die("buffer overflow");
    size_t total = b->size + n;
    if (total > b->capacity) {
        b->capacity = total <= SIZE_MAX / 2 ? total * 2 : total;
        b->data = resize(b->data, b->capacity);
    }
    if (n) memcpy(b->data + b->size, p, n);
    b->size = total;
}
static void release(struct buffer *b) { free(b->data); *b = (struct buffer){0}; }
static int64_t millis(void) {
    struct timespec t; if (clock_gettime(CLOCK_MONOTONIC, &t)) die("clock");
    return (int64_t)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}
static void nonblock(int fd) {
    int f = fcntl(fd, F_GETFL); if (f < 0 || fcntl(fd, F_SETFL, f | O_NONBLOCK) < 0) die("fcntl");
}
static void close_fd(int *fd) { if (*fd >= 0) close(*fd); *fd = -1; }
static int nibble(unsigned char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}
static int decode(const char *s, struct buffer *b) {
    if (!s) return -1;
    if (!strcmp(s, "-")) return 0;
    size_t n = strlen(s); if (!n || n % 2) return -1;
    for (size_t i = 0; i < n; i += 2) {
        int a = nibble((unsigned char)s[i]), c = nibble((unsigned char)s[i+1]);
        if (a < 0 || c < 0) return -1;
        unsigned char value = (unsigned char)(16*a+c); append(b, &value, 1);
    }
    return 0;
}
static char *decode_string(const char *s) {
    struct buffer b = {0};
    if (decode(s, &b) || (b.size && memchr(b.data, 0, b.size))) { release(&b); return NULL; }
    append(&b, "", 1); return (char *)b.data;
}
static int number(const char *s, uint64_t *value) {
    if (!s || !*s) return -1;
    uint64_t n = 0;
    for (; *s; ++s) {
        if (*s < '0' || *s > '9' || n > (UINT64_MAX-(unsigned)(*s-'0'))/10) return -1;
        n = n*10+(unsigned)(*s-'0');
    }
    *value = n; return 0;
}
static void hex(const struct buffer *b) {
    const char digits[] = "0123456789abcdef";
    if (!b->size) putchar('-');
    for (size_t i = 0; i < b->size; ++i) { putchar(digits[b->data[i] >> 4]); putchar(digits[b->data[i] & 15]); }
}
static void reply(const struct buffer *out, const struct buffer *err, const struct buffer *wire,
                  int status, int timed, const struct captures *cs) {
    fputs("O ", stdout); hex(out); putchar(' '); hex(err); putchar(' '); hex(wire);
    printf(" %d %d %zu\n", status, timed, cs->size);
    for (size_t i = 0; i < cs->size; ++i) { fputs("C ", stdout); hex(&cs->items[i]); putchar('\n'); }
    if (fflush(stdout)) exit(0);
}
static void capture(struct captures *cs, const struct buffer *b) {
    cs->items = resize(cs->items, (cs->size+1)*sizeof *cs->items);
    cs->items[cs->size] = (struct buffer){0};
    append(&cs->items[cs->size++], b->data, b->size);
}
static void free_captures(struct captures *cs) {
    for (size_t i = 0; i < cs->size; ++i) release(&cs->items[i]);
    free(cs->items); *cs = (struct captures){0};
}
static char *substitute(const char *s) {
    char port_text[16], addr[40], url[48];
    snprintf(port_text, sizeof port_text, "%u", port);
    snprintf(addr, sizeof addr, "127.0.0.1:%u", port);
    snprintf(url, sizeof url, "http://127.0.0.1:%u", port);
    struct buffer b = {0};
    while (*s) {
        const char *v = NULL; size_t used = 0;
        if (!strncmp(s, "{{PORT}}", 8)) { v = port_text; used = 8; }
        else if (!strncmp(s, "{{ADDR}}", 8)) { v = addr; used = 8; }
        else if (!strncmp(s, "{{URL}}", 7)) { v = url; used = 7; }
        if (v) { append(&b, v, strlen(v)); s += used; }
        else append(&b, s++, 1);
    }
    append(&b, "", 1); return (char *)b.data;
}
static int valid_env(const char *s) {
    if (!s || !((*s >= 'a' && *s <= 'z') || (*s >= 'A' && *s <= 'Z') || *s == '_')) return 0;
    const char *eq = strchr(s, '='); if (!eq) return 0;
    for (const char *p = s; p < eq; ++p)
        if (!((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9') || *p == '_')) return 0;
    size_t len = (size_t)(eq-s);
    for (size_t i = 0; i < env_count; ++i)
        if (!strncmp(child_env[i], s, len) && child_env[i][len] == '=') return 0;
    return 1;
}
/* Walk relative paths with directory fds; no ancestor or leaf symlink is followed. */
static int materialize(const char *name, const struct buffer *data) {
    if (!name || !*name || *name == '/') return -1;
    char *path = strdup(name); if (!path) die("strdup");
    int dir = open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC), result = -1;
    char *part = path;
    if (dir < 0) { free(path); return -1; }
    for (;;) {
        char *slash = strchr(part, '/'); if (slash) *slash = 0;
        if (!*part || !strcmp(part, ".") || !strcmp(part, "..")) break;
        if (slash) {
            if (mkdirat(dir, part, 0755) && errno != EEXIST) break;
            int next = openat(dir, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
            if (next < 0) break;
            close(dir); dir = next; part = slash+1;
        } else {
            int fd = openat(dir, part, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0644);
            if (fd < 0) break;
            size_t sent = 0; result = 0;
            while (sent < data->size) {
                ssize_t n = write(fd, data->data+sent, data->size-sent);
                if (n > 0) sent += (size_t)n;
                else if (n < 0 && errno == EINTR) continue;
                else { result = -1; break; }
            }
            if (close(fd)) result = -1;
            break;
        }
    }
    close(dir); free(path); return result;
}
static void drain(int *fd, struct buffer *b) {
    if (*fd < 0) return;
    for (int batch = 0; batch < 32; ++batch) {
        unsigned char data[8192]; ssize_t n = read(*fd, data, sizeof data);
        if (n > 0) append(b, data, (size_t)n);
        else if (!n) { close_fd(fd); break; }
        else if (errno == EINTR) continue;
        else if (errno == EAGAIN || errno == EWOULDBLOCK) break;
        else { close_fd(fd); break; }
    }
}
static void observe_process(struct process *p) {
    if (p->pid <= 0 || p->exited) return;
    int status; pid_t got = waitpid(p->pid, &status, WNOHANG);
    if (got == p->pid) {
        p->exited = 1;
        p->status = WIFEXITED(status) ? WEXITSTATUS(status) : 128+WTERMSIG(status);
    }
}
static void pump_daemon(void) {
    drain(&daemon_proc.output, &daemon_out); drain(&daemon_proc.error, &daemon_err);
    int old = daemon_proc.exited; observe_process(&daemon_proc);
    if (!old && daemon_proc.exited) daemon_status = daemon_proc.status;
}
static void kill_adopted(pid_t keep) {
    char path[96]; snprintf(path, sizeof path, "/proc/self/task/%ld/children", (long)getpid());
    FILE *f = fopen(path, "r"); if (!f) return;
    long pid; while (fscanf(f, "%ld", &pid) == 1) if (pid > 0 && pid != keep) kill((pid_t)pid, SIGKILL);
    fclose(f);
}
static void finish_process(struct process *p) {
    if (p->pid <= 0) return;
    kill(-p->pid, SIGTERM); if (!p->exited) kill(p->pid, SIGTERM);
    int64_t end = millis()+50;
    while (millis() < end) { pump_daemon(); observe_process(p); (void)poll(NULL, 0, 5); }
    kill(-p->pid, SIGKILL); if (!p->exited) kill(p->pid, SIGKILL);
    if (!p->exited) {
        int status; pid_t got;
        do { got = waitpid(p->pid, &status, 0); } while (got < 0 && errno == EINTR);
        if (got == p->pid) { p->status = WIFEXITED(status) ? WEXITSTATUS(status) : 128+WTERMSIG(status); p->exited = 1; }
    }
    close_fd(&p->input);
}
static void reap_all(void) {
    for (;;) {
        kill_adopted(-1);
        pid_t p = waitpid(-1, NULL, 0);
        if (p > 0 || (p < 0 && errno == EINTR)) continue;
        break;
    }
}
/* Docker files belong to uid 65534. After every child has been reaped, grant
 * the host readback/cleanup access. Net ownership models bytes, not modes.
 * lstat precedes every chmod/traversal; links and multiply-linked files are
 * never chmodded, so an external sentinel cannot be changed through a link. */
static void prepare_tree(const char *path, int root) {
    struct stat st;
    if (lstat(path, &st)) return;
    if (S_ISDIR(st.st_mode)) {
        if (!root && chmod(path, (st.st_mode & 0777) | 0777)) return;
        DIR *dir = opendir(path); if (!dir) return;
        struct dirent *entry;
        while ((entry = readdir(dir)) != NULL) {
            if (!strcmp(entry->d_name, ".") || !strcmp(entry->d_name, "..")) continue;
            size_t a = strlen(path), b = strlen(entry->d_name);
            char *child = malloc(a+b+2); if (!child) break;
            memcpy(child, path, a); child[a] = '/'; memcpy(child+a+1, entry->d_name, b+1);
            prepare_tree(child, 0); free(child);
        }
        closedir(dir);
    } else if (S_ISREG(st.st_mode) && st.st_nlink == 1) {
        int result = chmod(path, (st.st_mode & 0777) | 0444); (void)result;
    }
}
static void cleanup(void) {
    if (client_proc.pid > 0) { kill(-client_proc.pid, SIGKILL); kill(client_proc.pid, SIGKILL); }
    if (daemon_proc.pid > 0) { kill(-daemon_proc.pid, SIGKILL); kill(daemon_proc.pid, SIGKILL); }
    reap_all();
    prepare_tree(".", 1);
}
/* CLOEXEC error pipe reports failed exec synchronously, before openNet succeeds. */
static int spawn(struct process *p, char **args) {
    int in[2], out[2], err[2], ready[2];
    if (pipe2(in, O_CLOEXEC) || pipe2(out, O_CLOEXEC) || pipe2(err, O_CLOEXEC) || pipe2(ready, O_CLOEXEC)) die("pipe");
    pid_t parent = getpid(), pid = fork(); if (pid < 0) die("fork");
    if (!pid) {
        close(ready[0]);
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) || getppid() != parent || setsid() < 0 ||
            dup2(in[0], 0) < 0 || dup2(out[1], 1) < 0 || dup2(err[1], 2) < 0) goto failed;
        close(in[0]); close(in[1]); close(out[0]); close(out[1]); close(err[0]); close(err[1]);
        signal(SIGPIPE, SIG_DFL); signal(SIGTERM, SIG_DFL); signal(SIGINT, SIG_DFL);
        char **env = allocate((env_count+1)*sizeof *env);
        for (size_t i = 0; i < env_count; ++i) env[i] = substitute(child_env[i]);
        env[env_count] = NULL;
        for (size_t i = 0; args[i]; ++i) args[i] = substitute(args[i]);
        environ = env; execvpe(args[0], args, env);
failed: { int e = errno ? errno : EINVAL; ssize_t written = write(ready[1], &e, sizeof e); (void)written; _exit(127); }
    }
    close(in[0]); close(out[1]); close(err[1]); close(ready[1]);
    *p = (struct process){ .pid = pid, .input = in[1], .output = out[0], .error = err[0] };
    nonblock(p->input); nonblock(p->output); nonblock(p->error);
    int e; ssize_t n; do { n = read(ready[0], &e, sizeof e); } while (n < 0 && errno == EINTR);
    close(ready[0]); return n == 0 ? 0 : -1;
}
static int bind_loopback(int type, int keep) {
    int fd = socket(AF_INET, type | SOCK_CLOEXEC | SOCK_NONBLOCK, 0); if (fd < 0) return -1;
    struct sockaddr_in addr = { .sin_family = AF_INET, .sin_addr.s_addr = htonl(INADDR_LOOPBACK), .sin_port = 0 };
    if (bind(fd, (struct sockaddr *)&addr, sizeof addr)) { close(fd); return -1; }
    socklen_t len = sizeof addr;
    if (getsockname(fd, (struct sockaddr *)&addr, &len)) { close(fd); return -1; }
    port = ntohs(addr.sin_port);
    if (!keep) { close(fd); return 0; }
    if (type == SOCK_STREAM && listen(fd, 64)) { close(fd); return -1; }
    listener = fd; return 0;
}
static const struct buffer *raw_reply(const struct buffer *request) {
    for (size_t i = 0; i < rule_count; ++i)
        if (rules[i].prefix.size <= request->size && (!rules[i].prefix.size ||
            !memcmp(rules[i].prefix.data, request->data, rules[i].prefix.size))) return &rules[i].reply;
    static const struct buffer empty; return &empty;
}
static const struct buffer *http_reply(const struct buffer *request) {
    const unsigned char *space = memchr(request->data, ' ', request->size);
    if (!space) return &fallback;
    size_t method_len = (size_t)(space-request->data), left = request->size-method_len-1;
    const unsigned char *target = space+1, *end = memchr(target, ' ', left);
    if (!end) return &fallback;
    size_t target_len = (size_t)(end-target);
    for (size_t i = 0; i < rule_count; ++i) {
        struct rule *r = &rules[i];
        if ((!strcmp(r->method, "*") || (strlen(r->method) == method_len && !memcmp(r->method, request->data, method_len))) &&
            (!strcmp(r->target, "*") || (strlen(r->target) == target_len && !memcmp(r->target, target, target_len)))) return &r->reply;
    }
    return &fallback;
}
/* 0 incomplete, 1 complete, -1 malformed framing. Body bytes remain opaque. */
static int http_complete(const struct buffer *b, size_t *total) {
    size_t header = 0;
    for (size_t i = 0; i+3 < b->size; ++i)
        if (!memcmp(b->data+i, "\r\n\r\n", 4)) { header = i+4; break; }
    if (!header) return 0;
    size_t body = 0, line = 0; int found = 0;
    while (line+1 < header) {
        size_t end = line;
        while (end+1 < header && memcmp(b->data+end, "\r\n", 2)) ++end;
        if (end+1 >= header) return -1;
        if (end-line >= 15 && !strncasecmp((char *)b->data+line, "Content-Length:", 15)) {
            size_t p = line+15, value = 0; while (p < end && (b->data[p] == ' ' || b->data[p] == '\t')) ++p;
            size_t digits = p;
            while (p < end && b->data[p] >= '0' && b->data[p] <= '9') {
                if (value > (SIZE_MAX-(b->data[p]-'0'))/10) return -1;
                value = value*10+b->data[p++]-'0';
            }
            if (p == digits) return -1;
            while (p < end && (b->data[p] == ' ' || b->data[p] == '\t')) ++p;
            if (p != end || (found && body != value)) return -1;
            body = value; found = 1;
        }
        line = end+2;
    }
    if (body > SIZE_MAX-header) return -1;
    *total = header+body; return b->size >= *total;
}
static void close_connection(struct connection *c) { close_fd(&c->fd); release(&c->request); }
static void clear_connections(void) {
    for (size_t i = 0; i < connection_count; ++i) close_connection(&connections[i]);
    free(connections); connections = NULL; connection_count = 0;
}
static void service_stub(struct captures *cs) {
    if (listener < 0) return;
    if (mode == 3) {
        for (int batch = 0; batch < 64; ++batch) {
            unsigned char data[65536]; struct sockaddr_in peer; socklen_t len = sizeof peer;
            ssize_t n = recvfrom(listener, data, sizeof data, 0, (struct sockaddr *)&peer, &len);
            if (n < 0) { if (errno == EINTR) continue; break; }
            if (peer.sin_family != AF_INET || peer.sin_addr.s_addr != htonl(INADDR_LOOPBACK)) continue;
            struct buffer packet = { .data = data, .size = (size_t)n };
            capture(cs, &packet); const struct buffer *response = raw_reply(&packet);
            (void)sendto(listener, response->data, response->size, 0, (struct sockaddr *)&peer, len);
        }
        return;
    }
    for (int batch = 0; batch < 64; ++batch) {
        int fd = accept4(listener, NULL, NULL, SOCK_CLOEXEC | SOCK_NONBLOCK);
        if (fd < 0) { if (errno == EINTR) continue; break; }
        connections = resize(connections, (connection_count+1)*sizeof *connections);
        connections[connection_count++] = (struct connection){ .fd = fd, .touched = millis() };
    }
    for (size_t i = 0; i < connection_count; ++i) {
        struct connection *c = &connections[i]; if (c->fd < 0) continue;
        if (!c->replying) {
            int eof = 0;
            for (int batch = 0; batch < 32; ++batch) {
                unsigned char data[8192]; ssize_t n = recv(c->fd, data, sizeof data, 0);
                if (n > 0) { append(&c->request, data, (size_t)n); c->touched = millis(); }
                else if (!n) { eof = 1; break; }
                else if (errno == EINTR) continue;
                else if (errno == EAGAIN || errno == EWOULDBLOCK) break;
                else { close_connection(c); break; }
            }
            if (c->fd < 0) continue;
            size_t total = 0;
            int complete = mode == 1 ? http_complete(&c->request, &total) :
                (eof || (c->request.size && millis()-c->touched >= 50));
            if (complete < 0 || (mode == 1 && eof && !complete)) { close_connection(c); continue; }
            if (complete) {
                if (mode == 1) c->request.size = total;
                capture(cs, &c->request);
                c->reply = mode == 1 ? http_reply(&c->request) : raw_reply(&c->request);
                c->reply_at = millis() + (int64_t)stub_delay_ms;
                c->replying = 1;
            }
        }
        if (c->replying && millis() >= c->reply_at) {
            while (c->sent < c->reply->size) {
                ssize_t n = send(c->fd, c->reply->data+c->sent, c->reply->size-c->sent, MSG_NOSIGNAL);
                if (n > 0) c->sent += (size_t)n;
                else if (n < 0 && errno == EINTR) continue;
                else if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) break;
                else { close_connection(c); break; }
            }
            if (c->fd >= 0 && c->sent == c->reply->size) close_connection(c);
        }
    }
    size_t kept = 0;
    for (size_t i = 0; i < connection_count; ++i)
        if (connections[i].fd >= 0) connections[kept++] = connections[i];
    connection_count = kept;
}
/* One poll set pumps process pipes, loopback listeners and accepted sockets. */
static void pump_wait(int delay, struct process *p, int extra, short events, struct captures *cs) {
    size_t count = connection_count+7;
    struct pollfd *fds = allocate(count*sizeof *fds); size_t n = 0;
    fds[n++] = (struct pollfd){STDIN_FILENO, 0, 0};
    fds[n++] = (struct pollfd){daemon_proc.output, POLLIN, 0};
    fds[n++] = (struct pollfd){daemon_proc.error, POLLIN, 0};
    fds[n++] = (struct pollfd){p ? p->output : -1, POLLIN, 0};
    fds[n++] = (struct pollfd){p ? p->error : -1, POLLIN, 0};
    fds[n++] = (struct pollfd){listener, POLLIN, 0};
    fds[n++] = (struct pollfd){extra, events, 0};
    for (size_t i = 0; i < connection_count; ++i)
        fds[n++] = (struct pollfd){connections[i].fd,
            (connections[i].replying && millis() >= connections[i].reply_at) ? POLLOUT :
            (connections[i].replying ? 0 : POLLIN), 0};
    if (poll(fds, n, delay) < 0 && errno != EINTR) die("poll");
    if (fds[0].revents & (POLLHUP | POLLERR)) interrupted = 1;
    free(fds); pump_daemon(); if (cs) service_stub(cs);
}
/* Once a client and its descendants are gone, consume queued sends before
 * returning its observation. Otherwise short-lived UDP senders could leave
 * packets to be incorrectly attributed to the next runClient call. */
static void settle_stub(struct captures *cs) {
    int64_t end = millis()+100;
    do {
        service_stub(cs);
        struct pollfd *fds = allocate((connection_count+1)*sizeof *fds);
        fds[0] = (struct pollfd){listener, POLLIN, 0};
        for (size_t i = 0; i < connection_count; ++i)
            fds[i+1] = (struct pollfd){connections[i].fd, connections[i].replying ? POLLOUT : POLLIN, 0};
        int ready = poll(fds, connection_count+1, 0); free(fds);
        if (ready <= 0) break;
    } while (millis() < end);
}
static int run_client(char **args, const struct buffer *input, uint64_t timeout,
                      struct buffer *out, struct buffer *err, int *timed, struct captures *cs) {
    int failed = spawn(&client_proc, args); size_t sent = 0; int64_t start = millis();
    if (failed) { finish_process(&client_proc); }
    for (;;) {
        drain(&client_proc.output, out); drain(&client_proc.error, err); observe_process(&client_proc);
        service_stub(cs);
        if (client_proc.exited || interrupted) break;
        if ((uint64_t)(millis()-start) >= timeout) { *timed = 1; break; }
        if (client_proc.input >= 0) {
            if (sent == input->size) close_fd(&client_proc.input);
            else {
                size_t amount = input->size-sent; if (amount > 65536) amount = 65536;
                ssize_t n = write(client_proc.input, input->data+sent, amount);
                if (n > 0) sent += (size_t)n;
                else if (n < 0 && errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) close_fd(&client_proc.input);
            }
        }
        uint64_t remaining = timeout-(uint64_t)(millis()-start);
        pump_wait(remaining < 10 ? (int)remaining : 10, &client_proc, client_proc.input, POLLOUT, cs);
    }
    int status = client_proc.exited ? client_proc.status : 124;
    finish_process(&client_proc);
    /* Stub clients cannot leave descendants holding stdout or the workspace. */
    if (daemon_proc.pid <= 0) reap_all();
    settle_stub(cs);
    drain(&client_proc.output, out); drain(&client_proc.error, err);
    close_fd(&client_proc.output); close_fd(&client_proc.error); client_proc.pid = -1;
    clear_connections(); return *timed ? 124 : status;
}
static int connect_socket(int type) {
    int fd = socket(AF_INET, type | SOCK_NONBLOCK | SOCK_CLOEXEC, 0); if (fd < 0) return -1;
    struct sockaddr_in addr = { .sin_family = AF_INET, .sin_port = htons((uint16_t)port),
                               .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
    if (connect(fd, (struct sockaddr *)&addr, sizeof addr) && errno != EINPROGRESS) { close(fd); return -1; }
    return fd;
}
static int connected(int fd) {
    struct pollfd p = {fd, POLLOUT, 0};
    if (poll(&p, 1, 0) <= 0 || !p.revents) return 0;
    int error = 0; socklen_t len = sizeof error;
    return getsockopt(fd, SOL_SOCKET, SO_ERROR, &error, &len) || error ? -1 : 1;
}
static void wait_ready(uint64_t timeout, int *timed, struct captures *cs) {
    int64_t start = millis();
    for (;;) {
        int fd = connect_socket(SOCK_STREAM);
        if (fd >= 0) {
            for (;;) {
                int ready = connected(fd); if (ready) { close(fd); if (ready > 0) return; break; }
                if (interrupted || (uint64_t)(millis()-start) >= timeout) { close(fd); *timed = 1; return; }
                pump_wait(5, NULL, fd, POLLOUT, cs);
            }
        }
        if (interrupted || (uint64_t)(millis()-start) >= timeout) { *timed = 1; return; }
        pump_wait(10, NULL, -1, 0, cs);
    }
}
static void probe(char op, uint64_t timeout, const struct buffer *input,
                  struct buffer *wire, int *timed, struct captures *cs) {
    int64_t start = millis(); int fd = connect_socket(op == 'G' ? SOCK_DGRAM : SOCK_STREAM);
    if (fd < 0) { *timed = 1; return; }
    int ready = op == 'G', shut = 0, datagram_sent = 0; size_t sent = 0;
    for (;;) {
        if (!ready) {
            int state = connected(fd); if (state < 0) { *timed = 1; break; }
            ready = state > 0;
        }
        if (ready && (sent < input->size || (op == 'G' && !datagram_sent))) {
            ssize_t n = send(fd, input->data ? input->data+sent : NULL, input->size-sent, MSG_NOSIGNAL);
            if (n >= 0) { sent += (size_t)n; datagram_sent = 1; }
            else if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) { *timed = 1; break; }
        }
        if (ready && sent == input->size && op == 'C' && !shut) { (void)shutdown(fd, SHUT_WR); shut = 1; }
        if (ready) {
            unsigned char data[65536]; ssize_t n = recv(fd, data, sizeof data, 0);
            if (n > 0 || (n == 0 && op == 'G')) { append(wire, data, (size_t)n); if (op == 'G') break; }
            else if (!n) break;
            else if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) { *timed = 1; break; }
        }
        if (interrupted || (uint64_t)(millis()-start) >= timeout) { *timed = 1; break; }
        short events = POLLIN; if (!ready || sent < input->size || (op == 'G' && !datagram_sent)) events |= POLLOUT;
        pump_wait(10, NULL, fd, events, cs);
    }
    close(fd); pump_daemon();
}
static char **tokens(char *line, size_t *count) {
    char **parts = NULL, *save = NULL; *count = 0;
    for (char *p = strtok_r(line, " \t\r\n", &save); p; p = strtok_r(NULL, " \t\r\n", &save)) {
        parts = resize(parts, (*count+1)*sizeof *parts); parts[(*count)++] = p;
    }
    return parts;
}
static char **parse_args(char **tokens_in, size_t count, size_t exe_index, size_t argc_index, size_t first, size_t tail) {
    uint64_t argc;
    if (number(tokens_in[argc_index], &argc) || argc > count || argc != count-first-tail) return NULL;
    char **args = calloc((size_t)argc+2, sizeof *args); if (!args) die("calloc");
    args[0] = decode_string(tokens_in[exe_index]); int bad = !args[0] || !*args[0];
    for (size_t i = 0; i < argc; ++i) { args[i+1] = decode_string(tokens_in[first+i]); if (!args[i+1]) bad = 1; }
    if (bad) { for (size_t i = 0; i <= argc; ++i) free(args[i]); free(args); return NULL; }
    return args;
}
static void free_args(char **args) { if (args) { for (size_t i = 0; args[i]; ++i) free(args[i]); free(args); } }
/* Read control lines while draining a live daemon, including between calls. */
static char *read_command(struct buffer *pending) {
    for (;;) {
        unsigned char *newline = pending->size ? memchr(pending->data, '\n', pending->size) : NULL;
        if (newline) {
            size_t n = (size_t)(newline-pending->data), consumed = n+1;
            char *line = allocate(n+1); memcpy(line, pending->data, n); line[n] = 0;
            if (memchr(line, 0, n)) { free(line); return NULL; }
            memmove(pending->data, pending->data+consumed, pending->size-consumed); pending->size -= consumed;
            return line;
        }
        if (interrupted) return NULL;
        struct pollfd fds[3] = {{STDIN_FILENO, POLLIN, 0}, {daemon_proc.output, POLLIN, 0}, {daemon_proc.error, POLLIN, 0}};
        if (poll(fds, 3, 20) < 0 && errno != EINTR) die("poll control");
        pump_daemon();
        if (fds[0].revents) {
            unsigned char data[8192]; ssize_t n = read(STDIN_FILENO, data, sizeof data);
            if (n > 0) append(pending, data, (size_t)n);
            else if (!n) return NULL;
            else if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) return NULL;
        }
    }
}
static void interrupted_handler(int signal_number) { (void)signal_number; interrupted = 1; }
int main(void) {
    umask(0); signal(SIGPIPE, SIG_IGN); signal(SIGTERM, interrupted_handler); signal(SIGINT, interrupted_handler);
    if (prctl(PR_SET_CHILD_SUBREAPER, 1) || atexit(cleanup)) die("subreaper/atexit");
    child_env = calloc(1, sizeof *child_env); if (!child_env) die("calloc");
    nonblock(STDIN_FILENO); puts("READY"); fflush(stdout);
    struct buffer pending = {0}; int failed = 0;
    for (;;) {
        char *line = read_command(&pending); if (!line) break;
        size_t count = 0; char **t = tokens(line, &count);
        int bad = !count || strlen(t[0]) != 1, quitting = 0, status = -1, timed = 0;
        struct buffer out = {0}, err = {0}, wire = {0}; struct captures cs = {0};
        char op = bad ? 0 : t[0][0];
        if (!bad && op == 'Q' && count == 1) {
            quitting = 1; finish_process(&daemon_proc); reap_all(); pump_daemon();
        } else if (!bad && op == 'E' && count == 2 && !mode) {
            char *v = decode_string(t[1]); if (!valid_env(v)) { free(v); bad = 1; }
            else { child_env = resize(child_env, (env_count+2)*sizeof *child_env); child_env[env_count++] = v; child_env[env_count] = NULL; }
        } else if (!bad && op == 'W' && count == 3 && !mode) {
            char *path = decode_string(t[1]); struct buffer data = {0};
            bad = decode(t[2], &data) || materialize(path, &data); free(path); release(&data);
        } else if (!bad && op == 'Z' && count == 2) {
            bad = number(t[1], &stub_delay_ms);
        } else if (!bad && op == 'H' && count == 2 && !mode) {
            bad = decode(t[1], &fallback) || bind_loopback(SOCK_STREAM, 1); if (!bad) mode = 1;
        } else if (!bad && (op == 'T' || op == 'U') && count == 1 && !mode) {
            bad = bind_loopback(op == 'T' ? SOCK_STREAM : SOCK_DGRAM, 1); if (!bad) mode = op == 'T' ? 2 : 3;
        } else if (!bad && op == 'A' && count == 4 && mode == 1) {
            struct rule r = {0}; r.method = decode_string(t[1]); r.target = decode_string(t[2]);
            bad = !r.method || !r.target || decode(t[3], &r.reply);
            if (!bad) { rules = resize(rules, (rule_count+1)*sizeof *rules); rules[rule_count++] = r; }
            else { free(r.method); free(r.target); release(&r.reply); }
        } else if (!bad && op == 'B' && count == 3 && (mode == 2 || mode == 3)) {
            struct rule r = {0}; bad = decode(t[1], &r.prefix) || decode(t[2], &r.reply);
            if (!bad) { rules = resize(rules, (rule_count+1)*sizeof *rules); rules[rule_count++] = r; }
            else { release(&r.prefix); release(&r.reply); }
        } else if (!bad && op == 'D' && count >= 3 && !mode) {
            char **args = parse_args(t, count, 1, 2, 3, 0);
            bad = !args || bind_loopback(SOCK_STREAM, 0);
            if (!bad) { mode = 4; bad = spawn(&daemon_proc, args); close_fd(&daemon_proc.input); }
            free_args(args);
        } else if (!bad && op == 'R' && count >= 5 && mode) {
            uint64_t timeout; char **args = parse_args(t, count, 2, 3, 4, 1); struct buffer input = {0};
            bad = !args || number(t[1], &timeout) || decode(t[count-1], &input);
            if (!bad) status = run_client(args, &input, timeout, &out, &err, &timed, &cs);
            free_args(args); release(&input);
        } else if (!bad && (op == 'C' || op == 'J' || op == 'G') && count == 3 && mode) {
            uint64_t timeout; struct buffer input = {0}; bad = number(t[1], &timeout) || decode(t[2], &input);
            if (!bad) probe(op, timeout, &input, &wire, &timed, &cs);
            release(&input);
        } else if (!bad && op == 'P' && count == 2 && mode) {
            uint64_t timeout; bad = number(t[1], &timeout); if (!bad) wait_ready(timeout, &timed, &cs);
        } else if (!bad && op == 'S' && count == 2 && mode) {
            uint64_t timeout; bad = number(t[1], &timeout); int64_t start = millis();
            if (!bad) while (!interrupted && (uint64_t)(millis()-start) < timeout) {
                uint64_t remain = timeout-(uint64_t)(millis()-start);
                pump_wait(remain < 10 ? (int)remain : 10, NULL, -1, 0, &cs);
            }
        } else if (!bad && op == 'N' && count == 1 && mode) {
            pump_wait(0, NULL, -1, 0, &cs);
        } else bad = 1;
        pump_daemon(); append(&out, daemon_out.data, daemon_out.size); append(&err, daemon_err.data, daemon_err.size);
        release(&daemon_out); release(&daemon_err);
        if (status < 0) status = daemon_status;
        daemon_status = -1;
        if (bad) { puts("ERR network operation rejected"); fflush(stdout); failed = 1; }
        else reply(&out, &err, &wire, status, timed, &cs);
        release(&out); release(&err); release(&wire); free_captures(&cs); free(t); free(line);
        if (bad || quitting || interrupted) break;
    }
    finish_process(&daemon_proc); cleanup(); daemon_proc.pid = -1;
    clear_connections(); close_fd(&listener); release(&pending); release(&fallback); release(&daemon_out); release(&daemon_err);
    close_fd(&daemon_proc.output); close_fd(&daemon_proc.error);
    for (size_t i = 0; i < env_count; ++i) free(child_env[i]);
    free(child_env);
    for (size_t i = 0; i < rule_count; ++i) { free(rules[i].method); free(rules[i].target); release(&rules[i].prefix); release(&rules[i].reply); }
    free(rules); return failed ? 1 : 0;
}
