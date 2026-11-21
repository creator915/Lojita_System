#ifndef AGDA_DUMPD_SOCKET_H
#define AGDA_DUMPD_SOCKET_H
#include <errno.h>
#include <stddef.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>

/* GHC's base/unix packages expose handles, but not sockaddr_un. */
static inline int dump_unix_socket(const char *path, int server) {
    struct sockaddr_un addr = {0};
    size_t n = strlen(path);
    if (!n || n >= sizeof(addr.sun_path)) { errno = ENAMETOOLONG; return -1; }
    addr.sun_family = AF_UNIX;
    memcpy(addr.sun_path, path, n + 1);
    socklen_t size = offsetof(struct sockaddr_un, sun_path) + n + 1;
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    if (server) {
        mode_t mask = umask(0077);
        int rc = bind(fd, (struct sockaddr *)&addr, size);
        umask(mask);
        if (rc == 0) {
            if (listen(fd, 16) == 0) return fd;
            int cause = errno;
            unlink(path);
            errno = cause;
        }
    } else if (connect(fd, (struct sockaddr *)&addr, size) == 0) {
        return fd;
    }
    int cause = errno;
    close(fd);
    errno = cause;
    return -1;
}

static inline int dump_unix_accept(int fd) {
    return accept(fd, NULL, NULL);
}
#endif
