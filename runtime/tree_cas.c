/* Linux filesystem operations for the LJT1 codec. Child names are byte strings;
   only trusted host paths cross this boundary as Lean strings. */
#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#include <lean/lean.h>
#include <openssl/sha.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/random.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

typedef lean_object Obj;
#define DIR_FLAGS (O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC)
#define READ_FLAGS (O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK)
#define OK(x) lean_io_result_mk_ok(x)
static Obj *unit(void) { return OK(lean_box(0)); }
static Obj *error(const char *where) {
    char msg[320];
    snprintf(msg, sizeof msg, "TreeCAS %s: %s", where, strerror(errno));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}
static Obj *invalid(const char *where) { errno = EINVAL; return error(where); }
static Obj *bytes(const void *p, size_t n) {
    Obj *b = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(b), p, n);
    return b;
}
static int component(Obj *b, char name[256]) {
    size_t n = lean_sarray_size(b);
    const uint8_t *p = lean_sarray_cptr(b);
    if (!n || n > 255 || memchr(p, 0, n) || memchr(p, '/', n) ||
        (n == 1 && p[0] == '.') || (n == 2 && !memcmp(p, "..", 2))) {
        errno = EINVAL; return -1;
    }
    memcpy(name, p, n); name[n] = 0; return 0;
}
static int random_name(char out[64]) {
    uint8_t buf[16]; size_t got = 0;
    while (got < sizeof buf) {
        ssize_t n = getrandom(buf + got, sizeof buf - got, 0);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        got += (size_t)n;
    }
    memcpy(out, ".lojita-", 8);
    for (size_t i = 0; i < sizeof buf; i++) snprintf(out + 8 + i*2, 3, "%02x", buf[i]);
    return 0;
}
static int dir_at(int parent, const char *name, int create) {
    if (create) {
        if (!mkdirat(parent,name,0755)) { if (fsync(parent)) return -1; }
        else if (errno != EEXIST) return -1;
    }
    return openat(parent, name, DIR_FLAGS);
}
static int outside_capture(int store, int source);
static Obj *open_path(Obj *path, int create, int source) {
    const char *s = lean_string_cstr(path);
    if (!*s || strlen(s) + 1 != lean_string_size(path)) return invalid("host path");
    char *copy = strdup(s);
    if (!copy) return error("allocating path");
    int fd = open(*s == '/' ? "/" : ".", DIR_FLAGS);
    char *tok, *save = NULL;
    for (tok = strtok_r(copy, "/", &save); fd >= 0 && tok; tok = strtok_r(NULL, "/", &save)) {
        if (!strcmp(tok, ".")) continue;
        int next = dir_at(fd,tok,0);
        if (next < 0 && errno == ENOENT && create && strcmp(tok,"..")) {
            if (source >= 0 && outside_capture(fd,source)) { int e = errno; close(fd); fd = -1; errno = e; break; }
            next = dir_at(fd,tok,1);
        }
        int e = errno; close(fd); errno = e; fd = next;
    }
    free(copy);
    if (fd >= 0 && source >= 0 && outside_capture(fd,source)) {
        int e = errno; close(fd); fd = -1; errno = e;
    }
    return fd < 0 ? error("opening directory") : OK(lean_box_uint32((uint32_t)fd));
}
LEAN_EXPORT Obj *ljt_open(Obj *path, uint8_t create) { return open_path(path,create,-1); }
LEAN_EXPORT Obj *ljt_capture_store(Obj *path, uint32_t source) { return open_path(path,1,(int)source); }
/* Complete a capture/save transaction after every object and kind directory
   has been synced. One barrier persists all new names in the store root. */
LEAN_EXPORT Obj *ljt_sync_store(uint32_t fd) {
    return fsync(fd) ? error("syncing store root") : unit();
}
LEAN_EXPORT Obj *ljt_close(uint32_t fd) {
    return close((int)fd) ? error("closing directory") : unit();
}
static int same_inode(const struct stat *a, const struct stat *b) {
    return a->st_dev == b->st_dev && a->st_ino == b->st_ino;
}
static int unchanged(const struct stat *a, const struct stat *b) {
    return same_inode(a, b) && a->st_mode == b->st_mode && a->st_nlink == b->st_nlink &&
        a->st_size == b->st_size && a->st_mtim.tv_sec == b->st_mtim.tv_sec &&
        a->st_mtim.tv_nsec == b->st_mtim.tv_nsec && a->st_ctim.tv_sec == b->st_ctim.tv_sec &&
        a->st_ctim.tv_nsec == b->st_ctim.tv_nsec;
}
static int outside_capture(int store, int src) {
    struct stat root, here, up;
    if (fstat(src, &root)) return -1;
    int fd = openat(store,".",DIR_FLAGS);
    while (fd >= 0) {
        if (fstat(fd,&here)) break;
        if (same_inode(&here,&root)) { close(fd); errno = EINVAL; return -1; }
        int parent = openat(fd,"..",DIR_FLAGS);
        if (parent < 0) break;
        int rc = fstat(parent,&up); int e = errno; close(fd); fd = parent; errno = e;
        if (rc) break;
        if (same_inode(&here,&up)) { close(fd); return 0; }
    }
    int e = errno; if (fd >= 0) close(fd); errno = e;
    return -1;
}
LEAN_EXPORT Obj *ljt_names(uint32_t fd) {
    int copy = openat(fd, ".", DIR_FLAGS);
    if (copy < 0) return error("opening directory stream");
    DIR *dir = fdopendir(copy);
    if (!dir) { int e = errno; close(copy); errno = e; return error("directory stream"); }
    Obj *names = lean_mk_empty_array();
    struct dirent *ent;
    errno = 0;
    while ((ent = readdir(dir))) {
        if (strcmp(ent->d_name,".") && strcmp(ent->d_name,".."))
            names = lean_array_push(names,bytes(ent->d_name,strlen(ent->d_name)));
        errno = 0;
    }
    int e = errno;
    closedir(dir);
    if (e) { lean_dec(names); errno = e; return error("reading directory stream"); }
    return OK(names);
}
/* Three public bytes (kind, mode high, mode low) followed by a private capture
   stamp. memcpy avoids any alignment/word-size assumptions in Lean storage. */
LEAN_EXPORT Obj *ljt_stat(uint32_t parent, Obj *name) {
    struct stat st = {0}; char s[256];
    int rc;
    if (!lean_sarray_size(name)) rc = fstat(parent, &st);
    else if (component(name,s)) return invalid("path component");
    else rc = fstatat(parent,s,&st,AT_SYMLINK_NOFOLLOW);
    if (rc) return error("stat");
    char kind = S_ISDIR(st.st_mode) ? 't' : S_ISLNK(st.st_mode) ? 's' : S_ISREG(st.st_mode) ? 'b' : 0;
    if (!kind || (st.st_mode & 07000) || (kind != 't' && st.st_nlink != 1))
        return invalid("unsupported node, permissions or hard link");
    Obj *b = lean_alloc_sarray(1,3 + sizeof st,3 + sizeof st);
    uint8_t *p = lean_sarray_cptr(b);
    p[0] = kind; p[1] = (st.st_mode & 0777) >> 8; p[2] = st.st_mode & 255;
    memcpy(p+3,&st,sizeof st);
    return OK(b);
}
static int checked(const struct stat *actual, Obj *stamp) {
    struct stat expected;
    if (lean_sarray_size(stamp) != 3 + sizeof expected) { errno = EINVAL; return -1; }
    memcpy(&expected,lean_sarray_cptr(stamp)+3,sizeof expected);
    if (!unchanged(actual,&expected)) { errno = ESTALE; return -1; }
    return 0;
}
static int checkfd(int fd, Obj *stamp) {
    struct stat st;
    return fstat(fd,&st) || checked(&st,stamp) ? -1 : 0;
}
LEAN_EXPORT Obj *ljt_check(uint32_t fd, Obj *stamp) {
    return checkfd(fd,stamp) ? error("source changed during capture") : unit();
}
LEAN_EXPORT Obj *ljt_child(uint32_t parent, Obj *name, uint8_t create) {
    char s[256];
    if (component(name,s)) return invalid("path component");
    if (create && mkdirat(parent,s,0700)) return error("creating directory");
    int fd = openat(parent,s,DIR_FLAGS);
    return fd < 0 ? error("opening child directory") : OK(lean_box_uint32((uint32_t)fd));
}
/* off_t is 64 bits even on ILP32; leave room for the Lean object header
   and allocator alignment before converting a file length to size_t. */
static int file_length(off_t length, size_t *size) {
    if (length < 0 || (uintmax_t)length > SIZE_MAX - sizeof(lean_sarray_object) - 16) {
        errno = EFBIG; return -1;
    }
    *size = (size_t)length; return 0;
}
static Obj *read_file(int fd) {
    struct stat st, after;
    if (fstat(fd,&st)) return NULL;
    if (!S_ISREG(st.st_mode)) { errno = EINVAL; return NULL; }
    size_t size;
    if (file_length(st.st_size,&size)) return NULL;
    Obj *b = lean_alloc_sarray(1,size,size);
    for (size_t pos = 0; pos < size;) {
        size_t count = size - pos;
        if (count > 1024*1024) count = 1024*1024;
        ssize_t n = read(fd,lean_sarray_cptr(b) + pos,count);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { if (!n) errno = ESTALE; goto fail; }
        pos += (size_t)n;
    }
    if (fstat(fd,&after)) goto fail;
    if (!unchanged(&st,&after)) { errno = ESTALE; goto fail; }
    return b;
fail:
    lean_dec(b); return NULL;
}
LEAN_EXPORT Obj *ljt_source_bytes(uint32_t parent, Obj *name, Obj *stamp) {
    char s[256];
    if (component(name,s) || lean_sarray_size(stamp) != 3 + sizeof(struct stat))
        return invalid("capture entry");
    if (lean_sarray_cptr(stamp)[0] == 's') {
        char buf[4096]; struct stat st;
        ssize_t n = readlinkat(parent,s,buf,sizeof buf);
        if (n <= 0 || n == sizeof buf) return invalid("invalid symlink target");
        if (fstatat(parent,s,&st,AT_SYMLINK_NOFOLLOW) || checked(&st,stamp))
            return error("symlink changed during capture");
        return OK(bytes(buf,(size_t)n));
    }
    int fd = openat(parent,s,READ_FLAGS);
    if (fd < 0) return error("opening source file");
    Obj *b = checkfd(fd,stamp) ? NULL : read_file(fd);
    if (b && checkfd(fd,stamp)) { lean_dec(b); b = NULL; }
    int e = errno; close(fd); errno = e;
    return b ? OK(b) : error("reading stable source file");
}
static int write_all(int fd, Obj *b) {
    size_t pos = 0, size = lean_sarray_size(b);
    while (pos < size) {
        size_t count = size-pos;
        if (count > 1024*1024) count = 1024*1024;
        ssize_t n = write(fd,lean_sarray_cptr(b)+pos,count);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { if (!n) errno = EIO; return -1; }
        pos += (size_t)n;
    }
    return 0;
}
static int object_dir(int store, uint8_t kind, int create) {
    const char *folder = kind == 'b' ? "blob" : kind == 't' ? "tree" : kind == 's' ? "symlink" : NULL;
    if (!folder) { errno = EINVAL; return -1; }
    return dir_at(store,folder,create);
}
static void hex(const uint8_t id[32], char name[65]) {
    static const char digits[] = "0123456789abcdef";
    for (size_t i = 0; i < 32; ++i) {
        name[i*2] = digits[id[i] >> 4]; name[i*2+1] = digits[id[i] & 15];
    }
    name[64] = 0;
}
static Obj *load_object(int dir, const char *name, const uint8_t expected[32]) {
    int fd = openat(dir,name,READ_FLAGS);
    if (fd < 0) return NULL;
    Obj *b = read_file(fd);
    int e = errno; close(fd); errno = e;
    if (b) {
        uint8_t digest[32];
        if (!SHA256(lean_sarray_cptr(b),lean_sarray_size(b),digest) || memcmp(expected,digest,32)) {
            lean_dec(b); errno = EBADMSG; return NULL;
        }
    }
    return b;
}
LEAN_EXPORT Obj *ljt_get(uint32_t store, uint8_t kind, Obj *id) {
    if (lean_sarray_size(id) != 32) return invalid("invalid digest");
    int dir = object_dir(store,kind,0);
    if (dir < 0) return error("opening object directory");
    char name[65]; hex(lean_sarray_cptr(id),name);
    Obj *data = load_object(dir,name,lean_sarray_cptr(id));
    int e = errno; close(dir); errno = e;
    return data ? OK(data) : error(errno == EBADMSG ? "CAS_HASH_MISMATCH" : "reading object");
}
/* Large objects overlap SHA-256 with the stable write. The worker only
   borrows immutable bytes until pthread_join; all Lean allocation stays on the
   caller's thread. Small, existing objects avoid a temporary write. */
struct hash_job { const uint8_t *data; size_t size; uint8_t id[32]; int ok; };
static void *hash_bytes(void *ptr) {
    struct hash_job *job = ptr;
    job->ok = SHA256(job->data,job->size,job->id) != NULL;
    return NULL;
}
static int verify_prior(int dir, const char *name, const uint8_t id[32]) {
    Obj *prior = load_object(dir,name,id);
    if (!prior) return -1;
    lean_dec(prior); return 0;
}
LEAN_EXPORT Obj *ljt_put(uint32_t store, uint8_t kind, Obj *data) {
    struct hash_job job = {.data = lean_sarray_cptr(data), .size = lean_sarray_size(data)};
    char name[65], tmp[64];
    const char *folder = kind == 'b' ? "blob" : kind == 't' ? "tree" : kind == 's' ? "symlink" : NULL;
    if (!folder) return invalid("object kind");
    int fresh = !mkdirat(store,folder,0755);
    if (!fresh && errno != EEXIST) return error("creating object directory");
    int dir = object_dir(store,kind,0);
    if (dir < 0) return error("opening object directory");
    pthread_t worker;
    int running = job.size >= 1024*1024 && !pthread_create(&worker,NULL,hash_bytes,&job);
    int rc = 0, published = 0;
    if (!running) {
        hash_bytes(&job);
        if (!job.ok) { errno = EIO; rc = -1; goto finish; }
        hex(job.id,name);
        if (!fresh) {
            if (!verify_prior(dir,name,job.id)) goto finish;
            if (errno != ENOENT) { rc = -1; goto finish; }
        }
    }
    if (random_name(tmp)) { rc = -1; goto finish; }
    int fd = openat(dir,tmp,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);
    if (fd < 0) { rc = -1; goto finish; }
    rc = write_all(fd,data) || fchmod(fd,0444) || fsync(fd) ? -1 : 0;
    int e = errno;
    if (close(fd) && !rc) rc = -1; else errno = e;
    if (running) {
        pthread_join(worker,NULL); running = 0;
        if (!job.ok) { errno = EIO; rc = -1; }
        hex(job.id,name);
    }
    if (!rc && !syscall(SYS_renameat2,dir,tmp,dir,name,RENAME_NOREPLACE)) {
        published = 1;
        rc = fsync(dir);
    } else {
        if (!rc) rc = errno == EEXIST ? verify_prior(dir,name,job.id) : -1;
        e = errno;
        if (unlinkat(dir,tmp,0) && !rc) rc = -1; else errno = e;
    }
finish:
    e = errno;
    if (running) pthread_join(worker,NULL);
    /* With a full or read-only filesystem, a pre-existing correct object can
       still satisfy the request even if a speculative large write failed. */
    if (rc && !published && !fresh && job.ok && e != EBADMSG) {
        hex(job.id,name);
        if (!verify_prior(dir,name,job.id)) rc = 0;
    }
    close(dir); errno = e;
    return rc ? error(errno == EBADMSG ? "CAS_HASH_MISMATCH" : "publishing object") : OK(bytes(job.id,32));
}
LEAN_EXPORT Obj *ljt_emit(uint32_t dir, Obj *name, uint8_t kind, uint32_t mode, Obj *data) {
    char s[256];
    if (component(name,s) || mode > 0777) return invalid("materialized entry");
    if (kind == 's') {
        char target[4096]; size_t n = lean_sarray_size(data);
        if (mode != 0777 || !n || n >= sizeof target || memchr(lean_sarray_cptr(data),0,n))
            return invalid("symlink target");
        memcpy(target,lean_sarray_cptr(data),n); target[n] = 0;
        return symlinkat(target,dir,s) ? error("creating symlink") : unit();
    }
    if (kind != 'b') return invalid("file kind");
    int fd = openat(dir,s,O_WRONLY|O_EXCL|O_NOFOLLOW|O_CLOEXEC|O_CREAT,0600);
    if (fd < 0) return error("creating regular file");
    int rc = write_all(fd,data) || fchmod(fd,mode);
    int e = errno;
    if (close(fd) && !rc) rc = -1; else errno = e;
    return rc ? error("writing file") : unit();
}
LEAN_EXPORT Obj *ljt_mode(uint32_t dir, uint32_t mode) {
    return mode > 0777 ? invalid("directory mode") :
        fchmod(dir,mode) ? error("setting directory mode") : unit();
}
LEAN_EXPORT Obj *ljt_stage(uint32_t parent) {
    char s[64];
    if (random_name(s) || mkdirat(parent,s,0700)) return error("creating private stage");
    return OK(bytes(s,strlen(s)));
}
LEAN_EXPORT Obj *ljt_publish(uint32_t parent, Obj *stage, Obj *target) {
    char a[256], b[256];
    if (component(stage,a) || component(target,b)) return invalid("destination component");
    return syscall(SYS_renameat2,parent,a,parent,b,RENAME_NOREPLACE) ? error("publishing destination") : unit();
}
static int remove_entry(int parent, const char *name) {
    /* An O_PATH handle pins a directory even when its archived mode was 000.
       fchmod through /proc/self/fd never follows a symlink from the staged tree. */
    int pin = openat(parent,name,O_PATH|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    if (pin < 0) {
        if (errno == ENOENT) return 0;
        if (errno == ENOTDIR || errno == ELOOP) return unlinkat(parent,name,0);
        return -1;
    }
    char path[64]; snprintf(path,sizeof path,"/proc/self/fd/%d",pin);
    int fd = chmod(path,0700) ? -1 : openat(pin,".",DIR_FLAGS);
    int e = errno; close(pin); errno = e;
    if (fd < 0) return -1;
    DIR *dir = fdopendir(fd);
    if (!dir) { e = errno; close(fd); errno = e; return -1; }
    for (;;) {
        errno = 0; struct dirent *entry = readdir(dir);
        if (!entry) break;
        if (!strcmp(entry->d_name,".") || !strcmp(entry->d_name,"..")) continue;
        if (remove_entry(fd,entry->d_name)) break;
    }
    e = errno; closedir(dir); errno = e;
    return e ? -1 : unlinkat(parent,name,AT_REMOVEDIR);
}
LEAN_EXPORT Obj *ljt_remove(uint32_t parent, Obj *name) {
    char s[256];
    if (component(name,s)) return invalid("cleanup component");
    return remove_entry(parent,s) ? error("removing private stage") : unit();
}
