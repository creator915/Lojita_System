#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <linux/audit.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/mount.h>
#include <linux/landlock.h>
#include <linux/seccomp.h>
#include <net/if.h>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/sendfile.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/sysmacros.h>
#include <sys/wait.h>
#include <unistd.h>

/* The close-on-exec channel distinguishes setup failure from payload exit 125. */
static int setup_error=-1;
static void fail(const char *what) { perror(what); if (setup_error>=0) (void)!write(setup_error,"!",1); _exit(125); }
static long checked(long v, const char *what) { if (v < 0) fail(what); return v; }
static int dirfd_at(int dir, const char *name) {
    return checked(openat(dir, name, O_RDONLY|O_NOFOLLOW|O_CLOEXEC|O_DIRECTORY), name);
}
static void mk(int dir, const char *name, unsigned mode) {
    checked(mkdirat(dir, name, mode), name);
}
static void placeholder(int dir, const char *name) {
    checked(close(checked(openat(dir,name,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC,0600),name)), "close");
}
static DIR *entries(int dir) {
    DIR *d = fdopendir(dirfd_at(dir, "."));
    if (!d) fail("fdopendir");
    return d;
}
static const char *next(DIR *d) {
    for (;;) {
        errno = 0;
        struct dirent *e = readdir(d);
        if (!e) { if (errno) fail("readdir"); return NULL; }
        if (strcmp(e->d_name,".") && strcmp(e->d_name,"..")) return e->d_name;
    }
}
static void link_copy(int src, int dst, const char *name) {
    char b[PATH_MAX + 1];
    ssize_t n = checked(readlinkat(src,name,b,sizeof(b)-1),name);
    if (n == PATH_MAX) { errno=ENAMETOOLONG; fail(name); }
    b[n]=0;
    checked(symlinkat(b,dst,name),name);
}
struct budget { size_t entries, bytes; };
/* Inputs are private staging trees; export occurs only after PID-namespace teardown. */
static void copy_tree(int src, int dst, struct budget *budget, int depth, int seed) {
    if (depth >= 64) { errno=ELOOP; fail("snapshot depth"); }
    DIR *d=entries(src);
    const char *name;
    while ((name=next(d))) {
        if (!budget->entries--) { errno=E2BIG; fail("snapshot entries"); }
        struct stat st;
        checked(fstatat(src,name,&st,AT_SYMLINK_NOFOLLOW),name);
        if (S_ISLNK(st.st_mode)) { link_copy(src,dst,name); continue; }
        if (S_ISDIR(st.st_mode)) {
            mk(dst,name,0700);
            int a=dirfd_at(src,name), b=dirfd_at(dst,name);
            copy_tree(a,b,budget,depth+1,seed);
            if (seed) checked(fchown(b,65534,65534),"chown work directory");
            checked(fchmod(b,st.st_mode & 0777),"chmod directory");
            close(a); close(b);
        } else if (S_ISREG(st.st_mode)) {
            if ((size_t)st.st_size>budget->bytes) { errno=EFBIG; fail("snapshot bytes"); }
            budget->bytes-=(size_t)st.st_size;
            int in=checked(openat(src,name,O_RDONLY|O_NOFOLLOW|O_CLOEXEC|O_NONBLOCK),name);
            int out=checked(openat(dst,name,O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC,0600),name);
            off_t pos=0;
            while (pos<st.st_size) {
                ssize_t n=sendfile(out,in,&pos,st.st_size-pos);
                if (n<0 && errno==EINTR) continue;
                if (n<=0) fail("snapshot short copy");
            }
            if (seed) checked(fchown(out,65534,65534),"chown work file");
            checked(fchmod(out,st.st_mode & 0777),"chmod file");
            close(in); checked(close(out),"close file");
        } else { errno=EINVAL; fail("snapshot unsupported node"); }
    }
    closedir(d);
}
/* Nonrecursive bind clone: no host submount follows a supplied root. */
static void bind_ro(int src, const char *entry, int root, const char *dest, unsigned extra) {
    unsigned flags = OPEN_TREE_CLONE|OPEN_TREE_CLOEXEC|AT_SYMLINK_NOFOLLOW;
    int mountfd = checked(syscall(SYS_open_tree,src,entry,flags|(*entry ? 0 : AT_EMPTY_PATH)),"open_tree");
    struct mount_attr attr={.attr_set=MOUNT_ATTR_RDONLY|MOUNT_ATTR_NOSUID|extra};
    checked(syscall(SYS_mount_setattr,mountfd,"",AT_EMPTY_PATH,&attr,sizeof(attr)),"mount_setattr");
    checked(syscall(SYS_move_mount,mountfd,"",root,dest,MOVE_MOUNT_F_EMPTY_PATH),"move_mount");
    close(mountfd);
}
static void install_base(int base, int root) {
    const char *reserved[]={"work","fixtures","program",".oldroot","dev","proc","sys","tmp",NULL};
    DIR *d=entries(base);
    const char *name;
    while ((name=next(d))) {
        size_t i=0;
        while (reserved[i] && strcmp(name,reserved[i])) ++i;
        if (reserved[i]) continue;
        struct stat st;
        checked(fstatat(base,name,&st,AT_SYMLINK_NOFOLLOW),"base entry");
        if (S_ISLNK(st.st_mode)) { link_copy(base,root,name); continue; }
        if (S_ISDIR(st.st_mode)) mk(root,name,0755);
        else if (S_ISREG(st.st_mode)) placeholder(root,name);
        else { errno=EINVAL; fail("base contains special node"); }
        bind_ro(base,name,root,name,MOUNT_ATTR_NODEV);
    }
    closedir(d);
}
static void write_map(const char *name, const char *s) {
    int fd=checked(open(name,O_WRONLY|O_CLOEXEC),name);
    if (checked(write(fd,s,strlen(s)),name)!=(long)strlen(s)) fail("short ID mapping");
    checked(close(fd),name);
}
static int user_mapped;
static void isolate(void) {
    struct __user_cap_header_struct h={.version=_LINUX_CAPABILITY_VERSION_3};
    struct __user_cap_data_struct c[2]={0};
    checked(syscall(SYS_capget,&h,c),"capget");
    if (!(c[0].effective & (1U<<CAP_SYS_ADMIN))) {
        uid_t u=geteuid(); gid_t g=getegid();
        user_mapped=1;
        checked(unshare(CLONE_NEWUSER),"unshare user namespace");
        char map[64];
        snprintf(map,sizeof(map),"65534 %u 1\n",u);
        write_map("/proc/self/uid_map",map);
        write_map("/proc/self/setgroups","deny\n");
        snprintf(map,sizeof(map),"65534 %u 1\n",g);
        write_map("/proc/self/gid_map",map);
    }
    checked(unshare(CLONE_NEWNS|CLONE_NEWPID|CLONE_NEWNET|CLONE_NEWIPC|CLONE_NEWUTS),"unshare isolation namespaces");
    checked(mount(NULL,"/",NULL,MS_PRIVATE|MS_REC,NULL),"private mounts");
    checked(sethostname("lojita",6),"sethostname");
    int fd=checked(socket(AF_INET,SOCK_DGRAM|SOCK_CLOEXEC,0),"loopback socket");
    struct ifreq ifr={.ifr_name="lo"};
    checked(ioctl(fd,SIOCGIFFLAGS,&ifr),"get loopback flags");
    ifr.ifr_flags |= IFF_UP;
    checked(ioctl(fd,SIOCSIFFLAGS,&ifr),"enable loopback");
    close(fd);
}
static void limit(int which, rlim_t n) {
    struct rlimit lim={n,n}; checked(setrlimit(which,&lim),"setrlimit");
}
#define DENY(call) BPF_JUMP(BPF_JMP|BPF_JEQ|BPF_K,SYS_##call,0,1), BPF_STMT(BPF_RET|BPF_K,SECCOMP_RET_ERRNO|EPERM)
static void demote(unsigned ms) {
    limit(RLIMIT_AS,256UL<<20); limit(RLIMIT_CPU,1+(ms+999)/1000);
    limit(RLIMIT_FSIZE,32UL<<20); limit(RLIMIT_NOFILE,64); limit(RLIMIT_NPROC,16); limit(RLIMIT_CORE,0);
    for (int i=0; prctl(PR_CAPBSET_READ,i)>=0; ++i) checked(prctl(PR_CAPBSET_DROP,i),"drop bounding capability");
    /* An unprivileged gid_map requires setgroups=deny. The only mapped group is the caller,
       PID/mount isolation and readonly inputs also apply on this path. */
    if (!user_mapped) checked(setgroups(0,NULL),"clear supplementary groups");
    checked(setresgid(65534,65534,65534),"drop gid");
    checked(setresuid(65534,65534,65534),"drop uid");
    struct __user_cap_header_struct h={.version=_LINUX_CAPABILITY_VERSION_3};
    struct __user_cap_data_struct c[2]={0};
    checked(syscall(SYS_capset,&h,c),"clear capabilities");
    checked(prctl(PR_SET_NO_NEW_PRIVS,1,0,0,0),"no_new_privs");
    /* Readonly mounts do not prevent writes to character devices. Limit write opens
       to the private work tree and PTYs before executing the guest. */
    struct landlock_ruleset_attr rules={.handled_access_fs=LANDLOCK_ACCESS_FS_WRITE_FILE|LANDLOCK_ACCESS_FS_REFER};
    int policy=checked(syscall(SYS_landlock_create_ruleset,&rules,sizeof(rules),0),"Landlock ruleset");
    const char *writable[]={"/work","/dev/pts"};
    for (size_t i=0;i<2;i++) {
        struct landlock_path_beneath_attr rule={.allowed_access=rules.handled_access_fs,.parent_fd=checked(open(writable[i],O_PATH|O_DIRECTORY|O_CLOEXEC),"Landlock path")};
        checked(syscall(SYS_landlock_add_rule,policy,LANDLOCK_RULE_PATH_BENEATH,&rule,0),"Landlock write rule");
        close(rule.parent_fd);
    }
    checked(syscall(SYS_landlock_restrict_self,policy,0),"Landlock restrict"); close(policy);
    struct sock_filter code[]={
        BPF_STMT(BPF_LD|BPF_W|BPF_ABS,offsetof(struct seccomp_data,arch)),
        BPF_JUMP(BPF_JMP|BPF_JEQ|BPF_K,AUDIT_ARCH_X86_64,1,0), BPF_STMT(BPF_RET|BPF_K,SECCOMP_RET_KILL_PROCESS),
        BPF_STMT(BPF_LD|BPF_W|BPF_ABS,offsetof(struct seccomp_data,nr)),
        BPF_JUMP(BPF_JMP|BPF_JGE|BPF_K,0x40000000U,0,1), BPF_STMT(BPF_RET|BPF_K,SECCOMP_RET_KILL_PROCESS),
        DENY(mount), DENY(umount2), DENY(pivot_root), DENY(chroot), DENY(unshare), DENY(setns),
        DENY(open_tree), DENY(move_mount), DENY(fsopen), DENY(fspick), DENY(mount_setattr),
        DENY(io_uring_setup), DENY(bpf), DENY(ptrace), DENY(keyctl), DENY(perf_event_open),
        BPF_JUMP(BPF_JMP|BPF_JEQ|BPF_K,SYS_clone3,0,1), BPF_STMT(BPF_RET|BPF_K,SECCOMP_RET_ERRNO|ENOSYS),
        BPF_JUMP(BPF_JMP|BPF_JEQ|BPF_K,SYS_clone,0,3),
        BPF_STMT(BPF_LD|BPF_W|BPF_ABS,offsetof(struct seccomp_data,args[0])),
        BPF_JUMP(BPF_JMP|BPF_JSET|BPF_K,CLONE_NEWUSER|CLONE_NEWNS|CLONE_NEWPID|CLONE_NEWNET|CLONE_NEWIPC|CLONE_NEWUTS|CLONE_NEWCGROUP,0,1),
        BPF_STMT(BPF_RET|BPF_K,SECCOMP_RET_ERRNO|EPERM),
        BPF_STMT(BPF_RET|BPF_K,SECCOMP_RET_ALLOW)
    };
    struct sock_fprog prog={sizeof(code)/sizeof(code[0]),code};
    checked(prctl(PR_SET_SECCOMP,SECCOMP_MODE_FILTER,&prog),"seccomp");
}
static int status_code(int status) {
    return WIFEXITED(status) ? WEXITSTATUS(status) : 128+WTERMSIG(status);
}
static void namespace_init(char **argv,unsigned ms,int alive,int errors) {
    setup_error=errors;
    checked(prctl(PR_SET_PDEATHSIG,SIGKILL),"parent death signal");
    struct pollfd p={alive,POLLIN,0};
    if (checked(poll(&p,1,0),"parent check")) _exit(125);
    if (errors!=3) { checked(dup3(errors,3,O_CLOEXEC),"setup error channel"); setup_error=3; }
    checked(syscall(SYS_close_range,4,~0U,0),"close inherited handles");
    pid_t child=checked(fork(),"fork payload");
    if (!child) {
        demote(ms);
        char *env[]={"PATH=/bin:/usr/bin","HOME=/work","TMPDIR=/work","LANG=C.UTF-8","LC_ALL=C.UTF-8","LEAN_STACK_SIZE_KB=8192","LEAN_NUM_THREADS=1","LEAN_MAIN_USE_THREAD=0",NULL};
        execve("/program",argv,env); fail("exec sandbox program");
    }
    close(3); setup_error=-1;
    int status;
    while (checked(TEMP_FAILURE_RETRY(waitpid(-1,&status,0)),"reap") != child) {}
    _exit(status_code(status));
}
int main(int argc,char **argv) {
    if (argc<7) { fprintf(stderr,"usage: lojita-sandbox FIXTURES SEED EMPTY_OUTPUT BASE|- PROGRAM TIMEOUT_MS [ARG ...]\n"); return 125; }
    char *end;
    unsigned long ms=strtoul(argv[6],&end,10);
    if (*end || !ms || ms>600000) { errno=EINVAL; fail("timeout (1..600000 ms)"); }
    for (int i=0;i<3;i++) {
        struct stat st; checked(fstat(i,&st),"standard descriptor");
        if (!S_ISFIFO(st.st_mode) && !(S_ISCHR(st.st_mode) && st.st_rdev==makedev(1,3))) { errno=EPERM; fail("stdio requires pipes or null"); }
    }
    const char *receipt_path=getenv("LOJITA_SANDBOX_RECEIPT");
    int receipt=receipt_path ? checked(open(receipt_path,O_CREAT|O_EXCL|O_NOFOLLOW|O_WRONLY|O_CLOEXEC,0600),"create receipt") : -1;
    isolate();
    int fixtures=dirfd_at(AT_FDCWD,argv[1]),seed=dirfd_at(AT_FDCWD,argv[2]),out=dirfd_at(AT_FDCWD,argv[3]);
    DIR *out_entries=entries(out);
    if (next(out_entries)) { errno=ENOTEMPTY; fail("snapshot destination"); }
    closedir(out_entries);
    int base=strcmp(argv[4],"-") ? dirfd_at(AT_FDCWD,argv[4]) : -1;
    int exe=checked(open(argv[5],O_PATH|O_NOFOLLOW|O_CLOEXEC),"open executable");
    struct stat st; checked(fstat(exe,&st),"stat executable");
    if (!S_ISREG(st.st_mode)) { errno=EINVAL; fail("regular executable required"); }
    checked(mount("tmpfs","/tmp","tmpfs",MS_NOSUID|MS_NODEV,"size=4m,mode=0755"),"root tmpfs");
    int root=dirfd_at(AT_FDCWD,"/tmp");
    if (base>=0) { install_base(base,root); close(base); }
    mk(root,".oldroot",0700); mk(root,"work",0755); mk(root,"fixtures",0755);
    mk(root,"dev",0755);
    int dev=dirfd_at(root,"dev");
    placeholder(dev,"urandom");
    bind_ro(AT_FDCWD,"/dev/urandom",dev,"urandom",MOUNT_ATTR_NOEXEC);
    mk(dev,"pts",0755);
    checked(mount("devpts","/tmp/dev/pts","devpts",MS_NOSUID|MS_NOEXEC,
                  "newinstance,ptmxmode=0666,mode=0620"),"private devpts");
    checked(symlinkat("pts/ptmx",dev,"ptmx"),"ptmx link"); close(dev);
    placeholder(root,"program");
    /* CAS modes describe payload-owned files. Give only a private copy that identity. */
    mk(root,".inputs",0700);
    checked(mount("tmpfs","/tmp/.inputs","tmpfs",MS_NOSUID|MS_NODEV,"size=128m,nr_inodes=16384,mode=0700"),"fixture tmpfs");
    int inputs=dirfd_at(root,".inputs");
    struct budget fixtures_limit={16384,128UL<<20};
    copy_tree(fixtures,inputs,&fixtures_limit,0,1);
    checked(fstat(fixtures,&st),"fixture mode");
    checked(fchown(inputs,65534,65534),"fixture owner");
    checked(fchmod(inputs,st.st_mode & 0777),"fixture permissions");
    bind_ro(inputs,"",root,"fixtures",MOUNT_ATTR_NODEV); close(inputs);
    checked(umount2("/tmp/.inputs",MNT_DETACH),"detach fixture staging");
    checked(unlinkat(root,".inputs",AT_REMOVEDIR),"remove fixture staging");
    bind_ro(exe,"",root,"program",MOUNT_ATTR_NODEV);
    checked(symlinkat("/work",root,"tmp"),"sandbox tmp");
    checked(mount("tmpfs","/tmp/work","tmpfs",MS_NOSUID|MS_NODEV,"size=128m,nr_inodes=16384,mode=0700"),"work tmpfs");
    int work=dirfd_at(root,"work");
    struct budget seed_limit={16384,128UL<<20},out_limit=seed_limit;
    copy_tree(seed,work,&seed_limit,0,1); checked(fchown(work,65534,65534),"chown work");
    checked(fstat(seed,&st),"seed mode"); checked(fchmod(work,st.st_mode & 0777),"work permissions");
    close(fixtures); close(exe); close(seed);
    checked(fchdir(root),"new root"); close(root);
    checked(syscall(SYS_pivot_root,".",".oldroot"),"pivot_root");
    checked(chdir("/"),"chdir root"); checked(umount2("/.oldroot",MNT_DETACH),"detach old root");
    checked(rmdir("/.oldroot"),"remove old root");
    checked(mount(NULL,"/",NULL,MS_REMOUNT|MS_RDONLY|MS_NOSUID|MS_NODEV,NULL),"seal sandbox root");
    checked(fchdir(work),"chdir work");
    int alive[2]; checked(pipe2(alive,O_CLOEXEC),"parent liveness pipe");
    int errors[2]; checked(pipe2(errors,O_CLOEXEC),"setup error channel");
    pid_t init=checked(fork(),"fork namespace init");
    if (!init) { close(alive[1]); argv[6]="/program"; namespace_init(argv+6,ms,alive[0],errors[1]); }
    close(errors[1]);
    close(alive[0]);
    int pidfd=checked(syscall(SYS_pidfd_open,init,0),"pidfd_open");
    struct pollfd p={pidfd,POLLIN,0};
    int ready=checked(poll(&p,1,ms),"wait for namespace");
    if (!ready) checked(syscall(SYS_pidfd_send_signal,pidfd,SIGKILL,NULL,0),"timeout kill");
    int status; checked(waitpid(init,&status,0),"wait for PID namespace teardown");
    close(pidfd); close(alive[1]);
    char error;
    if (checked(read(errors[0],&error,1),"setup status")) { errno=EIO; fail("namespace setup"); }
    close(errors[0]);
    copy_tree(work,out,&out_limit,0,0);
    checked(fstat(work,&st),"work mode"); checked(fchmod(out,st.st_mode & 0777),"export permissions");
    int code=ready ? status_code(status) : 124;
    if (receipt>=0) {
        checked(dprintf(receipt,"%s %d\n",ready ? "exit" : "timeout",code),"write receipt");
        checked(close(receipt),"close receipt");
    }
    return code;
}
