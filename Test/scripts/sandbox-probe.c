#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/statvfs.h>
#include <sys/wait.h>
#include <unistd.h>

static void require(int ok,const char *name) {
    if (!ok) { perror(name); exit(2); }
}
static void read_marker(const char *path,char expected) {
    char data=0;
    int fd=open(path,O_RDONLY);
    require(fd>=0 && read(fd,&data,1)==1 && data==expected,path);
    close(fd);
}
static void absent(const char *path) {
    struct stat st;
    require(stat(path,&st)<0 && errno==ENOENT,path);
}
static void normal(const char *sentinel) {
    require(geteuid()==65534 && getegid()==65534 && getgroups(0,NULL)==0,"sandbox credentials");
    require(prctl(PR_GET_NO_NEW_PRIVS,0,0,0,0)==1,"no_new_privs");
    require(prctl(PR_CAPBSET_READ,21,0,0,0)==0,"bounding set");
    require(getpid()==2,"PID namespace");
    absent(sentinel); absent("/fixtures/host-marker"); absent("/.oldroot");
    absent("/proc/self/root"); absent("/root/.codex/config.toml");
    char up[2048];
    require(snprintf(up,sizeof(up),"../../..%s",sentinel)<(int)sizeof(up),"sentinel");
    absent(up);
    require(prctl(PR_CAPBSET_READ,0)==0,"capability set");
    require(chroot("/work")<0 && errno==EPERM,"chroot policy");
    require(syscall(SYS_mount,NULL,NULL,NULL,0,NULL)<0 && errno==EPERM,"mount policy");
    require(syscall(SYS_pivot_root,NULL,NULL)<0 && errno==EPERM,"pivot_root policy");
    read_marker("/fixtures/immutable",'I'); read_marker("seed",'S'); read_marker("/base-marker",'B');
    struct statvfs v;
    require(!statvfs("/fixtures",&v) && (v.f_flag & ST_RDONLY),"fixtures read-only");
    require(!statvfs("/program",&v) && (v.f_flag & ST_RDONLY),"executable read-only");
    require(!statvfs("/work",&v) && v.f_blocks*v.f_frsize<=128UL*1024*1024,"bounded tmpfs");
    require(open("/fixtures/immutable",O_RDWR)<0 && errno==EROFS,"immutable open");
    require(unlink("/fixtures/immutable")<0 && errno==EROFS,"immutable unlink");
    require(chmod("/fixtures/immutable",0777)<0 && errno==EROFS,"immutable chmod");
    require(open("/program",O_RDWR)<0 && (errno==EROFS || errno==ETXTBSY || errno==EACCES),"executable protection");
    require(unlink("/program")<0 && (errno==EROFS || errno==EBUSY || errno==EACCES),"cannot unlink mounted executable");
    require(chmod("/program",0777)<0 && (errno==EROFS || errno==EPERM),"cannot change executable mode");
    int fd=open("new",O_CREAT|O_EXCL|O_WRONLY,0600);
    require(fd>=0 && write(fd,"X",1)==1,"work result"); close(fd);
    require(!symlink("/outside", "link-out"),"snapshot symlink");
    int rng=open("/dev/urandom",O_RDONLY); char random_byte;
    require(rng>=0 && read(rng,&random_byte,1)==1,"kernel random source"); close(rng);
    require(open("/dev/urandom",O_WRONLY)<0 && (errno==EACCES || errno==EROFS),"read-only device");
    int master=posix_openpt(O_RDWR|O_NOCTTY|O_CLOEXEC);
    require(master>=0 && !grantpt(master) && !unlockpt(master),"private pty master");
    char *pts=ptsname(master);
    int slave=pts ? open(pts,O_RDWR|O_NOCTTY|O_CLOEXEC) : -1;
    require(slave>=0 && isatty(slave),"private pty slave");
    close(slave); close(master);
    require(getenv("LOJITA_PRIVATE_MARKER")==NULL,"environment not inherited");
    puts("isolated");
}
static void limits(void) {
    struct rlimit r;
    require(!getrlimit(RLIMIT_AS,&r) && r.rlim_max==256UL*1024*1024,"address limit");
    require(mmap(NULL,r.rlim_max+1,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0)==MAP_FAILED && errno==ENOMEM,"bounded memory");
    require(!getrlimit(RLIMIT_FSIZE,&r),"file size limit");
    int fd=open("limited",O_CREAT|O_RDWR,0600); require(fd>=0,"limited open");
    signal(SIGXFSZ,SIG_IGN);
    require(ftruncate(fd,r.rlim_max+1)<0 && errno==EFBIG,"bounded file");
    close(fd);
    require(!getrlimit(RLIMIT_NOFILE,&r) && r.rlim_max==64,"descriptor limit");
    require(!getrlimit(RLIMIT_CORE,&r) && r.rlim_max==0,"core limit");
    require(!getrlimit(RLIMIT_CPU,&r) && r.rlim_max<10,"cpu limit");
    require(!getrlimit(RLIMIT_NPROC,&r) && r.rlim_max==16,"process limit");
    r.rlim_cur=1; require(!setrlimit(RLIMIT_NPROC,&r),"lower process soft limit");
    require(fork()<0 && errno==EAGAIN,"bounded process creation");
    puts("limited");
}
static void orphan(const char *marker) {
    int ack[2]; require(!pipe(ack),"ack");
    pid_t child=fork(); require(child>=0,"child");
    if (child==0) {
        close(ack[0]); require(setsid()>=0,"new session");
        pid_t grandchild=fork(); require(grandchild>=0,"grandchild");
        if (!grandchild) {
            require(!prctl(PR_SET_NAME,marker),"marker");
            require(write(ack[1],"1",1)==1,"grandchild ready"); close(ack[1]);
            sleep(1); _exit(0);
        }
        _exit(0);
    }
    close(ack[1]); char c;
    require(read(ack[0],&c,1)==1 && c=='1',"read marker"); close(ack[0]);
    require(waitpid(child,NULL,0)==child,"reap parent");
    puts("descendant registered");
}
int main(int argc,char **argv) {
    require(argc>=2,"mode");
    if (!strcmp(argv[1],"normal") && argc==3) normal(argv[2]);
    else if (!strcmp(argv[1],"limits")) limits();
    else if (!strcmp(argv[1],"orphan") && argc==3) orphan(argv[2]);
    else if (!strcmp(argv[1],"cas")) {
        unsigned char bytes[128]; ssize_t n;
        int fd=open("saved",O_WRONLY|O_CREAT|O_TRUNC,0600); require(fd>=0,"saved");
        while ((n=read(0,bytes,sizeof(bytes)))>0) {
            require(write(fd,bytes,n)==n && write(1,bytes,n)==n,"cas echo");
        }
        require(n==0 && !close(fd),"cas input");
        require(write(2,"abcdef",6)==6,"cas stderr"); return 125;
    }
    else if (!strcmp(argv[1],"abort") && argc==3) {
        require(!prctl(PR_SET_NAME,argv[2]),"child tag");
        require(write(1,"R",1)==1,"ready"); pause();
    }
    else if (!strcmp(argv[1],"wait")) pause();
    else return 3;
    return 0;
}
