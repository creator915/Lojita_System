#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pty.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

/* The generator supplies only these paths, small descriptors and bounded lengths. */
static const char *words[]={"a","b","c","d","d/e","d/f","s","t","d/../a","missing/leaf","./a","bin\xff",NULL,NULL,"d//e","."};
static char abs_a[80], abs_s[80];
static const char *path(int n) { return n==12 ? abs_a : n==13 ? abs_s : words[n]; }
static void num(long n) { if (n<0) printf("E%d",errno); else printf("N%ld",n); }
static void hex(const unsigned char *p,int n) { for (int i=0;i<n;i++) printf("%02x",p[i]); }
static void bytes(const unsigned char *p,long n) { if (n<0) num(n); else {putchar('B'); hex(p,n);} }
static void pair(int a,int b) { printf("P%d,%d",a,b); }
static void die(const char *s) { perror(s); exit(90); }
static void ignored(int sig) { (void)sig; }
static int flags(int x) {
    return (x&3) | ((x & 4)?O_CREAT:0) | ((x & 8)?O_EXCL:0) | ((x & 16)?O_TRUNC:0) |
           ((x & 32)?O_APPEND:0) | ((x & 64)?O_DIRECTORY:0) | ((x & 128)?O_NOFOLLOW:0);
}
static void populate(unsigned char *bs,int n,int seed) {
    for (int i=0;i<n;i++) bs[i]=seed>=256 ? ((i%7==6)?10:97+(seed+i)%26) : (seed+29*i)%256;
}
static int attrs(int fd,int canon) {
    struct termios t;
    if (tcgetattr(fd,&t)<0) return -1;
    cfmakeraw(&t);
    if (canon) t.c_lflag |= ICANON;
    return tcsetattr(fd,TCSANOW,&t);
}
static int makepty(int f[2]) {
    if (openpty(&f[0],&f[1],NULL,NULL,NULL)) return -1;
    if (attrs(f[1],0) || fcntl(f[0],F_SETFL,O_NONBLOCK) || fcntl(f[1],F_SETFL,O_NONBLOCK)) die("initialize tty");
    return 0;
}
static void interrupt_poll(void) {
    struct sigevent ev={.sigev_notify=SIGEV_SIGNAL,.sigev_signo=SIGWINCH};
    struct itimerspec when={.it_value={.tv_nsec=100000}};
    timer_t timer;
    sigset_t mask;
    sigemptyset(&mask);
    if (timer_create(CLOCK_MONOTONIC,&ev,&timer) || timer_settime(timer,0,&when,NULL)) die("timer");
    struct timespec timeout={.tv_sec=1};
    int ret=ppoll(NULL,0,&timeout,&mask), saved=errno;
    if (timer_delete(timer)) die("timer_delete");
    errno=saved; num(ret);
}
/* Independent byte reader. The first line and entire remaining stream share a chunk. */
static void line_and_all(int fd,int chunk) {
    unsigned char data[4096]; size_t used=0;
    for (;;) {
        if (used+chunk>sizeof(data)) die("bounded buffer");
        ssize_t n=read(fd,data+used,chunk);
        if (n<0 && errno==EINTR) continue;
        if (n<0) { num(n); return; }
        if (!n) break;
        used+=n;
    }
    unsigned char *lf=memchr(data,'\n',used);
    size_t first=lf ? (size_t)(lf-data)+1 : used;
    putchar('L'); if (!used) putchar('-'); else hex(data,first);
    putchar('|'); hex(data+first,used-first);
}
static int valid(int op,int a,int b,int c) {
    if (a<0 || b<0 || c<0 || a>511 || b>511 || c>511) return 0;
    switch(op) {
    case 0: return a<16 && (b&3)!=3;
    case 6: case 7: case 10: return a<16;
    case 8: case 9: return a<16 && b<16;
    case 11: case 13: case 15: case 20: return 1;
    case 21: case 22: return a>=3 && a<64 && b<=23;
    case 4: case 12: return a>=3 && a<64 && b>=3 && b<64;
    case 2: case 3: case 16: case 17: case 18: return a>=3 && a<64 && b<=128;
    case 1: case 14: return a>=3 && a<64;
    case 5: return a>=3 && a<64 && c<3;
    case 19: return a>=3 && a<64 && b>=1 && b<=128;
    default: return 0;
    }
}
static void operation(int op,int a,int b,int c) {
    unsigned char buf[256]; int f[2];
    switch(op) {
    case 0: num(openat(AT_FDCWD,path(a),flags(b),c)); break;
    case 1: num(close(a)); break;
    case 2: bytes(buf,read(a,buf,b)); break;
    case 3: populate(buf,b,c); num(write(a,buf,b)); break;
    case 4: num(dup2(a,b)); break;
    case 5: num(lseek(a,b-8,c)); break;
    case 6: num(mkdirat(AT_FDCWD,path(a),b)); break;
    case 7: num(unlinkat(AT_FDCWD,path(a),b ? AT_REMOVEDIR : 0)); break;
    case 8: num(renameat(AT_FDCWD,path(a),AT_FDCWD,path(b))); break;
    case 9: num(symlinkat(path(a),AT_FDCWD,path(b))); break;
    case 10: bytes(buf,readlinkat(AT_FDCWD,path(a),(char *)buf,sizeof(buf))); break;
    case 11: if (pipe2(f,O_CLOEXEC|O_NONBLOCK)) num(-1); else pair(f[0],f[1]); break;
    case 12: {
        struct pollfd p[]={{a,POLLIN|POLLOUT,0},{b,POLLIN|POLLOUT,0}};
        struct timespec now={0};
        if (ppoll(p,2,&now,NULL)<0) num(-1); else pair(p[0].revents,p[1].revents);
        break;
    }
    case 13: if (makepty(f)) num(-1); else pair(f[0],f[1]); break;
    case 14: num(attrs(a,b)); break;
    case 15: interrupt_poll(); break;
    case 16: bytes(buf,pread(a,buf,b,c)); break;
    case 17: populate(buf,b,c); num(pwrite(a,buf,b,c%11)); break;
    case 18: {
        int done=0; populate(buf,b,c);
        while (done<b) {
            int k=write(a,buf+done,b-done);
            if (k<0 && errno==EINTR) continue;
            if (k<=0) {num(k<0 ? k : -1); return;} done+=k;
        }
        num(0); break;
    }
    case 19: line_and_all(a,b); break;
    case 20:
        if (pipe2(f,O_NONBLOCK|O_CLOEXEC)) num(-1);
        else {
            if (fcntl(f[1],F_SETPIPE_SZ,4096)!=4096) die("set one-page pipe");
            pair(f[0],f[1]);
        }
        break;
    case 21: {
        unsigned char page[4096+23];
        int n=b ? 4096+b : 4095;
        populate(page,n,c); num(write(a,page,n)); break;
    }
    case 22: {
        unsigned char page[4096];
        bytes(page,read(a,page,sizeof(page))); break;
    }
    default: die("unknown command");
    }
}
int main(void) {
    signal(SIGPIPE,SIG_IGN);
    struct sigaction action={.sa_handler=ignored};
    sigaction(SIGWINCH,&action,NULL);
    sigset_t blocked; sigemptyset(&blocked); sigaddset(&blocked,SIGWINCH);
    if (sigprocmask(SIG_BLOCK,&blocked,NULL)) die("sigmask");
    umask(0022);
    unsigned long id; int count;
    while (scanf("%lu %d",&id,&count)==2) {
        if (count<0 || count>40) die("case size");
        char name[64]; snprintf(name,sizeof(name),"D%lu",id);
        snprintf(abs_a,sizeof(abs_a),"/work/D%lu/a",id); snprintf(abs_s,sizeof(abs_s),"/work/D%lu/s",id);
        if (chdir("/work") || mkdir(name,0755) || chdir(name)) die("case directory");
        for (int i=0;i<count;i++) {
            int op,a,b,c;
            if (scanf("%d %d %d %d",&op,&a,&b,&c)!=4) die("case format");
            if (!valid(op,a,b,c)) die("invalid encoded operation");
            operation(op,a,b,c); putchar('\n');
        }
        if (close_range(3,~0U,0)) die("close case descriptors");
    }
    return ferror(stdin) || ferror(stdout);
}
