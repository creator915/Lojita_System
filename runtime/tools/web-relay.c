/* Integer sample points, half-open rectangles and positive uniform similarities.
 * Only stdout carries protocol replies. A rejected frame terminates the session. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

enum { MAX_SIDE = 2048, MAX_DEPTH = 64, MAX_LINE = 4 * 1024 * 1024 };
typedef __int128 Wide;
typedef struct { uint8_t r, g, b, alpha; } Pixel;
typedef struct { int x0, y0, x1, y1; } Bounds;
typedef struct { int64_t n, d, tx, ty; Bounds clip; } Frame;
typedef struct { int64_t x, y, w, h; } Rect;

static int width, height, depth, file_count;
static char **files;
static Pixel *pixels;
static Frame frame, saved[MAX_DEPTH];

static void reject(const char *why) {
    fprintf(stderr, "web-relay: %s\n", why);
    exit(2);
}

static int64_t number(const char *s, int64_t min, int64_t max) {
    char *end;
    if (!s || !*s) reject("missing number");
    errno = 0;
    long long v = strtoll(s, &end, 10);
    if (*end || errno || v < min || v > max) reject("invalid number");
    return v;
}

static int64_t arg(char **cursor, int64_t lo, int64_t hi) {
    return number(strtok_r(NULL, " ", cursor), lo, hi);
}

static int64_t coord(char **cursor) { return arg(cursor, INT32_MIN, INT32_MAX); }

static void reset(void) {
    frame = (Frame){1,1,0,0,{0,0,width,height}};
    depth = 0;
    memset(pixels, 0, (size_t)width * height * sizeof(*pixels));
}

static void resize(int w, int h) {
    Pixel *p = calloc((size_t)w * h, sizeof(*p));
    if (!p) reject("framebuffer allocation");
    free(pixels);
    pixels = p;
    width = w;
    height = h;
    reset();
}

static Wide magnitude(Wide x) { return x < 0 ? -x : x; }

static Wide gcd(Wide a, Wide b) {
    while (b) { Wide r = a % b; a = b; b = r; }
    return a;
}

static int64_t coefficient(Wide x) {
    if (magnitude(x) > ((Wide)1 << 48)) reject("transform precision limit");
    return (int64_t)x;
}

/* Postmultiply the current matrix. Divide all homogeneous coefficients by
 * their common divisor before checking the representation bound. */
static void transform(int64_t n, int64_t d, int64_t x, int64_t y) {
    Wide a = (Wide)frame.n * n, b = (Wide)frame.d * d;
    Wide tx = (Wide)frame.n * x + (Wide)frame.tx * d;
    Wide ty = (Wide)frame.n * y + (Wide)frame.ty * d;
    Wide g = gcd(gcd(a,b), gcd(magnitude(tx),magnitude(ty)));
    frame.n = coefficient(a/g);
    frame.d = coefficient(b/g);
    frame.tx = coefficient(tx/g);
    frame.ty = coefficient(ty/g);
}

/* For integer samples, [L,R) projects to [ceil(T L),ceil(T R)). */
static int edge(int64_t x, int64_t shift, int limit) {
    Wide p = (Wide)frame.n * x + shift;
    if (p <= 0) return 0;
    Wide v = (p + frame.d - 1) / frame.d;
    return v >= limit ? limit : (int)v;
}

static int larger(int a, int b) { return a > b ? a : b; }
static int smaller(int a, int b) { return a < b ? a : b; }

static Bounds bounds(Rect r) {
    Bounds c = frame.clip;
    return (Bounds){ larger(c.x0,edge(r.x,frame.tx,width)), larger(c.y0,edge(r.y,frame.ty,height)),
                     smaller(c.x1,edge(r.x+r.w,frame.tx,width)), smaller(c.y1,edge(r.y+r.h,frame.ty,height)) };
}

static void fill(Rect r, Pixel ink) {
    Bounds b = bounds(r);
    for (int y = b.y0; y < b.y1; ++y)
        for (int x = b.x0; x < b.x1; ++x) pixels[y*width+x] = ink;
}

static void stroke(Rect r, Pixel ink) {
    if (!r.w || !r.h) return;
    fill((Rect){r.x,r.y,r.w,1},ink);
    fill((Rect){r.x,r.y+r.h-1,r.w,1},ink);
    fill((Rect){r.x,r.y,1,r.h},ink);
    fill((Rect){r.x+r.w-1,r.y,1,r.h},ink);
}

static void line(int64_t x, int64_t y, int64_t u, int64_t v, Pixel ink) {
    int64_t dx = u-x, dy = v-y;
    Wide major = magnitude(dx) > magnitude(dy) ? magnitude(dx) : magnitude(dy);
    if (!major) { fill((Rect){x,y,1,1},ink); return; }
    Bounds b = bounds((Rect){x<u?x:u, y<v?y:v, (int64_t)magnitude(dx)+1, (int64_t)magnitude(dy)+1});
    for (int j = b.y0; j < b.y1; ++j) {
        Wide sy = (Wide)frame.d*j - frame.ty - (Wide)y*frame.n;
        for (int i = b.x0; i < b.x1; ++i) {
            Wide sx = (Wide)frame.d*i - frame.tx - (Wide)x*frame.n;
            if (2*magnitude(sx*dy - sy*dx) <= major*frame.n) pixels[j*width+i] = ink;
        }
    }
}

static int nibble(char c) {
    if (c >= '0' && c <= '9') return c-'0';
    if (c >= 'a' && c <= 'f') return c-'a'+10;
    if (c >= 'A' && c <= 'F') return c-'A'+10;
    reject("invalid hex");
    return 0;
}

static size_t unhex(char *s) {
    if (!s) reject("missing hex");
    if (!strcmp(s,"-")) { *s = 0; return 0; }
    size_t len = strlen(s);
    if (len % 2) reject("odd hex");
    for (size_t i = 0; i < len/2; ++i)
        s[i] = (char)(16*nibble(s[2*i]) + nibble(s[2*i+1]));
    s[len/2] = 0;
    return len/2;
}

/* A deterministic glyph cell for each UTF-8 scalar. Space has advance only. */
static void text(Rect r, Pixel ink, char *hex) {
    size_t len = unhex(hex);
    Bounds prior = frame.clip;
    frame.clip = bounds(r);
    int64_t x = r.x+6, y = r.y+(r.h>7?(r.h-7)/2:0);
    for (size_t i=0; i<len && x<r.x+r.w; ++i) {
        unsigned ch = (unsigned char)hex[i];
        if ((ch & 192) == 128) continue;
        if (ch != ' ') {
            stroke((Rect){x,y,4,7},ink);
            fill((Rect){x+1,y+1+(ch%5),2,1},ink);
        }
        x += 6;
    }
    frame.clip = prior;
}

static Rect read_rect(char **cursor) {
    Rect r;
    r.x = coord(cursor); r.y = coord(cursor);
    r.w = arg(cursor,0,INT32_MAX); r.h = arg(cursor,0,INT32_MAX);
    return r;
}

static Pixel read_colour(char **cursor) {
    Pixel p;
    p.r = (uint8_t)arg(cursor,0,255);
    p.g = (uint8_t)arg(cursor,0,255);
    p.b = (uint8_t)arg(cursor,0,255);
    p.alpha = 255;
    return p;
}

static void draw(char *command) {
    char *cursor = NULL, *op = strtok_r(command," ",&cursor);
    if (!op) reject("empty draw command");
    if (!strcmp(op,"SAVE")) {
        if (depth == MAX_DEPTH) reject("stack overflow");
        saved[depth++] = frame;
    } else if (!strcmp(op,"RESTORE")) {
        if (!depth) reject("stack underflow");
        frame = saved[--depth];
    } else if (!strcmp(op,"TRANSFORM")) {
        int64_t n = arg(&cursor,1,INT32_MAX), d = arg(&cursor,1,INT32_MAX);
        int64_t x = coord(&cursor), y = coord(&cursor);
        transform(n,d,x,y);
    } else if (!strcmp(op,"CLIP")) {
        frame.clip = bounds(read_rect(&cursor));
    } else if (!strcmp(op,"LINE")) {
        Pixel c = read_colour(&cursor);
        int64_t x = coord(&cursor), y = coord(&cursor);
        int64_t u = coord(&cursor), v = coord(&cursor);
        line(x,y,u,v,c);
    } else if (!strcmp(op,"FILL") || !strcmp(op,"STROKE") || !strcmp(op,"TEXT")) {
        Pixel c = read_colour(&cursor);
        Rect r = read_rect(&cursor);
        if (!strcmp(op,"FILL")) fill(r,c);
        else if (!strcmp(op,"STROKE")) stroke(r,c);
        else text(r,c,strtok_r(NULL," ",&cursor));
    } else reject("unknown draw command");
    if (strtok_r(NULL," ",&cursor)) reject("extra argument");
}

/* Walk by directory descriptor. Neither directory components nor the leaf
 * may be symlinks. Never truncate until the open file is known to be owned. */
static void export_ppm(char *path) {
    int known = 0;
    for (int i=0; i<file_count; ++i) if (!strcmp(files[i],path)) known = 1;
    if (!known || !*path || *path=='/' || path[strlen(path)-1]=='/' || strstr(path,"//")) reject("unowned path");
    int dir = open(".",O_RDONLY|O_DIRECTORY|O_CLOEXEC);
    if (dir < 0) reject("open work directory");
    char *part = path;
    for (;;) {
        char *slash = strchr(part,'/');
        if (slash) *slash = 0;
        if (!strcmp(part,".") || !strcmp(part,"..")) reject("invalid path component");
        if (!slash) break;
        int next = openat(dir,part,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
        if (next < 0) reject("invalid export directory");
        close(dir); dir=next; part=slash+1;
    }
    int fd = openat(dir,part,O_WRONLY|O_NOFOLLOW|O_NONBLOCK|O_CLOEXEC);
    close(dir);
    struct stat st;
    if (fd < 0 || fstat(fd,&st) || !S_ISREG(st.st_mode) || st.st_nlink!=1 || ftruncate(fd,0)) reject("invalid export file");
    FILE *out = fdopen(fd,"wb");
    if (!out || fprintf(out,"P6\n%d %d\n255\n",width,height)<0) reject("PPM header");
    unsigned char row[MAX_SIDE*3];
    for (int y=0; y<height; ++y) {
        for (int x=0; x<width; ++x) {
            Pixel p=pixels[y*width+x];
            row[3*x]=p.r; row[3*x+1]=p.g; row[3*x+2]=p.b;
        }
        if (fwrite(row,3,(size_t)width,out)!=(size_t)width) reject("PPM raster");
    }
    if (fclose(out)) reject("PPM close");
}

int main(int argc, char **argv) {
    if (argc < 3) reject("expected width and height");
    files = argv+3; file_count = argc-3;
    resize((int)number(argv[1],1,MAX_SIDE),(int)number(argv[2],1,MAX_SIDE));
    char *request = malloc(MAX_LINE+2);
    if (!request) reject("protocol buffer");
    puts("READY"); fflush(stdout);
    while (fgets(request,MAX_LINE+2,stdin)) {
        char *end = strchr(request,'\n');
        if (!end) reject("oversized or incomplete request");
        *end = 0;
        if (!strcmp(request,"STOP")) { puts("OK"); break; }
        if (!strncmp(request,"FLUSH ",6)) {
            char *wire=request+6, *next=NULL;
            size_t len=unhex(wire), count=0;
            if (memchr(wire,0,len)) reject("NUL in draw stream");
            reset();
            for (char *cmd=strtok_r(wire,"\n",&next); cmd; cmd=strtok_r(NULL,"\n",&next)) {
                draw(cmd); ++count;
            }
            if (depth) reject("unbalanced frame");
            printf("FRAME %zu %d\n",count,depth);
        } else if (!strncmp(request,"EXPORT_PPM ",11)) {
            export_ppm(request+11); puts("OK");
        } else {
            char *cursor=NULL, *op=strtok_r(request," ",&cursor);
            if (!op) reject("empty request");
            if (!strcmp(op,"PIXEL")) {
                int x=(int)arg(&cursor,0,width-1), y=(int)arg(&cursor,0,height-1);
                if (strtok_r(NULL," ",&cursor)) reject("extra pixel argument");
                Pixel p=pixels[y*width+x];
                printf("PIXEL %u %u %u %u\n",(unsigned)(p.alpha != 0),p.r,p.g,p.b);
            } else if (!strcmp(op,"RESIZE")) {
                int w=(int)arg(&cursor,1,MAX_SIDE), h=(int)arg(&cursor,1,MAX_SIDE);
                if (strtok_r(NULL," ",&cursor)) reject("extra resize argument");
                resize(w,h); puts("OK");
            } else reject("unknown request");
        }
        fflush(stdout);
    }
    free(request); free(pixels);
    return ferror(stdin) || fflush(stdout) != 0;
}
