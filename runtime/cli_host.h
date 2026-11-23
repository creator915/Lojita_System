#ifndef CODETRANSPORT_CLI_HOST_H
#define CODETRANSPORT_CLI_HOST_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* FsError codes matching Context.World.FsError (0 = ok) */
#define CT_FS_OK                0
#define CT_FS_NOT_FOUND         1
#define CT_FS_IS_DIRECTORY      2
#define CT_FS_NOT_DIRECTORY     3
#define CT_FS_ALREADY_EXISTS    4
#define CT_FS_PERMISSION_DENIED 5
#define CT_FS_SYMLINK_LOOP      6
#define CT_FS_INVALID_PATH      7
#define CT_FS_IO_ERROR          8

/* FsNodeKind codes matching Context.Tools.FsSandbox.FsNodeKind */
#define CT_NODE_REGULAR 0
#define CT_NODE_DIR     1
#define CT_NODE_SYMLINK 2

/* NetError codes matching Context.World.NetError (0 = ok) */
#define CT_NET_OK               0
#define CT_NET_CONN_REFUSED     1
#define CT_NET_TIMED_OUT        2
#define CT_NET_INVALID_ENDPOINT 3
#define CT_NET_TLS_ERROR        4
#define CT_NET_IO_ERROR         5

/* Clock */
uint64_t ct_now_mono_ms(void);
uint64_t ct_now_wall_ms(void);
void ct_sleep_ms(uint32_t ms);

/* Process environment */
const char *ct_get_prog_name(void);
int ct_get_argc(void);
const char *ct_get_arg(int idx);
const char *ct_lookup_env_n(const char *key, size_t key_len);

/* Standard streams */
/* A successful pull sets out_got_byte even when the byte is zero. It stays zero at EOF. */
int ct_read_stdin_byte(int *out_got_byte, uint8_t *out_byte);
int ct_is_tty(int fd);
int ct_write_fd_all(int fd, const uint8_t *buf, size_t len);

/* Controlling terminal */
int ct_has_tty(void);
int ct_set_tty_raw(int enable);
void ct_term_size(uint32_t *out_rows, uint32_t *out_cols);
int ct_read_tty_byte(int *out_got_byte, uint8_t *out_byte);
int ct_write_tty_all(const uint8_t *buf, size_t len);

#define CT_POLL_STDIO 1u
#define CT_POLL_TTY   2u
#define CT_POLL_SIG   4u
#define CT_POLL_CLOCK 8u

/* 1 = evTickMs (a = elapsed ms), 2 = evSignal (a = 1..4),
 * 3 = evResize (a = rows, b = cols), 4 = evTTYBytes (1..256 bytes),
 * 5 = evTTYEOF, 6 = evStdinBytes (1..4096 bytes), 7 = evStdinEOF.
 * Byte payloads belong to the caller and are released with ct_free_buf.
 * Other events leave *out_buf NULL and *out_len zero. Returns -1 on allocation failure. */
int ct_poll_reactive_event(uint32_t poll_mask, uint32_t wait_ms,
                           uint32_t *out_a, uint32_t *out_b,
                           uint8_t **out_buf, size_t *out_len);

/* Filesystem (1-to-1 with Context.World VirtualFs semantics) */
int ct_fs_read_file(const char *path, size_t path_len, uint8_t **out_buf, size_t *out_len);
int ct_fs_write_file(const char *path, size_t path_len, const uint8_t *buf, size_t len);
int ct_fs_mkdir(const char *path, size_t path_len, uint32_t mode);
int ct_fs_symlink(const char *path, size_t path_len, const char *dest, size_t dest_len);
int ct_fs_unlink(const char *path, size_t path_len);
int ct_fs_stat(const char *path, size_t path_len, int *out_kind);

/* Network */
int ct_tcp_exchange(
    const char *host,
    uint32_t port,
    const uint8_t *req,
    size_t req_len,
    int half_close,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    char *err_buf,
    size_t err_cap);
int ct_tls_exchange(
    const char *host,
    uint32_t port,
    const char *sni_host,
    int insecure_skip_verify,
    const uint8_t *tunnel_req,
    size_t tunnel_req_len,
    const uint8_t *req,
    size_t req_len,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    char *err_buf,
    size_t err_cap);
int ct_tcp_exchange_code(
    const char *host,
    size_t host_len,
    uint32_t port,
    const uint8_t *req,
    size_t req_len,
    int half_close,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    int *out_err_code);
int ct_tls_exchange_code(
    const char *host,
    size_t host_len,
    uint32_t port,
    const char *sni_host,
    size_t sni_len,
    int insecure_skip_verify,
    const uint8_t *tunnel_req,
    size_t tunnel_req_len,
    const uint8_t *req,
    size_t req_len,
    uint32_t timeout_ms,
    uint8_t **out_buf,
    size_t *out_len,
    int *out_err_code);

void ct_free_buf(void *p);
void ct_exit_code(uint32_t code);

#ifdef __cplusplus
}
#endif

#endif
