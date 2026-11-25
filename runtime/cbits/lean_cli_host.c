#define CT_HAVE_OPENSSL 1
#include "../cli_host.c"
#include <lean/lean.h>
#if __has_include(<openssl/sha.h>)
#include <openssl/sha.h>
#else
/* Minimal libcrypto ABI, as in cli_host.c on headerless runtime images. */
extern unsigned char *SHA256(const unsigned char *, size_t, unsigned char *);
#define SHA256_DIGEST_LENGTH 32
#endif

LEAN_EXPORT lean_obj_res ct_lean_sha256(b_lean_obj_arg bytes) {
    unsigned char digest[SHA256_DIGEST_LENGTH];
    static const char hex[] = "0123456789abcdef";
    char result[2 * SHA256_DIGEST_LENGTH + 1];
    if (SHA256(lean_sarray_cptr(bytes), lean_sarray_size(bytes), digest) == NULL) {
        return lean_mk_string("");
    }
    for (size_t i = 0; i < sizeof(digest); ++i) {
        result[2 * i] = hex[digest[i] >> 4];
        result[2 * i + 1] = hex[digest[i] & 15];
    }
    result[sizeof(result) - 1] = '\0';
    return lean_mk_string(result);
}

static size_t ct_lean_str_byte_len(b_lean_obj_arg s) {
    size_t sz = lean_string_size(s);
    return sz > 0 ? sz - 1 : 0;
}

static lean_object *ct_mk_byte_array(const uint8_t *buf, size_t len) {
    lean_object *ba = lean_alloc_sarray(1, len, len);
    if (len > 0 && buf) {
        memcpy(lean_sarray_cptr(ba), buf, len);
    }
    return ba;
}

static lean_object *ct_mk_pair(lean_object *fst, lean_object *snd) {
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, fst);
    lean_ctor_set(pair, 1, snd);
    return pair;
}

static lean_object *ct_mk_except_nat_err(size_t code) {
    lean_object *res = lean_alloc_ctor(0, 1, 0); /* Except.error */
    lean_ctor_set(res, 0, lean_box(code));
    return res;
}

static lean_object *ct_mk_except_ok(lean_object *val) {
    lean_object *res = lean_alloc_ctor(1, 1, 0); /* Except.ok */
    lean_ctor_set(res, 0, val);
    return res;
}

/* Clock */
LEAN_EXPORT lean_obj_res ct_lean_now_mono_ms(void) {
    uint64_t ms = ct_now_mono_ms();
    return lean_io_result_mk_ok(lean_uint64_to_nat(ms));
}

LEAN_EXPORT lean_obj_res ct_lean_now_wall_ms(void) {
    uint64_t ms = ct_now_wall_ms();
    return lean_io_result_mk_ok(lean_uint64_to_nat(ms));
}

LEAN_EXPORT lean_obj_res ct_lean_sleep_ms(uint32_t ms) {
    ct_sleep_ms(ms);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Process environment */
LEAN_EXPORT lean_obj_res ct_lean_prog_name(void) {
    const char *p = ct_get_prog_name();
    return lean_io_result_mk_ok(lean_mk_string(p ? p : ""));
}

LEAN_EXPORT lean_obj_res ct_lean_argc(void) {
    int n = ct_get_argc();
    return lean_io_result_mk_ok(lean_box((size_t)(n < 0 ? 0 : n)));
}

LEAN_EXPORT lean_obj_res ct_lean_arg_at(uint32_t idx) {
    const char *a = ct_get_arg((int)idx);
    return lean_io_result_mk_ok(lean_mk_string(a ? a : ""));
}

LEAN_EXPORT lean_obj_res ct_lean_lookup_env(b_lean_obj_arg key_obj) {
    const char *k = lean_string_cstr(key_obj);
    size_t klen = ct_lean_str_byte_len(key_obj);
    const char *v = ct_lookup_env_n(k, klen);
    if (!v) {
        return lean_io_result_mk_ok(lean_box(0)); /* Option.none */
    }
    lean_object *some_v = lean_alloc_ctor(1, 1, 0); /* Option.some */
    lean_ctor_set(some_v, 0, lean_mk_string(v));
    return lean_io_result_mk_ok(some_v);
}

/* Standard streams and controlling terminal */
static lean_obj_res ct_lean_byte_result(int got, uint8_t byte) {
    if (!got) return lean_io_result_mk_ok(lean_box(0)); /* Option.none */
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, lean_box(byte));
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_obj_res ct_lean_read_stdin_byte(void) {
    int got = 0;
    uint8_t byte = 0;
    if (ct_read_stdin_byte(&got, &byte) < 0) {
        return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    }
    return ct_lean_byte_result(got, byte);
}

LEAN_EXPORT lean_obj_res ct_lean_is_tty(uint32_t fd) {
    int r = ct_is_tty((int)fd);
    return lean_io_result_mk_ok(lean_box(r ? 1 : 0));
}

LEAN_EXPORT lean_obj_res ct_lean_has_tty(void) {
    return lean_io_result_mk_ok(lean_box(ct_has_tty()));
}

LEAN_EXPORT lean_obj_res ct_lean_set_tty_raw(uint8_t raw) {
    return lean_io_result_mk_ok(lean_box(ct_set_tty_raw(raw)));
}

LEAN_EXPORT lean_obj_res ct_lean_term_size(void) {
    uint32_t rows = 24, cols = 80;
    ct_term_size(&rows, &cols);
    return lean_io_result_mk_ok(ct_mk_pair(lean_uint32_to_nat(rows), lean_uint32_to_nat(cols)));
}

LEAN_EXPORT lean_obj_res ct_lean_write_fd(uint32_t fd, b_lean_obj_arg ba_obj) {
    const uint8_t *ptr = lean_sarray_cptr(ba_obj);
    size_t len = lean_sarray_size(ba_obj);
    (void)ct_write_fd_all((int)fd, ptr, len);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res ct_lean_read_tty_byte(void) {
    int got = 0;
    uint8_t b = 0;
    (void)ct_read_tty_byte(&got, &b);
    return ct_lean_byte_result(got, b);
}

LEAN_EXPORT lean_obj_res ct_lean_write_tty(b_lean_obj_arg ba) {
    int ok = ct_write_tty_all(lean_sarray_cptr(ba), lean_sarray_size(ba));
    return lean_io_result_mk_ok(lean_box(ok));
}

LEAN_EXPORT lean_obj_res ct_lean_poll_reactive_event(uint32_t poll_mask, uint32_t wait_ms) {
    uint32_t a = 0, b = 0;
    uint8_t *buf = NULL;
    size_t len = 0;
    int kind = ct_poll_reactive_event(poll_mask, wait_ms, &a, &b, &buf, &len);
    if (kind < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
    lean_object *ba = ct_mk_byte_array(buf, len);
    ct_free_buf(buf);
    lean_object *payload = ct_mk_pair(lean_uint32_to_nat(b), ba);
    lean_object *fields = ct_mk_pair(lean_uint32_to_nat(a), payload);
    return lean_io_result_mk_ok(ct_mk_pair(lean_box((size_t)kind), fields));
}

/* Filesystem */
LEAN_EXPORT lean_obj_res ct_lean_fs_read_file(b_lean_obj_arg path_obj) {
    const char *p = lean_string_cstr(path_obj);
    size_t plen = ct_lean_str_byte_len(path_obj);
    uint8_t *buf = NULL;
    size_t len = 0;
    int rc = ct_fs_read_file(p, plen, &buf, &len);
    if (rc != CT_FS_OK) {
        ct_free_buf(buf);
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)rc));
    }
    lean_object *ba = ct_mk_byte_array(buf, len);
    ct_free_buf(buf);
    return lean_io_result_mk_ok(ct_mk_except_ok(ba));
}

LEAN_EXPORT lean_obj_res ct_lean_fs_write_file(b_lean_obj_arg path_obj, b_lean_obj_arg ba_obj) {
    const char *p = lean_string_cstr(path_obj);
    size_t plen = ct_lean_str_byte_len(path_obj);
    const uint8_t *buf = lean_sarray_cptr(ba_obj);
    size_t len = lean_sarray_size(ba_obj);
    int rc = ct_fs_write_file(p, plen, buf, len);
    if (rc != CT_FS_OK) {
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)rc));
    }
    return lean_io_result_mk_ok(ct_mk_except_ok(lean_box(0)));
}

LEAN_EXPORT lean_obj_res ct_lean_fs_mkdir(b_lean_obj_arg path_obj, uint32_t mode) {
    const char *p = lean_string_cstr(path_obj);
    size_t plen = ct_lean_str_byte_len(path_obj);
    int rc = ct_fs_mkdir(p, plen, mode);
    if (rc != CT_FS_OK) {
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)rc));
    }
    return lean_io_result_mk_ok(ct_mk_except_ok(lean_box(0)));
}

LEAN_EXPORT lean_obj_res ct_lean_fs_symlink(b_lean_obj_arg path_obj, b_lean_obj_arg dest_obj) {
    const char *p = lean_string_cstr(path_obj);
    size_t plen = ct_lean_str_byte_len(path_obj);
    const char *d = lean_string_cstr(dest_obj);
    size_t dlen = ct_lean_str_byte_len(dest_obj);
    int rc = ct_fs_symlink(p, plen, d, dlen);
    if (rc != CT_FS_OK) {
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)rc));
    }
    return lean_io_result_mk_ok(ct_mk_except_ok(lean_box(0)));
}

LEAN_EXPORT lean_obj_res ct_lean_fs_unlink(b_lean_obj_arg path_obj) {
    const char *p = lean_string_cstr(path_obj);
    size_t plen = ct_lean_str_byte_len(path_obj);
    int rc = ct_fs_unlink(p, plen);
    if (rc != CT_FS_OK) {
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)rc));
    }
    return lean_io_result_mk_ok(ct_mk_except_ok(lean_box(0)));
}

LEAN_EXPORT lean_obj_res ct_lean_fs_stat(b_lean_obj_arg path_obj) {
    const char *p = lean_string_cstr(path_obj);
    size_t plen = ct_lean_str_byte_len(path_obj);
    int kind = 0;
    int rc = ct_fs_stat(p, plen, &kind);
    if (rc != CT_FS_OK) {
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)rc));
    }
    return lean_io_result_mk_ok(ct_mk_except_ok(lean_box((size_t)kind)));
}

/* Network */
LEAN_EXPORT lean_obj_res ct_lean_tcp_exchange(
    b_lean_obj_arg host_obj,
    uint32_t port,
    b_lean_obj_arg req_obj,
    uint8_t half_close,
    uint32_t timeout_ms)
{
    const char *host = lean_string_cstr(host_obj);
    const uint8_t *req_ptr = lean_sarray_cptr(req_obj);
    size_t req_len = lean_sarray_size(req_obj);

    uint8_t *out_buf = NULL;
    size_t out_len = 0;
    char err_buf[512];
    err_buf[0] = '\0';

    int rc = ct_tcp_exchange(
        host, port, req_ptr, req_len, (int)half_close, timeout_ms,
        &out_buf, &out_len, err_buf, sizeof(err_buf));

    if (rc != 0) {
        lean_object *err_str = lean_mk_string(err_buf[0] ? err_buf : "tcp error");
        lean_object *res = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(res, 0, err_str);
        return lean_io_result_mk_ok(res);
    }

    lean_object *ba = ct_mk_byte_array(out_buf, out_len);
    ct_free_buf(out_buf);
    return lean_io_result_mk_ok(ct_mk_except_ok(ba));
}

LEAN_EXPORT lean_obj_res ct_lean_tls_exchange(
    b_lean_obj_arg host_obj,
    uint32_t port,
    b_lean_obj_arg sni_obj,
    uint8_t insecure_skip_verify,
    b_lean_obj_arg tunnel_obj,
    b_lean_obj_arg req_obj,
    uint32_t timeout_ms)
{
    const char *host = lean_string_cstr(host_obj);
    const char *sni  = lean_string_cstr(sni_obj);
    const uint8_t *tun_ptr = lean_sarray_cptr(tunnel_obj);
    size_t tun_len = lean_sarray_size(tunnel_obj);
    const uint8_t *req_ptr = lean_sarray_cptr(req_obj);
    size_t req_len = lean_sarray_size(req_obj);

    uint8_t *out_buf = NULL;
    size_t out_len = 0;
    char err_buf[512];
    err_buf[0] = '\0';

    int rc = ct_tls_exchange(
        host, port, sni, (int)insecure_skip_verify,
        tun_ptr, tun_len, req_ptr, req_len, timeout_ms,
        &out_buf, &out_len, err_buf, sizeof(err_buf));

    if (rc != 0) {
        lean_object *err_str = lean_mk_string(err_buf[0] ? err_buf : "tls error");
        lean_object *res = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(res, 0, err_str);
        return lean_io_result_mk_ok(res);
    }

    lean_object *ba = ct_mk_byte_array(out_buf, out_len);
    ct_free_buf(out_buf);
    return lean_io_result_mk_ok(ct_mk_except_ok(ba));
}

LEAN_EXPORT lean_obj_res ct_lean_tcp_exchange_code(
    b_lean_obj_arg host_obj,
    uint32_t port,
    b_lean_obj_arg req_obj,
    uint8_t half_close,
    uint32_t timeout_ms)
{
    const char *host = lean_string_cstr(host_obj);
    size_t hlen = ct_lean_str_byte_len(host_obj);
    const uint8_t *req_ptr = lean_sarray_cptr(req_obj);
    size_t req_len = lean_sarray_size(req_obj);

    uint8_t *out_buf = NULL;
    size_t out_len = 0;
    int err_code = CT_NET_IO_ERROR;

    int rc = ct_tcp_exchange_code(
        host, hlen, port, req_ptr, req_len, (int)half_close, timeout_ms,
        &out_buf, &out_len, &err_code);

    if (rc != 0) {
        ct_free_buf(out_buf);
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)(err_code > 0 ? err_code : CT_NET_IO_ERROR)));
    }
    lean_object *ba = ct_mk_byte_array(out_buf, out_len);
    ct_free_buf(out_buf);
    return lean_io_result_mk_ok(ct_mk_except_ok(ba));
}

LEAN_EXPORT lean_obj_res ct_lean_tls_exchange_code(
    b_lean_obj_arg host_obj,
    uint32_t port,
    b_lean_obj_arg sni_obj,
    uint8_t insecure_skip_verify,
    b_lean_obj_arg tunnel_obj,
    b_lean_obj_arg req_obj,
    uint32_t timeout_ms)
{
    const char *host = lean_string_cstr(host_obj);
    size_t hlen = ct_lean_str_byte_len(host_obj);
    const char *sni  = lean_string_cstr(sni_obj);
    size_t slen = ct_lean_str_byte_len(sni_obj);
    const uint8_t *tun_ptr = lean_sarray_cptr(tunnel_obj);
    size_t tun_len = lean_sarray_size(tunnel_obj);
    const uint8_t *req_ptr = lean_sarray_cptr(req_obj);
    size_t req_len = lean_sarray_size(req_obj);

    uint8_t *out_buf = NULL;
    size_t out_len = 0;
    int err_code = CT_NET_IO_ERROR;

    int rc = ct_tls_exchange_code(
        host, hlen, port, sni, slen, (int)insecure_skip_verify,
        tun_ptr, tun_len, req_ptr, req_len, timeout_ms,
        &out_buf, &out_len, &err_code);

    if (rc != 0) {
        ct_free_buf(out_buf);
        return lean_io_result_mk_ok(ct_mk_except_nat_err((size_t)(err_code > 0 ? err_code : CT_NET_IO_ERROR)));
    }
    lean_object *ba = ct_mk_byte_array(out_buf, out_len);
    ct_free_buf(out_buf);
    return lean_io_result_mk_ok(ct_mk_except_ok(ba));
}

LEAN_EXPORT lean_obj_res ct_lean_exit_code(uint32_t code) {
    ct_exit_code(code);
    return lean_io_result_mk_ok(lean_box(0));
}
