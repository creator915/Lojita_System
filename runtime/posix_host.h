#ifndef LOJITA_POSIX_HOST_H
#define LOJITA_POSIX_HOST_H

#include <lean/lean.h>
#include <stdint.h>

/* Lean 4.36, Linux amd64. Strings are raw byte arrays with a trailing NUL.
   Reply is a Lean structure containing an errno, an unsigned scalar, and
   optional data. Stat fields and poll arrays use little-endian integers. */
LEAN_EXPORT lean_obj_res lojita_posix_call(uint32_t operation, uint64_t a,
    uint64_t b, uint64_t c, b_lean_obj_arg x, b_lean_obj_arg y);

#endif
