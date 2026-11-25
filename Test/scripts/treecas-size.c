/* Test the production checked conversion with the host ABI. The same source
   can be built with -m32 -msse2 -mfpmath=sse and ILP32 libc headers. Link
   with --gc-sections so this arithmetic test needs no Lean runtime. */
#include "../../runtime/tree_cas.c"

int main(void) {
    _Static_assert(sizeof(off_t) == 8, "TreeCAS requires large-file offsets");
    size_t out;
    if (file_length(0,&out) || out != 0) return 1;
    if (file_length(4194304,&out) || out != 4194304) return 2;
    if (!file_length(-1,&out) || errno != EFBIG) return 3;
#if SIZE_MAX == UINT32_MAX
    if (!file_length(INT64_C(4294967296),&out) || errno != EFBIG) return 4;
    if (!file_length(INT64_C(4294967295),&out) || errno != EFBIG) return 5;
    if (file_length(UINT32_MAX - sizeof(lean_sarray_object) - 16,&out)) return 6;
#else
    if (file_length(INT64_C(4294967296),&out) || out != INT64_C(4294967296)) return 7;
#endif
    return 0;
}
