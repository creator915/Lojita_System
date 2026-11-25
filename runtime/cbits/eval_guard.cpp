#include <lean/lean.h>

namespace lean {
void reset_heartbeat();
}

extern "C" lean_obj_res lean_add_decl(
    lean_obj_arg env, size_t max_heartbeat, size_t max_rec_depth,
    b_lean_obj_arg decl, b_lean_obj_arg cancel_tk);
extern "C" lean_obj_res lean_eval_const(b_lean_obj_arg env, b_lean_obj_arg opts, b_lean_obj_arg c);

// Upstream Lean 4.36 maintains two disjoint TLS counters:
//   1. Allocator heartbeats (`object.cpp`, `lean::get_num_heartbeats()`), used by `CoreM`/`MetaM`;
//   2. Kernel/runtime `check_system` heartbeats (`thread.cpp`, `g_heartbeat` vs `g_max_heartbeat`),
//      used by `lean_add_decl` and the IR interpreter.
// `lean_add_decl` sets `scope_max_heartbeat(max_heartbeat)` WITHOUT calling `lean::reset_heartbeat()`,
// causing `g_heartbeat` to accumulate across calls on the same worker thread and eventually trigger
// false-positive `deterministicTimeout`s! Calling `lean::reset_heartbeat()` immediately before
// `lean_add_decl` gives every kernel check an exact, zero-drift `check_system` budget while leaving
// `CoreM`'s allocator heartbeat counter completely untouched.
extern "C" LEAN_EXPORT lean_obj_res lojita_add_decl_guarded(
    lean_obj_arg env, size_t max_heartbeat, size_t max_rec_depth,
    b_lean_obj_arg decl, b_lean_obj_arg cancel_tk) noexcept {
  lean::reset_heartbeat();
  return lean_add_decl(env, max_heartbeat, max_rec_depth, decl, cancel_tk);
}

extern "C" LEAN_EXPORT lean_obj_res lojita_reset_runtime_heartbeat(lean_obj_arg /* world */) noexcept {
  lean::reset_heartbeat();
  return lean_io_result_mk_ok(lean_box(0));
}

// Upstream Lean 4.36's `lean_eval_const` only catches `lean::exception` and misses
// sibling subclasses of `lean::throwable` (`stack_space_exception`, `memory_exception`),
// causing `libc++abi` `std::terminate()` (`SIGABRT`) when `lean::check_stack` or
// `lean::check_memory` trips inside the IR bytecode interpreter.
// `catch (...)` uses only Itanium ABI `__cxa_begin_catch` / `__cxa_end_catch` with zero
// C++ STL header or `typeinfo` ABI coupling, turning any C++ unwind into `Except.error`.
extern "C" LEAN_EXPORT lean_obj_res lojita_eval_const_guarded(
    b_lean_obj_arg env, b_lean_obj_arg opts, b_lean_obj_arg c) noexcept {
  try {
    return lean_eval_const(env, opts, c);
  } catch (...) {
    lean_object * msg = lean_mk_string(
        "deep recursion or excessive memory intercepted in bytecode interpreter");
    lean_object * err = lean_alloc_ctor(0, 1, 0); // Except.error
    lean_ctor_set(err, 0, msg);
    return err;
  }
}
