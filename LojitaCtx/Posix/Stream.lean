import LojitaCtx.Posix.Types

namespace LojitaCtx.Posix

structure StreamBuf where
  pendingBytes : Bytes := []
  cap : Nat := 65536
  readers : Nat := 1
  writers : Nat := 1
  deriving Repr, DecidableEq, Inhabited

def StreamBuf.available (s : StreamBuf) := s.pendingBytes.length
def StreamBuf.freeSpace (s : StreamBuf) := s.cap - s.available

private def waiting {α : Type} (nb : Bool) (event : WaitFor) : Ret α :=
  if nb then .err .EAGAIN else .wouldBlock event

/-- A read of positive size. The syscall layer handles a zero-sized request. -/
def streamRead (sl : StepSlice) (nb : Bool) (s : StreamBuf) : Ret Bytes × StreamBuf :=
  if sl.intrBefore then (.err .EINTR, s) else
  match s.pendingBytes with
  | [] => (if s.writers = 0 then .ok [] else waiting nb .readable, s)
  | b :: bs =>
    let n := sl.maxBytes - 1
    (.ok (b :: bs.take n), { s with pendingBytes := bs.drop n })

def pipeBuf : Nat := 4096

/-- For a small pipe write the entire request must fit atomically. A large
    request may complete partially. EPIPE on a nonempty write signals the caller. -/
def streamWrite (sl : StepSlice) (nb : Bool) (bs : Bytes) (s : StreamBuf) :
    Ret Nat × StreamBuf :=
  if bs.isEmpty then (.ok 0, s)
  else if s.readers = 0 then (.err .EPIPE, s)
  else if sl.intrBefore then (.err .EINTR, s)
  else if s.freeSpace = 0 || (bs.length ≤ pipeBuf && s.freeSpace < bs.length) then
    (waiting nb .writable, s)
  else
    let n := if bs.length ≤ pipeBuf then bs.length
             else min bs.length (min s.freeSpace (max 1 sl.maxBytes))
    (.ok n, { s with pendingBytes := s.pendingBytes ++ bs.take n })

theorem streamRead_eof_iff (sl : StepSlice) (nb : Bool) (s : StreamBuf)
    (h : sl.intrBefore = false) :
    (streamRead sl nb s).1 = .ok [] ↔ s.available = 0 ∧ s.writers = 0 := by
  cases hp : s.pendingBytes with
  | nil => by_cases hw : s.writers = 0 <;> cases nb <;> simp [streamRead, h, hp, hw, waiting, StreamBuf.available]
  | cons b bs => simp [streamRead, h, hp, StreamBuf.available]

theorem streamRead_blocked_preserves (sl : StepSlice) (nb : Bool) (s : StreamBuf)
    (h : (streamRead sl nb s).1 = .err .EAGAIN ∨ (streamRead sl nb s).1 = .err .EINTR ∨
      ∃ w, (streamRead sl nb s).1 = .wouldBlock w) : (streamRead sl nb s).2 = s := by
  cases hi : sl.intrBefore <;> cases hp : s.pendingBytes <;> simp_all [streamRead]

theorem streamRead_byte_conservation (sl : StepSlice) (nb : Bool) (s s' : StreamBuf)
    (out : Bytes) (h : streamRead sl nb s = (.ok out, s')) :
    out ++ s'.pendingBytes = s.pendingBytes := by
  cases hi : sl.intrBefore <;> cases hp : s.pendingBytes with
  | nil =>
    by_cases hw : s.writers = 0 <;> cases nb <;>
      simp_all [streamRead, waiting]
  | cons b bs =>
    simp [streamRead, hi, hp] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp

theorem streamWrite_epipe (sl : StepSlice) (nb : Bool) (bs : Bytes) (s : StreamBuf)
    (hr : s.readers = 0) (hne : bs ≠ []) : streamWrite sl nb bs s = (.err .EPIPE, s) := by
  cases bs <;> simp_all [streamWrite]

end LojitaCtx.Posix
