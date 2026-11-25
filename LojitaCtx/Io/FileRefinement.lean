import LojitaCtx.Io.FileKernel
import LojitaCtx.Io.FsLib

namespace LojitaCtx.Io.FsLib
open LojitaCtx.Posix

/-- A completed trace of actual regular-file reads at a stationary inode.
    Offsets follow the number of bytes Linux returned, starting at zero after open. -/
inductive FileReads (fd ino size : Nat) (bytes : ByteArray) :
    Nat → Machine → List StepSlice → List (Ret Bytes) → Machine → Prop where
  | eof {off m sl z}
    (file : AtRegular m fd ino bytes off)
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.ok [],z)) :
    FileReads fd ino size bytes off m [sl] [.ok []] z
  | data {off m sl next slices qs z b bs}
    (file : AtRegular m fd ino bytes off)
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.ok (b::bs),next))
    (rest : FileReads fd ino size bytes (off+(b::bs).length) next slices qs z) :
    FileReads fd ino size bytes off m (sl::slices) (.ok (b::bs)::qs) z
  | interrupted {off m sl slices qs z}
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.err .EINTR,m))
    (rest : FileReads fd ino size bytes off m slices qs z) :
    FileReads fd ino size bytes off m (sl::slices) (.err .EINTR::qs) z

theorem FileReads.toEof {fd ino size bytes off m slices qs z}
    (r : FileReads fd ino size bytes off m slices qs z) : ReadsToEof qs := by
  induction r with
  | eof _ _ => exact .eof
  | data _ _ _ ih => exact .data _ _ ih
  | interrupted _ _ ih => exact .interrupt ih

private theorem prefix_remaining (bs : Bytes) (n : Nat) :
    bs.take n ++ bs.drop (bs.take n).length = bs := by
  by_cases hn : n ≤ bs.length
  · simp [List.length_take, Nat.min_eq_left hn]
  · have h := Nat.le_of_not_ge hn
    simp [List.take_of_length_le h]

theorem FileReads.contents {fd ino size bytes off m slices qs z}
    (r : FileReads fd ino size bytes off m slices qs z) :
    delivered qs = bytes.data.toList.drop off ∧ z.fds = m.fds := by
  induction r with
  | @eof off m sl z file step =>
    obtain ⟨h,fds⟩ := inode_chunk file step
    refine ⟨?_,fds⟩
    change [] = _
    cases hx : bytes.data.toList.drop off with
    | nil => rfl
    | cons b bs =>
      have positive : 0 < min (max 1 size) (max 1 sl.maxBytes) := by omega
      cases hk : min (max 1 size) (max 1 sl.maxBytes) with
      | zero => omega
      | succ k => simp [hx,hk] at h
  | @data off m sl next slices qs z b bs file step rest ih =>
    obtain ⟨h,fds⟩ := inode_chunk file step
    refine ⟨?_,ih.2.trans fds⟩
    change (b::bs) ++ delivered qs = _
    rw [ih.1, ← List.drop_drop, h]
    exact prefix_remaining _ _
  | interrupted _ _ ih => exact ih

def sameDescriptors (a b : Machine) : Prop := ∀ (i : Fd), a.fds[i]? = b.fds[i]?

theorem close_restores {m opened before closed : Machine} {fd : Fd}
    (fresh : FreshFd m fd opened) (reads : before.fds = opened.fds)
    (closedFd : closed.fds = before.fds.erase fd) : sameDescriptors closed m := by
  obtain ⟨missing,entry,h⟩ := fresh
  intro i
  rw [closedFd, reads, h, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]
  split <;> rename_i cmp
  · have heq : fd = i := by simpa using cmp
    simpa [← heq] using missing.symm
  · simp

/-- Replay a buffered read at the kernel boundary. This relation records the
    syscall and slice, so changing the requested descriptor changes the run. -/
inductive Executes {Δ : List Cap} {A : Type} :
    Prefix Δ A → Machine → List StepSlice → A → Machine → Prop where
  | done (a : A) (m : Machine) : Executes (.done a) m [] a m
  | ask {op : SysOp} {h : op.cap ∈ Δ} {k : Ret op.Result → Prefix Δ A}
    {m sl reply next rest a z} (step : stepSyscall m sl op = (reply,next))
    (tail : Executes (k reply) next rest a z) :
    Executes (.ask op h k) m (sl::rest) a z

theorem Executes.bind {Δ : List Cap} {A B : Type} {p : Prefix Δ A} {m a next s}
    (x : Executes p m s a next) {f : A → Prefix Δ B} {t b z}
    (y : Executes (f a) next t b z) : Executes (p.bind f) m (s++t) b z := by
  induction x with
  | done => exact y
  | ask step _ ih => exact .ask step (ih y)

theorem Executes.run {Δ : List Cap} {A : Type} {p : Prefix Δ A} {m s a z}
    (x : Executes p m s a z) : runPrefix p m s = (.done a,z) := by
  induction x with
  | done => rfl
  | ask step tail ih => simp only [runPrefix,step]; exact ih

private theorem oneRead {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {r : BufReader} {m sl q next rest n result z}
    (awake : r.eof = false) (step : stepSyscall m sl (.read r.fd (max 1 r.chunkSize)) = (q,next))
    (tail : Executes (PosixProg.unfoldPrefix (readStep cap .all) n (r.receive q)) next rest result z) :
    Executes (PosixProg.unfoldPrefix (readStep cap .all) (n+1) (.ready r)) m (sl::rest) result z := by
  rw [PosixProg.unfoldPrefix]
  simp only [readStep, BufReader.inspect, awake, Bool.false_eq_true, ite_false]
  exact .ask step tail

private theorem readKernel {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {fd ino size bytes off m slices qs z} (t : FileReads fd ino size bytes off m slices qs z)
    (r : BufReader) (desc : r.fd = fd) (count : r.chunkSize = size) (awake : r.eof = false) :
    Executes ((PosixProg.unfold (.ready r) (readStep cap .all)).observe qs.length)
      m slices (.ok (some (r.pending ++ delivered qs)), {r.clear with eof := true}) z := by
  induction t generalizing r with
  | @eof off m sl z file step =>
    apply oneRead cap (n := 0) (q := .ok []) (next := z) awake (by rw [desc,count] <;> exact step)
    simp only [delivered, List.append_nil]
    exact .done _ _
  | @data off m sl next slices qs z b bs file step rest ih =>
    apply oneRead cap (n := qs.length) (q := .ok (b::bs)) (next := next) awake (by rw [desc,count] <;> exact step)
    have tail := ih (r.ingest (b::bs)) desc count awake
    have hc : (r.ingest (b::bs)).clear = r.clear := rfl
    rw [hc] at tail
    simpa [delivered, List.append_assoc, PosixProg.unfold, BufReader.receive] using tail
  | @interrupted off m sl slices qs z step rest ih =>
    apply oneRead cap (n := qs.length) (q := .err .EINTR) (next := m) awake (by rw [desc,count] <;> exact step)
    exact ih r desc count awake

/-- Under successful open and close and a progressing trace on a stationary
    regular inode, readFileAll executes against stepSyscall, returns the exact
    file, and restores every descriptor binding. Std.TreeMap balances internally,
    so FD-table identity is expressed by lookup at *every* descriptor number. -/
theorem readFileAll_refines_spec {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fs : .fsPathCap ∈ Δ)
    {m opened before closed : Machine} {fd ino size : Nat} {bytes : ByteArray}
    {path : Bytes} {slOpen slClose slices qs}
    (acquired : stepSyscall m slOpen (.openat none path {} 0) = (.ok fd,opened))
    (reads : FileReads fd ino size bytes 0 opened slices qs before)
    (released : stepSyscall before slClose (.close fd) = (.ok (),closed)) :
    runPrefix ((readFileAll cap fs path size).observe qs.length) m
        (slOpen :: (slices ++ [slClose])) = (.done (.ok bytes.data.toList),closed) ∧
    sameDescriptors closed m := by
  have data := reads.contents
  refine ⟨Executes.run ?_, close_restores (open_fresh acquired) data.2 (close_fds released)⟩
  let r : BufReader := {fd,chunkSize := size}
  have core := readKernel cap reads r rfl rfl rfl
  have hbytes : r.pending ++ delivered qs = bytes.data.toList := by simpa [r,BufReader.pending] using data.1
  rw [hbytes] at core
  have readRun : Executes ((readAll cap r).observe qs.length) opened slices
      (.ok bytes.data.toList,{r.clear with eof := true}) before := by
    rw [← List.append_nil slices]
    exact core.bind (.done _ _)
  let use : PosixProg Δ (Ret Bytes) := do return (← readAll cap r).1
  have useRun : Executes (use.observe qs.length) opened slices (.ok bytes.data.toList) before := by
    rw [← List.append_nil slices]
    exact readRun.bind (.done _ _)
  apply Executes.ask acquired
  exact useRun.bind (.ask released (.done _ _))

theorem readFileAll_open_error {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fs : .fsPathCap ∈ Δ)
    {m : Machine} {path : Bytes} {sl size depth} {e : Errno}
    (failed : stepSyscall m sl (.openat none path {} 0) = (.err e,m)) :
    runPrefix ((readFileAll cap fs path size).observe depth) m [sl] = (.done (.err e), m) :=
  Executes.run (.ask failed (.done _ _))

end LojitaCtx.Io.FsLib
