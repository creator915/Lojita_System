import LojitaCtx.Io.FileKernel
import LojitaCtx.Io.FdScope

namespace LojitaCtx.Io.FsLib
open LojitaCtx.Posix

/-- A completed trace of actual regular-file reads at a stationary inode.
    Offsets follow the number of bytes Linux returned, starting at zero after open. -/
inductive FileReads (fd ino size : Nat) (bytes : ByteArray) :
    Nat → Machine → List StepSlice → List (Ret Bytes) → Machine → Prop where
  | eof {off m sl z}
    (file : AtRegular m fd ino bytes off)
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.ok ([] : Bytes).toByteArray,z)) :
    FileReads fd ino size bytes off m [sl] [.ok []] z
  | data {off m sl next slices qs z b bs}
    (file : AtRegular m fd ino bytes off)
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.ok (b::bs).toByteArray,next))
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

theorem prefix_remaining (bs : Bytes) (n : Nat) :
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

theorem Executes.extend {Δ : List Cap} {A : Type} {p q : Prefix Δ A} {m s a z}
    (run : Executes p m s a z) (more : Prefix.Extends p q) : Executes q m s a z := by
  induction run generalizing q with
  | done => cases more; exact .done _ _
  | ask step tail ih =>
    cases more with
    | ask _ _ _ _ children => exact .ask step (ih (children _))

theorem Executes.withFd_body {Δ : List Cap} {A S : Type} (cap : .fdIoCap ∈ Δ)
    (acquire : FreeSys Δ (Ret Fd)) (use : Fd → PosixMachine Δ S (Ret A))
    {fd n m slices value before closed sl} (body : Executes ((use fd).observe n) m slices value before)
    (release : stepSyscall before sl (.close fd) = (.ok (), closed)) :
    Executes ((withFd cap acquire use).observeFrom (n+1) (some (fd,(use fd).init)))
      m (slices ++ [sl]) value closed := by
  have tail : Executes (closePrefix cap fd value) before [sl] value closed := by
    apply Executes.ask release
    cases value <;> exact .done _ _
  exact (body.bind tail).extend (withFd_body_extends cap acquire use fd n (use fd).init)

theorem Executes.run {Δ : List Cap} {A : Type} {p : Prefix Δ A} {m s a z}
    (x : Executes p m s a z) : runPrefix p m s = (.done a,z) := by
  induction x with
  | done => rfl
  | ask step tail ih => simp only [runPrefix,step]; exact ih

/-- A completed sequence of actual read syscalls. No hypothesis specifies the
    final machine or the payload of a successful read. -/
inductive MachineReads (fd size : Nat) : Machine → List StepSlice → List (Ret Bytes) → Machine → Prop where
  | eof {m sl z} (step : stepSyscall m sl (.read fd (max 1 size)) = (.ok ([] : Bytes).toByteArray,z)) :
    MachineReads fd size m [sl] [.ok []] z
  | data {m sl next slices qs z b bs}
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.ok (b::bs).toByteArray,next))
    (rest : MachineReads fd size next slices qs z) :
    MachineReads fd size m (sl::slices) (.ok (b::bs)::qs) z
  | interrupted {m sl next slices qs z}
    (step : stepSyscall m sl (.read fd (max 1 size)) = (.err .EINTR,next))
    (rest : MachineReads fd size next slices qs z) :
    MachineReads fd size m (sl::slices) (.err .EINTR::qs) z

theorem FileReads.machineReads {fd ino size bytes off m ss qs z} (r : FileReads fd ino size bytes off m ss qs z) :
    MachineReads fd size m ss qs z := by
  induction r with
  | eof _ step => exact .eof step
  | data _ step _ ih => exact .data step ih
  | interrupted step _ ih => exact .interrupted step ih

private theorem oneRead {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {r : BufReader} {m sl q next rest n result z}
    (awake : r.eof = false) (step : stepSyscall m sl (.read r.fd (max 1 r.chunkSize)) = (q.map List.toByteArray,next))
    (tail : Executes (PosixMachine.unfoldPrefix (readStep cap .all) n (r.receive q)) next rest result z) :
    Executes (PosixMachine.unfoldPrefix (readStep cap .all) (n+1) (.ready r)) m (sl::rest) result z := by
  rw [PosixMachine.unfoldPrefix]
  simp only [readStep, BufReader.inspect, awake, Bool.false_eq_true, ite_false]
  apply Executes.ask step
  change Executes (PosixMachine.unfoldPrefix (readStep cap .all) n (r.receivePacked (q.map List.toByteArray))) _ _ _ _
  rw [BufReader.receivePacked_list]
  exact tail

theorem readKernel {Δ : List Cap} (cap : .fdIoCap ∈ Δ)
    {fd size m slices qs z} (t : MachineReads fd size m slices qs z)
    (r : BufReader) (desc : r.fd = fd) (count : r.chunkSize = size) (awake : r.eof = false) :
    Executes ((PosixMachine.unfold (.ready r) (readStep cap .all)).observe qs.length)
      m slices (.ok (some (r.pending ++ delivered qs)), {r.clear with eof := true}) z := by
  rw [PosixMachine.observe_unfold]
  induction t generalizing r with
  | @eof m sl z step =>
    apply oneRead cap (n := 0) (q := .ok []) (next := z) awake (by rw [desc,count] <;> exact step)
    simp only [delivered, List.append_nil]
    exact .done _ _
  | @data m sl next slices qs z b bs step rest ih =>
    apply oneRead cap (n := qs.length) (q := .ok (b::bs)) (next := next) awake (by rw [desc,count] <;> exact step)
    have tail := ih (r.ingest (b::bs)) desc count awake
    have hc : (r.ingest (b::bs)).clear = r.clear := rfl
    rw [hc] at tail
    simpa [delivered, List.append_assoc, PosixMachine.unfold, BufReader.receive] using tail
  | @interrupted m sl next slices qs z step rest ih =>
    apply oneRead cap (n := qs.length) (q := .err .EINTR) (next := next) awake (by rw [desc,count] <;> exact step)
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
    runPrefix ((readFileAll cap fs path size).observe (qs.length+2)) m
        (slOpen :: (slices ++ [slClose])) = (.done (.ok bytes.data.toList),closed) ∧
    sameDescriptors closed m := by
  have data := reads.contents
  refine ⟨Executes.run ?_, close_restores (open_fresh acquired) data.2 (close_fds released)⟩
  let r : BufReader := {fd,chunkSize := size}
  have core := readKernel cap reads.machineReads r rfl rfl rfl
  have hbytes : r.pending ++ delivered qs = bytes.data.toList := by simpa [r,BufReader.pending] using data.1
  rw [hbytes] at core
  let use (i : Fd) := (readAll cap {fd := i, chunkSize := size}).map Prod.fst
  have readRun : Executes ((readAll cap r).observe qs.length) opened slices
      (.ok bytes.data.toList,{r.clear with eof := true}) before := by
    rw [readAll,readBytes,PosixMachine.observe_map,← List.append_nil slices]
    exact core.bind (.done _ _)
  have useRun : Executes ((use fd).observe qs.length) opened slices (.ok bytes.data.toList) before := by
    rw [show (use fd).observe qs.length = ((readAll cap r).observe qs.length).bind (fun a => .done a.1) from
      PosixMachine.observe_map _ _ _, ← List.append_nil slices]
    exact readRun.bind (.done _ _)
  apply Executes.ask acquired
  exact useRun.withFd_body cap (FreeSys.call (.openat none path {} 0) fs) use released

theorem readFileAll_open_error {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (fs : .fsPathCap ∈ Δ)
    {m : Machine} {path : Bytes} {sl size depth} {e : Errno}
    (failed : stepSyscall m sl (.openat none path {} 0) = (.err e,m)) :
    runPrefix ((readFileAll cap fs path size).observe (depth+1)) m [sl] = (.done (.err e), m) :=
  Executes.run (.ask failed (.done _ _))

end LojitaCtx.Io.FsLib
