import LojitaCtx.World

namespace LojitaCtx.ClockLaws
open Clock

theorem advanceClockZero (c : SimClock) : advanceClock 0 c = c := by simp [advanceClock]
theorem advanceClockAdd (a b : Nat) (c : SimClock) :
    advanceClock (a + b) c = advanceClock b (advanceClock a c) := by
  simp [advanceClock, Nat.add_left_comm, Nat.add_comm]
theorem advanceClockComm (a b : Nat) (c : SimClock) :
    advanceClock a (advanceClock b c) = advanceClock b (advanceClock a c) := by
  rw [← advanceClockAdd, ← advanceClockAdd, Nat.add_comm]
theorem advanceClockMonoLe (d : Nat) (c : SimClock) : c.monoMs ≤ (advanceClock d c).monoMs := Nat.le_add_left ..
theorem advanceClockWallLe (d : Nat) (c : SimClock) : c.wallEpochMs ≤ (advanceClock d c).wallEpochMs := Nat.le_add_left ..
theorem advanceClockTicks (d : Nat) (c : SimClock) : (advanceClock d c).autoTicks = c.autoTicks := rfl
theorem readMonoMonotonic (c : SimClock) : c.monoMs ≤ (readMonoMs c).1 := Nat.le_add_left ..
theorem readWallMonotonic (c : SimClock) : c.wallEpochMs ≤ (readWallMs c).1 := Nat.le_add_left ..
theorem readMonoIdle (m w : Nat) : readMonoMs ⟨m, w, []⟩ = (m, ⟨m, w, []⟩) := by simp [readMonoMs, tickClock, popTick]
theorem sleepClockZero (c : SimClock) : sleepClockMs 0 c = c := advanceClockZero c
theorem sleepClockAdd (a b : Nat) (c : SimClock) :
    sleepClockMs (a+b) c = sleepClockMs b (sleepClockMs a c) := advanceClockAdd a b c
export Clock (traceSimClockAppend)
end LojitaCtx.ClockLaws

namespace LojitaCtx.TermLaws
open Terminal

theorem stepANSINil (s : Screen) : stepANSI s [] = s := rfl
theorem stepANSICons (s : Screen) (b : Byte) (bs : Bytes) : stepANSI s (b :: bs) = stepANSI (ansiByte b s) bs := rfl
theorem stepANSIAppend (s : Screen) (a b : Bytes) : stepANSI s (a ++ b) = stepANSI (stepANSI s a) b :=
  List.foldl_append
theorem latestNothingLeft (x : Option Nat) : latest (fun _ => none) x = x := by cases x <;> rfl
theorem latestNothingRight (x : Option Nat) : latest (fun _ => x) none = x := rfl
theorem latestAssoc (a b c : Option Nat) : latest (fun _ => latest (fun _ => a) b) c = latest (fun _ => a) (latest (fun _ => b) c) := by cases c <;> rfl
theorem appendObsEmptyLeft (o : RawTermObs) : appendObs emptyObs o = o := by
  cases o; simp [appendObs, emptyObs, latestNothingLeft]
theorem appendObsEmptyRight (o : RawTermObs) : appendObs o emptyObs = o := by
  cases o; simp [appendObs, emptyObs, latestNothingRight]
theorem appendObsAssoc (a b c : RawTermObs) : appendObs (appendObs a b) c = appendObs a (appendObs b c) := by
  simp [appendObs, List.append_assoc, latestAssoc]
theorem pendingAdd (p : PendingOutput) (o : RawTermObs) :
    (p.add o).toObs = appendObs p.toObs o := by
  simp [PendingOutput.add, PendingOutput.toObs, appendObs, List.reverseAux_eq]

theorem advanceZero {S E : Type} (h : Handler S E) (m : TimedMachine S E) : advance 0 h m = m := rfl
theorem advanceAdd {S E : Type} (a b : Nat) (h : Handler S E) (m : TimedMachine S E) :
    advance (a+b) h m = advance b h (advance a h m) := by
  induction a generalizing m with
  | zero => simp [advance]
  | succ a ih => rw [Nat.succ_add]; exact ih _
theorem altScreenRoundtrip (s : Screen) (h : s.primary = none) : altScreen false (altScreen true s) = s := by
  cases s; cases h; rfl
end LojitaCtx.TermLaws

namespace LojitaCtx.FsLaws
open Terminal FsSandbox

theorem eqStrReflect (a b : String) : eqStr a b = true ↔ a = b := beq_iff_eq
theorem eqBytesReflect (xs ys : Bytes) : eqBytes xs ys = true ↔ xs = ys := beq_iff_eq
theorem eqCharsReflect (xs ys : List Char) : eqChars xs ys = true ↔ xs = ys := beq_iff_eq
theorem eqStrRefl (s : String) : eqStr s s = true := (eqStrReflect ..).2 rfl
theorem eqStrSym (s t : String) : eqStr s t = eqStr t s := BEq.comm
theorem lookupInsertSame (e : FsEntryObs) (es : List FsEntryObs) :
    lookupEntry e.entryPath (insertEntry e es) = some e := by
  induction es with
  | nil => simp [insertEntry, lookupEntry, eqStrRefl]
  | cons x xs ih =>
    simp only [insertEntry]
    split <;> first | simp [lookupEntry, eqStrRefl] | skip
    split <;> simp_all [lookupEntry, eqStrRefl]
theorem lookupInsertOther (p : String) (e : FsEntryObs) (es : List FsEntryObs) (h : p ≠ e.entryPath) :
    lookupEntry p (insertEntry e es) = lookupEntry p es := by
  induction es with
  | nil => simp [insertEntry, lookupEntry, eqStr, h]
  | cons x xs ih =>
    simp only [insertEntry]
    by_cases same : e.entryPath = x.entryPath
    · have hx : p ≠ x.entryPath := same ▸ h
      simp [eqStr, same, lookupEntry, hx]
    · simp only [eqStr, beq_iff_eq, same, ite_false]
      split <;> simp [lookupEntry, eqStr, h, ih]
theorem insertInsertSame (a b : FsEntryObs) (es : List FsEntryObs) (h : a.entryPath = b.entryPath) :
    insertEntry a (insertEntry b es) = insertEntry a es := by
  induction es with
  | nil => simp [insertEntry, eqStr, h]
  | cons x xs ih =>
    simp only [insertEntry, h]
    split
    · simp [insertEntry, eqStr, h]
    · split <;> simp_all [insertEntry, eqStr]

/-- A normalized relative leaf directly under the simulated root. -/
abbrev ValidFlatFile (p : String) : Prop :=
  World.normalizeRelPath p = p ∧ p ≠ "." ∧ validRelPath p = true ∧ parentPaths p = []
def CanWriteReg (p : String) (v : VirtualFs) : Prop :=
  ∀ e, lookupEntry p v.fsEntries = some e → e.entryKind = .regularNode
def NotSymlink (p : String) (v : VirtualFs) : Prop :=
  ∀ e, lookupEntry p v.fsEntries = some e → e.entryKind ≠ .symlinkNode

private theorem writeFlat (p : String) (bs : Bytes) (v : VirtualFs)
    (flat : ValidFlatFile p) (writable : CanWriteReg p v) :
    ∃ mode, World.writeVirtualFile p bs v = (.inr (), putEntry ⟨p, .regularNode, mode, bs⟩ v) := by
  obtain ⟨norm, dot, rel, root⟩ := flat
  rw [World.writeVirtualFile, World.writeVirtualFileFuel, norm]
  simp [eqStr, dot, rel, root, ensureParents]
  cases hl : lookupEntry p v.fsEntries with
  | none => exact ⟨420, rfl⟩
  | some e => exact ⟨e.entryMode, by simp [writable e hl, eqKind]⟩

theorem readAfterWriteSame (p : String) (bs : Bytes) (v : VirtualFs)
    (flat : ValidFlatFile p) (writable : CanWriteReg p v) :
    World.readVirtualFile p (World.writeVirtualFile p bs v).2 = .inr bs := by
  obtain ⟨mode, write⟩ := writeFlat p bs v flat writable
  obtain ⟨norm, dot, rel, _⟩ := flat
  rw [write, World.readVirtualFile, World.readVirtualFileFuel, norm]
  simp [eqStr, dot, rel, putEntry, lookupInsertSame ⟨p, .regularNode, mode, bs⟩ v.fsEntries, eqKind]

theorem readAfterWriteOther (p q : String) (bs : Bytes) (v : VirtualFs)
    (flatP : ValidFlatFile p) (flatQ : ValidFlatFile q) (different : q ≠ p)
    (writable : CanWriteReg p v) (ordinary : NotSymlink q v) :
    World.readVirtualFile q (World.writeVirtualFile p bs v).2 = World.readVirtualFile q v := by
  obtain ⟨mode, write⟩ := writeFlat p bs v flatP writable
  obtain ⟨norm, dot, rel, _⟩ := flatQ
  let e : FsEntryObs := ⟨p, .regularNode, mode, bs⟩
  rw [write]
  change World.readVirtualFile q (putEntry e v) = World.readVirtualFile q v
  unfold World.readVirtualFile
  conv => lhs; rw [World.readVirtualFileFuel, norm]
  conv => rhs; rw [World.readVirtualFileFuel, norm]
  simp only [eqStr, beq_iff_eq, dot, rel, Bool.not_true, Bool.false_eq_true, ite_false, putEntry,
    lookupInsertOther q e v.fsEntries different]
  cases hl : lookupEntry q v.fsEntries with
  | none => rfl
  | some entry =>
    have hs := ordinary entry hl
    cases hk : entry.entryKind with
    | regularNode => simp [hk, eqKind]
    | dirNode => simp [hk, eqKind]
    | symlinkNode => exact (hs hk).elim

end LojitaCtx.FsLaws

namespace LojitaCtx.GitLaws
open GitSandbox

theorem lookupNamePutNameSame {A : Type} (p : String) (v : A) (m : List (String × A)) :
    lookupName p (putName p v m) = some v := by
  induction m with
  | nil => simp [putName, lookupName, FsSandbox.eqStr]
  | cons x xs ih => simp only [putName]; split <;> simp_all [lookupName, FsSandbox.eqStr]
theorem lookupNamePutNameOther {A : Type} (p q : String) (v : A) (m : List (String × A)) (h : p ≠ q) :
    lookupName p (putName q v m) = lookupName p m := by
  induction m with
  | nil => simp [putName, lookupName, FsSandbox.eqStr, h]
  | cons x xs ih => simp only [putName]; split <;> simp_all [lookupName, FsSandbox.eqStr]
theorem stepPureGitStatusId (r : PureGitRepo) : stepPureGit .gitStatus r = (r, some (projectSummary r)) := rfl
theorem stepPureGitStageAllIndex (r : PureGitRepo) : (stepPureGit .gitStageAll r).1.index = r.worktree := rfl
theorem stepPureGitStageAllHead (r : PureGitRepo) : (stepPureGit .gitStageAll r).1.headBranch = r.headBranch := rfl
theorem stepPureGitStageAllModifiedEmpty (r : PureGitRepo) :
    (projectSummary (stepPureGit .gitStageAll r).1).modifiedPaths = [] := by
  change choosePaths (fun p => !(eqMaybeBytes (lookupName p r.worktree) (lookupName p r.worktree))) _ = []
  have same (p : String) : eqMaybeBytes (lookupName p r.worktree) (lookupName p r.worktree) = true := by
    cases lookupName p r.worktree <;> simp [eqMaybeBytes, FsSandbox.eqBytes]
  have clean (ps : List String) : choosePaths (fun p => !(eqMaybeBytes (lookupName p r.worktree) (lookupName p r.worktree))) ps = [] := by
    induction ps with
    | nil => rfl
    | cons p ps ih => rw [choosePaths, same]; exact ih
  exact clean _
theorem runPureGitNil (r : PureGitRepo) : runPureGit [] r = r := rfl
theorem runPureGitAppend (xs ys : List GitStep) (r : PureGitRepo) :
    runPureGit (xs ++ ys) r = runPureGit ys (runPureGit xs r) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => exact ih _
end LojitaCtx.GitLaws

namespace LojitaCtx.NetLaws
open Terminal NetSandbox

theorem prefixBytesAppend (xs ys : Bytes) : prefixBytes xs (xs ++ ys) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [prefixBytes, FsSandbox.prefixBytes] using ih
theorem prefixBytesRefl (xs : Bytes) : prefixBytes xs xs = true := by simpa using prefixBytesAppend xs []
theorem dropLengthAppend (xs ys : Bytes) : (xs ++ ys).drop xs.length = ys := by simp
theorem evalStubExchangeReqs (mode : NetTopology) (reqs : List Bytes) : (evalStubExchange mode reqs).1 = reqs := rfl
theorem evalStubExchangeAppend (mode : NetTopology) (xs ys : List Bytes) :
    (evalStubExchange mode (xs ++ ys)).2 = (evalStubExchange mode xs).2 ++ (evalStubExchange mode ys).2 := by
  simp [evalStubExchange]
end LojitaCtx.NetLaws
