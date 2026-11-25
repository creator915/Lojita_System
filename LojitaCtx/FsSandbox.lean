import LojitaCtx.Terminal

namespace LojitaCtx.FsSandbox

open LojitaCtx.Terminal

def eqChars (xs ys : List Char) : Bool := xs == ys

def eqStr (a b : String) : Bool := a == b

def splitSegmentChars : List Char → List Char → List (List Char)
  | acc, [] => [List.reverse acc]
  | acc, c :: cs =>
    if Char.toNat c == 47 then List.reverse acc :: splitSegmentChars [] cs
    else splitSegmentChars (c :: acc) cs
termination_by structural _ cs => cs

def segments (p : String) : List String :=
  List.map String.ofList (splitSegmentChars [] (String.toList p))

def all {A : Type} (f : A → Bool) : List A → Bool
  | [] => true
  | x :: xs => f x && all f xs
termination_by structural xs => xs

def validSegChars (cs : List Char) : Bool :=
  Bool.not (eqChars cs []) && (Bool.not (eqChars cs ['.']) && Bool.not (eqChars cs ['.', '.']))

def validSegment (s : String) : Bool :=
  validSegChars (String.toList s)

def validRelPath (p : String) : Bool :=
  all validSegChars (splitSegmentChars [] (String.toList p)) &&
    all (fun c => Bool.not (Char.toNat c == 0)) (String.toList p)

def eqBytes (xs ys : Bytes) : Bool := xs == ys

def ltBytes : Bytes → Bytes → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if UInt8.toNat a == UInt8.toNat b then ltBytes as bs else UInt8.toNat a < UInt8.toNat b
termination_by structural as _ => as

def prefixBytes : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => UInt8.toNat a == UInt8.toNat b && prefixBytes as bs
termination_by structural as _ => as

def isParent (p q : String) : Bool :=
  prefixBytes (bytes (p ++ "/")) (bytes q)

def collide (p q : String) : Bool :=
  eqStr p q || (isParent p q || isParent q p)

def noPathCollisions : List String → Bool
  | [] => true
  | p :: ps => validRelPath p && (all (fun q => Bool.not (collide p q)) ps && noPathCollisions ps)
termination_by structural ps => ps

def maskMode (n : Nat) : Nat :=
  (n % 512)

inductive FsNodeKind : Type where
  | regularNode : FsNodeKind
  | dirNode     : FsNodeKind
  | symlinkNode : FsNodeKind

inductive FsFixture : Type where
  | fixDir     : String → Nat → FsFixture
  | fixFile    : String → Nat → Bytes → FsFixture
  | fixSymlink : String → String → FsFixture

structure FsConfig : Type where fsConfig ::
  target : SandboxTarget
  envVars : List (String × String)
  ownedFiles : List String
  fixtures : List FsFixture

inductive FsStep : Type where
  | runCmd        : String → List String → Bytes → Nat → FsStep
  | writeFileStep : String → Bytes → FsStep
  | mkdirStep     : String → Nat → FsStep
  | symlinkStep   : String → String → FsStep
  | chmodStep     : String → Nat → FsStep
  | unlinkStep    : String → FsStep
  | snapshotStep  : FsStep

structure FsEntryObs : Type where
  fsEntry ::
  entryPath  : String
  entryKind  : FsNodeKind
  entryMode  : Nat
  entryBytes : Bytes

structure RawFsObs : Type where
  rawFsObs ::
  stdoutOut  : Bytes
  stderrOut  : Bytes
  exitStatus : Option Nat
  timedOut   : Bool
  entries    : List FsEntryObs

def emptyFsObs : RawFsObs :=
  RawFsObs.rawFsObs [] [] .none false []

def rejectedFsObs : RawFsObs :=
  RawFsObs.rawFsObs [] (bytes "filesystem operation rejected") (.some 1) false []

def eqKind : FsNodeKind → FsNodeKind → Bool
  | .regularNode, .regularNode => true
  | .dirNode,     .dirNode     => true
  | .symlinkNode, .symlinkNode => true
  | _,            _            => false

def eqEntry (a b : FsEntryObs) : Bool :=
  eqStr a.entryPath b.entryPath &&
    (eqKind a.entryKind b.entryKind &&
      (a.entryMode == b.entryMode && eqBytes a.entryBytes b.entryBytes))

def eqEntries : List FsEntryObs → List FsEntryObs → Bool
  | [], [] => true
  | a :: as, b :: bs => eqEntry a b && eqEntries as bs
  | _, _ => false
termination_by structural as _ => as

def eqExit : Option Nat → Option Nat → Bool
  | .none, .none => true
  | .some a,  .some b  => (a == b)
  | _,        _        => false

def eqBool : Bool → Bool → Bool
  | true,  true  => true
  | false, false => true
  | _,     _     => false

def eqObs (a b : RawFsObs) : Bool :=
  eqBytes a.stdoutOut b.stdoutOut &&
    (eqBytes a.stderrOut b.stderrOut &&
      (eqExit a.exitStatus b.exitStatus &&
        (eqBool a.timedOut b.timedOut && eqEntries a.entries b.entries)))

def eqTrace : List RawFsObs → List RawFsObs → Bool
  | [], [] => true
  | a :: as, b :: bs => eqObs a b && eqTrace as bs
  | _, _ => false
termination_by structural as _ => as

structure VirtualFs : Type where
  virtualFs ::
  fsEntries : List FsEntryObs

def lookupEntry (p : String) : List FsEntryObs → Option FsEntryObs
  | []      => .none
  | e :: es => (if (eqStr p e.entryPath) then (.some e) else (lookupEntry p es))
termination_by structural es => es

def insertEntry (e : FsEntryObs) : List FsEntryObs → List FsEntryObs
  | [] => [e]
  | x :: xs =>
    if eqStr e.entryPath x.entryPath then e :: xs
    else
      if ltBytes (bytes e.entryPath) (bytes x.entryPath) then e :: x :: xs
      else x :: insertEntry e xs
termination_by structural xs => xs

def removeEntry (p : String) : List FsEntryObs → List FsEntryObs
  | []      => []
  | x :: xs => (if (eqStr p x.entryPath) then xs else (x :: removeEntry p xs))
termination_by structural xs => xs

def putEntry (e : FsEntryObs) (v : VirtualFs) : VirtualFs :=
  VirtualFs.virtualFs (insertEntry e v.fsEntries)

def joinPart (p q : String) : String :=
  if eqStr p "" then q else p ++ ("/" ++ q)

def parentsFrom : String → List String → List String
  | _, []            => []
  | _, [_]           => []
  | p, x :: y :: xs  =>
      let px := joinPart p x
      px :: parentsFrom px (y :: xs)
termination_by structural _ xs => xs

def parentPaths (p : String) : List String :=
  parentsFrom "" (segments p)

def ensureParents (create : Bool) : List String → VirtualFs → Option VirtualFs
  | [], v      => .some v
  | p :: ps, v =>
      match lookupEntry p v.fsEntries with
      | .some e  => (if (eqKind e.entryKind .dirNode) then (ensureParents create ps v) else .none)
      | .none => (if create then (ensureParents create ps (putEntry (FsEntryObs.fsEntry p .dirNode 493 []) v)) else .none)
termination_by structural ps _ => ps

def prepare (create : Bool) (p : String) (v : VirtualFs) : Option VirtualFs :=
  (if (validRelPath p) then (ensureParents create (parentPaths p) v) else .none)

def writeLeaf (p : String) (bs : Bytes) (v : VirtualFs) : Option VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .none => .some (putEntry (FsEntryObs.fsEntry p .regularNode 420 bs) v)
  | .some e  =>
      (if (eqKind e.entryKind .regularNode) then (.some (putEntry (FsEntryObs.fsEntry p .regularNode e.entryMode bs) v)) else .none)

def mkdirLeaf (p : String) (mode : Nat) (v : VirtualFs) : Option VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .none => .some (putEntry (FsEntryObs.fsEntry p .dirNode (maskMode mode) []) v)
  | .some e  =>
      (if (eqKind e.entryKind .dirNode) then (.some (putEntry (FsEntryObs.fsEntry p .dirNode (maskMode mode) []) v)) else .none)

def linkLeaf (p dest : String) (v : VirtualFs) : Option VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .none => .some (putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v)
  | .some e  =>
      (if (eqKind e.entryKind .dirNode) then .none else (.some (putEntry (FsEntryObs.fsEntry p .symlinkNode 511 (bytes dest)) v)))

def chmodLeaf (p : String) (mode : Nat) (v : VirtualFs) : Option VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .none => .none
  | .some e  =>
      (if (eqKind e.entryKind .symlinkNode) then .none else (.some (putEntry (FsEntryObs.fsEntry p e.entryKind (maskMode mode) e.entryBytes) v)))

def unlinkLeaf (p : String) (v : VirtualFs) : Option VirtualFs :=
  match lookupEntry p v.fsEntries with
  | .none => .none
  | .some _  =>
      (if (all (fun x => Bool.not (isParent p x.entryPath)) v.fsEntries) then (.some (VirtualFs.virtualFs (removeEntry p v.fsEntries))) else .none)

def bindMaybe {A B : Type} : Option A → (A → Option B) → Option B
  | .none, _ => .none
  | .some x,  f => f x

def applyFs : FsStep → VirtualFs → Option VirtualFs
  | .writeFileStep p bs, v => bindMaybe (prepare true p v) (writeLeaf p bs)
  | .mkdirStep p mode, v => bindMaybe (prepare true p v) (mkdirLeaf p mode)
  | .symlinkStep p dest, v =>
    if
        all (fun c => Bool.not (Char.toNat c == 0)) (String.toList dest) &&
          Bool.not (eqStr dest "") then
      bindMaybe (prepare true p v) (linkLeaf p dest)
    else .none
  | .chmodStep p mode, v => bindMaybe (prepare false p v) (chmodLeaf p mode)
  | .unlinkStep p, v => bindMaybe (prepare false p v) (unlinkLeaf p)
  | _, v => .some v

abbrev CmdSemantics : Type :=
  String → List String → Bytes → Nat → VirtualFs → VirtualFs × Bytes × Bytes × Nat × Bool

def noopCmd : CmdSemantics :=
  fun _ _ _ _ v =>
    Prod.mk v (Prod.mk [] (Prod.mk [] (Prod.mk 0 false)))

def finishFs (old : VirtualFs) : Option VirtualFs → (VirtualFs × RawFsObs)
  | .none   => Prod.mk old rejectedFsObs
  | .some next => Prod.mk next emptyFsObs

def stepVirtualFs (cmd : CmdSemantics) : FsStep → VirtualFs → (VirtualFs × RawFsObs)
  | .runCmd exe args input ms, v =>
      let r := cmd exe args input ms v
      let next    := r.1
      let out     := r.2.1
      let err     := r.2.2.1
      let status  := r.2.2.2.1
      let timeout := r.2.2.2.2
      Prod.mk next (RawFsObs.rawFsObs out err (.some status) timeout [])
  | .snapshotStep, v =>
      Prod.mk v (RawFsObs.rawFsObs [] [] .none false v.fsEntries)
  | q, v =>
      finishFs v (applyFs q v)

def traceVirtualFs (cmd : CmdSemantics) : List FsStep → VirtualFs → List RawFsObs
  | [], _      => []
  | q :: qs, v =>
      let r := stepVirtualFs cmd q v
      r.2 :: traceVirtualFs cmd qs r.1
termination_by structural qs _ => qs

def retain (old : VirtualFs) : Option VirtualFs → VirtualFs
  | .none => old
  | .some v  => v

def initOwned : List String → List Bytes → VirtualFs → VirtualFs
  | [], _, v            => v
  | p :: ps, [], v      => initOwned ps [] (retain v (applyFs (.writeFileStep p []) v))
  | p :: ps, b :: bs, v => initOwned ps bs (retain v (applyFs (.writeFileStep p b) v))
termination_by structural ps _ _ => ps

def initDirs : List FsFixture → VirtualFs → VirtualFs
  | [], v                    => v
  | .fixDir p mode :: fs, v  => initDirs fs (retain v (applyFs (.mkdirStep p mode) v))
  | _ :: fs, v               => initDirs fs v
termination_by structural fs _ => fs

def initFixtures : List FsFixture → VirtualFs → VirtualFs
  | [], v                          => v
  | .fixFile p mode bs :: fs, v    =>
      initFixtures fs (retain v (bindMaybe (applyFs (.writeFileStep p bs) v) (chmodLeaf p mode)))
  | .fixSymlink p dest :: fs, v    =>
      initFixtures fs (retain v (applyFs (.symlinkStep p dest) v))
  | _ :: fs, v                     => initFixtures fs v
termination_by structural fs _ => fs

def initVirtualFs (cfg : FsConfig) (contents : List Bytes) : VirtualFs :=
  initFixtures cfg.fixtures
    (initOwned cfg.ownedFiles contents (initDirs cfg.fixtures (VirtualFs.virtualFs [])))

inductive FsDiff : Type where
  | added    : String → FsDiff
  | modified : String → FsDiff
  | removed  : String → FsDiff

def diffSnapshot : List FsEntryObs → List FsEntryObs → List FsDiff
  | [], ys => ys.map (fun y => .added y.entryPath)
  | x :: xs, ys =>
    let after := diffSnapshot xs
    let rec scan : List FsEntryObs → List FsDiff
      | [] => .removed x.entryPath :: after []
      | y :: rest =>
        if eqStr x.entryPath y.entryPath then
          if eqEntry x y then after rest else .modified x.entryPath :: after rest
        else if ltBytes (bytes x.entryPath) (bytes y.entryPath) then
          .removed x.entryPath :: after (y :: rest)
        else .added y.entryPath :: scan rest
      termination_by structural zs => zs
    scan ys
termination_by structural xs _ => xs
end LojitaCtx.FsSandbox
