import LojitaCtx.FsSandbox

namespace LojitaCtx.GitSandbox

open LojitaCtx.Terminal

structure GitConfig : Type where gitConfig ::
  target : SandboxTarget
  defaultBranch : String
  authorName : String
  authorEmail : String
  baseEpochSec : Nat
  envVars : List (String × String)
  ownedFiles : List String

inductive GitStep : Type where
  | gitWriteFile    : String → Bytes → GitStep
  | gitRemoveFile   : String → GitStep
  | gitStageAll     : GitStep
  | gitStagePaths   : List String → GitStep
  | gitCommit       : String → Nat → GitStep
  | gitSwitchBranch : String → Bool → GitStep
  | gitCreateTag    : String → GitStep
  | gitStatus       : GitStep
  | gitRunTarget    : String → List String → Bytes → Nat → GitStep

structure GitRepoSummary : Type where
  gitSummary ::
  currentBranch  : String
  commitCount    : Nat
  branchNames    : List String
  tagNames       : List String
  stagedPaths    : List String
  modifiedPaths  : List String
  untrackedPaths : List String

structure RawGitObs : Type where
  rawGitObs ::
  stdoutOut  : Bytes
  stderrOut  : Bytes
  commitHash : String
  exitStatus : Option Nat
  timedOut   : Bool
  summary    : Option GitRepoSummary

def validGitPath (p : String) : Bool :=
  match FsSandbox.segments p with
  | [] => false
  | first :: _ => FsSandbox.validRelPath p && Bool.not (FsSandbox.eqStr first ".git")

def refChar (c : Char) : Bool :=
  let n := Char.toNat c
  47 < n && n < 58 ||
    (64 < n && n < 91 || (96 < n && n < 123 || (n == 45 || (n == 95 || (n == 46 || n == 47)))))

def noDoubleDot : List Char → Bool
  | [] => true
  | [_] => true
  | a :: b :: cs => Bool.not (Char.toNat a == 46 && Char.toNat b == 46) && noDoubleDot (b :: cs)
termination_by structural cs => cs

def validRefPart (p : String) : Bool :=
  match String.toList p with
  | [] => false
  | c :: _ =>
    Bool.not (Char.toNat c == 46) &&
      (Bool.not (FsSandbox.prefixBytes (bytes ".") (List.reverse (bytes p))) &&
        Bool.not (FsSandbox.prefixBytes (List.reverse (bytes ".lock")) (List.reverse (bytes p))))

def validRefName (p : String) : Bool :=
  match String.toList p with
  | [] => false
  | c :: cs =>
    Bool.not (Char.toNat c == 45) &&
      (FsSandbox.validRelPath p &&
        (FsSandbox.all refChar (c :: cs) &&
          (noDoubleDot (c :: cs) &&
            (FsSandbox.all validRefPart (FsSandbox.segments p) &&
              Bool.not (FsSandbox.prefixBytes (bytes ".") (List.reverse (bytes p)))))))

def validBranch (p : String) : Bool :=
  validRefName p && Bool.not (FsSandbox.eqStr p "HEAD")

abbrev GitTree : Type :=
  List (String × Bytes)

structure PureCommit : Type where
  pureCommit ::
  parentIndex   : Option Nat
  treeSnapshot  : GitTree
  commitMessage : String
  timestamp     : Nat

structure PureGitRepo : Type where pureGitRepo ::
  config : GitConfig
  worktree : GitTree
  index : GitTree
  commits : Array PureCommit
  branchMap : List (String × Option Nat)
  headBranch : String
  tagMap : List (String × Nat)

def lookupName {A : Type} (p : String) : List (String × A) → Option A
  | [] => .none
  | qx :: xs => if FsSandbox.eqStr p qx.1 then .some qx.2 else lookupName p xs
termination_by structural xs => xs

def putName {A : Type} (p : String) (x : A) : List (String × A) → List (String × A)
  | [] => [Prod.mk p x]
  | qy :: xs => if FsSandbox.eqStr p qy.1 then Prod.mk p x :: xs else qy :: putName p x xs
termination_by structural xs => xs

def removeName {A : Type} (p : String) : List (String × A) → List (String × A)
  | [] => []
  | qx :: xs => if FsSandbox.eqStr p qx.1 then xs else qx :: removeName p xs
termination_by structural xs => xs

def present {A : Type} : Option A → Bool
  | .none => false
  | .some _  => true

def eqMaybeBytes : Option Bytes → Option Bytes → Bool
  | .none, .none => true
  | .some a,  .some b  => FsSandbox.eqBytes a b
  | _,        _        => false

def insertPath (p : String) : List String → List String
  | [] => [p]
  | q :: qs =>
    if FsSandbox.eqStr p q then q :: qs
    else if FsSandbox.ltBytes (bytes p) (bytes q) then p :: q :: qs else q :: insertPath p qs
termination_by structural qs => qs

def sortPaths : List String → List String
  | []      => []
  | p :: ps => insertPath p (sortPaths ps)
termination_by structural ps => ps

def choosePaths (f : String → Bool) : List String → List String
  | []      => []
  | p :: ps => (if (f p) then (p :: choosePaths f ps) else (choosePaths f ps))
termination_by structural ps => ps

def nthCommit (n : Nat) (cs : Array PureCommit) := cs[n]?

def headIndex (r : PureGitRepo) : Option Nat :=
  match lookupName r.headBranch r.branchMap with
  | .none => .none
  | .some n  => n

def treeAt : Option Nat → Array PureCommit → GitTree
  | .none, _  => []
  | .some n,  cs =>
      match nthCommit n cs with
      | .none => []
      | .some c  => c.treeSnapshot

def headTree (r : PureGitRepo) : GitTree :=
  treeAt (headIndex r) r.commits

def countParents : Nat → Option Nat → Array PureCommit → Nat
  | 0,          _,        _  => 0
  | Nat.succ _, .none, _  => 0
  | Nat.succ f, .some n,  cs =>
      match nthCommit n cs with
      | .none => 0
      | .some c  => Nat.succ (countParents f c.parentIndex cs)
termination_by structural f _ _ => f

def changedPaths (a b : GitTree) : List String :=
  choosePaths (fun p => Bool.not (eqMaybeBytes (lookupName p a) (lookupName p b)))
    (sortPaths (List.map Prod.fst a ++ List.map Prod.fst b))

def liveBranches : List (String × Option Nat) → List String
  | [] => []
  | ⟨_, .none⟩ :: bs => liveBranches bs
  | ⟨p, .some _⟩ :: bs => p :: liveBranches bs
termination_by structural bs => bs

def projectSummary (r : PureGitRepo) : GitRepoSummary :=
  GitRepoSummary.gitSummary
    r.headBranch
    (countParents (r.commits.size) (headIndex r) r.commits)
    (sortPaths (liveBranches r.branchMap))
    (sortPaths (List.map Prod.fst r.tagMap))
    (changedPaths (headTree r) r.index)
    (choosePaths (fun p => Bool.not (eqMaybeBytes (lookupName p r.worktree) (lookupName p r.index)))
      (sortPaths (List.map Prod.fst r.index)))
    (choosePaths (fun p => Bool.not (present (lookupName p r.index)))
      (sortPaths (List.map Prod.fst r.worktree)))

def initTree : List String → List Bytes → GitTree
  | [], _             => []
  | p :: ps, []       => Prod.mk p [] :: initTree ps []
  | p :: ps, b :: bs  => Prod.mk p b  :: initTree ps bs
termination_by structural ps _ => ps

def initPureGit (cfg : GitConfig) (bs : List Bytes) : PureGitRepo :=
  PureGitRepo.pureGitRepo cfg
    (if FsSandbox.all validGitPath cfg.ownedFiles && FsSandbox.noPathCollisions cfg.ownedFiles then
      initTree cfg.ownedFiles bs
    else [])
    [] #[] [Prod.mk cfg.defaultBranch .none] cfg.defaultBranch []

def writeTree (p : String) (b : Bytes) (t : GitTree) : GitTree :=
  if
      validGitPath p &&
        FsSandbox.all (fun q => FsSandbox.eqStr p q.1 || Bool.not (FsSandbox.collide p q.1)) t then
    putName p b t
  else t

def pathSelected : List String → String → Bool
  | [], _ => false
  | q :: qs, p => FsSandbox.eqStr p q || (FsSandbox.isParent q p || pathSelected qs p)
termination_by structural qs _ => qs

private def chooseEntries (f : String → Bool) : GitTree → GitTree
  | []         => []
  | pb :: rest => (if (f pb.1) then (pb :: chooseEntries f rest) else (chooseEntries f rest))
termination_by structural rest => rest

def stageSelected (ps : List String) (w i : GitTree) : GitTree :=
  chooseEntries (fun p => Bool.not (pathSelected ps p)) i ++ chooseEntries (pathSelected ps) w

private def hasTreePath (p : String) : GitTree → Bool
  | [] => false
  | qb :: rest => FsSandbox.eqStr p qb.1 || (FsSandbox.isParent p qb.1 || hasTreePath p rest)
termination_by structural rest => rest

def allStagePathsExist : List String → GitTree → GitTree → Bool
  | [], _, _ => true
  | p :: ps, w, i => hasTreePath p (w ++ i) && allStagePathsExist ps w i
termination_by structural ps _ _ => ps

def checkoutSafe (old next staged working : GitTree) : Bool :=
  let safe (p : String) : Bool :=
    eqMaybeBytes (lookupName p old) (lookupName p next) ||
      (eqMaybeBytes (lookupName p staged) (lookupName p next) ||
        eqMaybeBytes (lookupName p staged) (lookupName p old) &&
          eqMaybeBytes (lookupName p working) (lookupName p staged))
  FsSandbox.all safe
    (sortPaths (List.map Prod.fst old ++ (List.map Prod.fst next ++ List.map Prod.fst staged)))

def carryTree (old next staged : GitTree) : GitTree → List String → GitTree
  | working, [] => working
  | working, p :: ps =>
    let keep :=
      eqMaybeBytes (lookupName p old) (lookupName p next) ||
        eqMaybeBytes (lookupName p staged) (lookupName p next)
    let working' :=
      match keep with
      | true => working
      | false =>
        match lookupName p next with
        | .none => removeName p working
        | .some b => putName p b working
    carryTree old next staged working' ps
termination_by structural _ ps => ps

def checkoutExisting (name : String) (dest : Option Nat) (r : PureGitRepo) : PureGitRepo :=
  let old := headTree r
  let next := treeAt dest r.commits
  let paths :=
    sortPaths (List.map Prod.fst old ++ (List.map Prod.fst next ++ List.map Prod.fst r.index))
  let nextIndex := carryTree old next r.index r.index paths
  let nextWorktree := carryTree old next r.index r.worktree paths
  if
      checkoutSafe old next r.index r.worktree &&
        (FsSandbox.noPathCollisions (List.map Prod.fst nextIndex) &&
          FsSandbox.noPathCollisions (List.map Prod.fst nextWorktree)) then
    { r with headBranch := name, index := nextIndex, worktree := nextWorktree }
  else r

def newBranchMap (r : PureGitRepo) : List (String × Option Nat) :=
  match headIndex r with
  | .none => removeName r.headBranch r.branchMap
  | .some _ => r.branchMap

def switchBranch (name : String) (create : Bool) (r : PureGitRepo) : PureGitRepo :=
  match validBranch name, lookupName name r.branchMap with
  | false, _ => r
  | true, .some dest => if create then r else checkoutExisting name dest r
  | true, .none =>
    if
        create &&
          FsSandbox.all (fun p => Bool.not (FsSandbox.collide name p.1)) (newBranchMap r) then
      { r with headBranch := name, branchMap := putName name (headIndex r) (newBranchMap r) }
    else r

def createTag (name : String) (r : PureGitRepo) : PureGitRepo :=
  match headIndex r with
  | .none => r
  | .some n =>
    if
        validRefName name &&
          FsSandbox.all (fun p => Bool.not (FsSandbox.collide name p.1)) r.tagMap then
      { r with tagMap := putName name n r.tagMap }
    else r

def commitTree (msg : String) (offset : Nat) (r : PureGitRepo) : PureGitRepo :=
  let changed := Bool.not (List.length (changedPaths (headTree r) r.index) == 0)
  if
      Bool.not (FsSandbox.eqStr msg "") &&
        (FsSandbox.all (fun c => Bool.not (Char.toNat c == 0)) (String.toList msg) && changed) then
    {
      r with
      commits :=
        r.commits.push ⟨headIndex r, r.index, msg, r.config.baseEpochSec + offset⟩
      branchMap := putName r.headBranch (.some (r.commits.size)) r.branchMap }
  else r

def stepPureGit : GitStep → PureGitRepo → PureGitRepo × Option GitRepoSummary
  | .gitWriteFile p bs, r => Prod.mk { r with worktree := writeTree p bs r.worktree } .none
  | .gitRemoveFile p, r =>
    Prod.mk (if validGitPath p then { r with worktree := removeName p r.worktree } else r) .none
  | .gitStageAll, r => Prod.mk { r with index := r.worktree } .none
  | .gitStagePaths ps, r =>
    Prod.mk
      (if FsSandbox.all validGitPath ps && allStagePathsExist ps r.worktree r.index then
        { r with index := stageSelected ps r.worktree r.index }
      else r)
      .none
  | .gitCommit msg offset, r => Prod.mk (commitTree msg offset r) .none
  | .gitSwitchBranch name create, r => Prod.mk (switchBranch name create r) .none
  | .gitCreateTag name, r => Prod.mk (createTag name r) .none
  | .gitStatus, r => Prod.mk r (.some (projectSummary r))
  | .gitRunTarget _ _ _ _, r => Prod.mk r .none

def runPureGit : List GitStep → PureGitRepo → PureGitRepo
  | [], r      => r
  | q :: qs, r => runPureGit qs (stepPureGit q r).1
termination_by structural qs _ => qs

def eqStrings : List String → List String → Bool
  | [], [] => true
  | a :: as, b :: bs => FsSandbox.eqStr a b && eqStrings as bs
  | _, _ => false
termination_by structural as _ => as

def eqGitSummary (a b : GitRepoSummary) : Bool :=
  FsSandbox.eqStr a.currentBranch b.currentBranch &&
    (a.commitCount == b.commitCount &&
      (eqStrings a.branchNames b.branchNames &&
        (eqStrings a.tagNames b.tagNames &&
          (eqStrings a.stagedPaths b.stagedPaths &&
            (eqStrings a.modifiedPaths b.modifiedPaths &&
              eqStrings a.untrackedPaths b.untrackedPaths)))))

end LojitaCtx.GitSandbox
