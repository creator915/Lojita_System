{-# OPTIONS --safe #-}
module Context.Tools.GitSandbox where

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; length; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)
open import Context.Tools.FsSandbox using (all; segments; validRelPath; noPathCollisions; collide; isParent; eqBytes; ltBytes; prefixBytes)

record GitConfig : Set where
  constructor gitConfig
  field
    target : SandboxTarget
    defaultBranch authorName authorEmail : String
    baseEpochSec : ℕ
    envVars : List (String × String)
    ownedFiles : List String
open GitConfig public

data GitStep : Set where
  gitWriteFile : String → Bytes → GitStep
  gitRemoveFile : String → GitStep
  gitStageAll : GitStep
  gitStagePaths : List String → GitStep
  gitCommit : String → ℕ → GitStep
  gitSwitchBranch : String → Bool → GitStep
  gitCreateTag : String → GitStep
  gitStatus : GitStep
  gitRunTarget : String → List String → Bytes → ℕ → GitStep

record GitRepoSummary : Set where
  constructor gitSummary
  field
    currentBranch : String
    commitCount : ℕ
    branchNames tagNames stagedPaths modifiedPaths untrackedPaths : List String
open GitRepoSummary public

record RawGitObs : Set where
  constructor rawGitObs
  field
    stdoutOut stderrOut : Bytes
    commitHash : String
    exitStatus : Maybe ℕ
    timedOut : Bool
    summary : Maybe GitRepoSummary
open RawGitObs public

validGitPath : String → Bool
validGitPath p with segments p
... | [] = false
... | first ∷ rest = validRelPath p ∧ not (primStringEquality first ".git")

refChar : Char → Bool
refChar c = ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))
  ∨ ((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 91))
  ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 123))
  ∨ (toℕ c ≡ᵇ 45) ∨ (toℕ c ≡ᵇ 95) ∨ (toℕ c ≡ᵇ 46) ∨ (toℕ c ≡ᵇ 47)

noDoubleDot : List Char → Bool
noDoubleDot [] = true
noDoubleDot (_ ∷ []) = true
noDoubleDot (a ∷ b ∷ cs) = not ((toℕ a ≡ᵇ 46) ∧ (toℕ b ≡ᵇ 46)) ∧ noDoubleDot (b ∷ cs)

validRefPart : String → Bool
validRefPart p with toList p
... | [] = false
... | c ∷ cs = not (toℕ c ≡ᵇ 46)
  ∧ not (prefixBytes (bytes ".") (reverse (bytes p)))
  ∧ not (prefixBytes (reverse (bytes ".lock")) (reverse (bytes p)))

validRefName : String → Bool
validRefName p with toList p
... | [] = false
... | c ∷ cs = not (toℕ c ≡ᵇ 45) ∧ validRelPath p ∧ all refChar (c ∷ cs)
  ∧ noDoubleDot (c ∷ cs) ∧ all validRefPart (segments p)
  ∧ not (prefixBytes (bytes ".") (reverse (bytes p)))

validBranch : String → Bool
validBranch p = validRefName p ∧ not (primStringEquality p "HEAD")

GitTree : Set
GitTree = List (String × Bytes)

record PureCommit : Set where
  constructor pureCommit
  field
    parentIndex : Maybe ℕ
    treeSnapshot : GitTree
    commitMessage : String
    timestamp : ℕ
open PureCommit public

-- Closed world: flat path maps of regular files with implicit parent directories.
-- Fixtures have no ignore, attribute/filter, or nested-repository policy files;
-- GitSteps model these file/index/commit/ref transitions. Arbitrary target-process
-- effects are outside this model and must be supplied as explicit model updates.
-- Commit indices are stable zero-based positions; each parent precedes its child.
record PureGitRepo : Set where
  constructor pureGitRepo
  field
    config : GitConfig
    worktree index : GitTree
    commits : List PureCommit
    branchMap : List (String × Maybe ℕ)
    headBranch : String
    tagMap : List (String × ℕ)
open PureGitRepo public

lookupName : ∀ {A : Set} → String → List (String × A) → Maybe A
lookupName p [] = nothing
lookupName p ((q , x) ∷ xs) = if primStringEquality p q then just x else lookupName p xs

putName : ∀ {A : Set} → String → A → List (String × A) → List (String × A)
putName p x [] = (p , x) ∷ []
putName p x ((q , y) ∷ xs) = if primStringEquality p q then (p , x) ∷ xs else (q , y) ∷ putName p x xs

removeName : ∀ {A : Set} → String → List (String × A) → List (String × A)
removeName p [] = []
removeName p ((q , x) ∷ xs) = if primStringEquality p q then xs else (q , x) ∷ removeName p xs

present : ∀ {A : Set} → Maybe A → Bool
present nothing = false
present (just _) = true

eqMaybeBytes : Maybe Bytes → Maybe Bytes → Bool
eqMaybeBytes nothing nothing = true
eqMaybeBytes (just a) (just b) = eqBytes a b
eqMaybeBytes _ _ = false

insertPath : String → List String → List String
insertPath p [] = p ∷ []
insertPath p (q ∷ qs) = if primStringEquality p q then q ∷ qs else
  if ltBytes (bytes p) (bytes q) then p ∷ q ∷ qs else q ∷ insertPath p qs

sortPaths : List String → List String
sortPaths [] = []
sortPaths (p ∷ ps) = insertPath p (sortPaths ps)

choosePaths : (String → Bool) → List String → List String
choosePaths f [] = []
choosePaths f (p ∷ ps) = if f p then p ∷ choosePaths f ps else choosePaths f ps

nthCommit : ℕ → List PureCommit → Maybe PureCommit
nthCommit n [] = nothing
nthCommit zero (c ∷ cs) = just c
nthCommit (suc n) (c ∷ cs) = nthCommit n cs

headIndex : PureGitRepo → Maybe ℕ
headIndex r with lookupName (headBranch r) (branchMap r)
... | nothing = nothing
... | just n = n

treeAt : Maybe ℕ → List PureCommit → GitTree
treeAt nothing cs = []
treeAt (just n) cs with nthCommit n cs
... | nothing = []
... | just c = treeSnapshot c

headTree : PureGitRepo → GitTree
headTree r = treeAt (headIndex r) (commits r)

countParents : ℕ → Maybe ℕ → List PureCommit → ℕ
countParents zero n cs = zero
countParents (suc fuel) nothing cs = zero
countParents (suc fuel) (just n) cs with nthCommit n cs
... | nothing = zero
... | just c = suc (countParents fuel (parentIndex c) cs)

changedPaths : GitTree → GitTree → List String
changedPaths a b = choosePaths (λ p → not (eqMaybeBytes (lookupName p a) (lookupName p b)))
  (sortPaths (map proj₁ a ++ map proj₁ b))

liveBranches : List (String × Maybe ℕ) → List String
liveBranches [] = []
liveBranches ((p , nothing) ∷ bs) = liveBranches bs
liveBranches ((p , just _) ∷ bs) = p ∷ liveBranches bs

projectSummary : PureGitRepo → GitRepoSummary
projectSummary r = gitSummary (headBranch r)
  (countParents (length (commits r)) (headIndex r) (commits r))
  (sortPaths (liveBranches (branchMap r))) (sortPaths (map proj₁ (tagMap r)))
  (changedPaths (headTree r) (index r))
  (choosePaths (λ p → not (eqMaybeBytes (lookupName p (worktree r)) (lookupName p (index r))))
    (sortPaths (map proj₁ (index r))))
  (choosePaths (λ p → not (present (lookupName p (index r)))) (sortPaths (map proj₁ (worktree r))))

initTree : List String → List Bytes → GitTree
initTree [] bs = []
initTree (p ∷ ps) [] = (p , []) ∷ initTree ps []
initTree (p ∷ ps) (b ∷ bs) = (p , b) ∷ initTree ps bs

initPureGit : GitConfig → List Bytes → PureGitRepo
initPureGit cfg bs = pureGitRepo cfg
  (if all validGitPath (ownedFiles cfg) ∧ noPathCollisions (ownedFiles cfg)
    then initTree (ownedFiles cfg) bs else [])
  [] [] ((defaultBranch cfg , nothing) ∷ []) (defaultBranch cfg) []

writeTree : String → Bytes → GitTree → GitTree
writeTree p b t = if validGitPath p ∧ all (λ q → primStringEquality p (proj₁ q) ∨ not (collide p (proj₁ q))) t
  then putName p b t else t

pathSelected : List String → String → Bool
pathSelected [] p = false
pathSelected (q ∷ qs) p = primStringEquality p q ∨ isParent q p ∨ pathSelected qs p

stageSelected : List String → GitTree → GitTree → GitTree
stageSelected ps w i = chooseEntries (λ p → not (pathSelected ps p)) i ++ chooseEntries (pathSelected ps) w
  where
    chooseEntries : (String → Bool) → GitTree → GitTree
    chooseEntries f [] = []
    chooseEntries f ((p , b) ∷ rest) = if f p then (p , b) ∷ chooseEntries f rest else chooseEntries f rest

allStagePathsExist : List String → GitTree → GitTree → Bool
allStagePathsExist [] w i = true
allStagePathsExist (p ∷ ps) w i = hasPath p (w ++ i) ∧ allStagePathsExist ps w i
  where
    hasPath : String → GitTree → Bool
    hasPath p [] = false
    hasPath p ((q , _) ∷ rest) = primStringEquality p q ∨ isParent p q ∨ hasPath p rest

-- Checkout's two-tree carry rule retains local changes where the target tree
-- agrees with HEAD or the index, and refuses to overwrite conflicting changes.
checkoutSafe : GitTree → GitTree → GitTree → GitTree → Bool
checkoutSafe old next staged working = all safe (sortPaths (map proj₁ old ++ map proj₁ next ++ map proj₁ staged))
  where
    safe : String → Bool
    safe p = eqMaybeBytes (lookupName p old) (lookupName p next)
      ∨ eqMaybeBytes (lookupName p staged) (lookupName p next)
      ∨ (eqMaybeBytes (lookupName p staged) (lookupName p old)
        ∧ eqMaybeBytes (lookupName p working) (lookupName p staged))

carryTree : GitTree → GitTree → GitTree → GitTree → List String → GitTree
carryTree old next staged working [] = working
carryTree old next staged working (p ∷ ps) = carryTree old next staged (replace p) ps
  where
    replace : String → GitTree
    replace p with eqMaybeBytes (lookupName p old) (lookupName p next)
      ∨ eqMaybeBytes (lookupName p staged) (lookupName p next)
    ... | true = working
    ... | false with lookupName p next
    ...   | nothing = removeName p working
    ...   | just b = putName p b working

checkoutExisting : String → Maybe ℕ → PureGitRepo → PureGitRepo
checkoutExisting name dest r = if checkoutSafe old next (index r) (worktree r)
    ∧ noPathCollisions (map proj₁ nextIndex) ∧ noPathCollisions (map proj₁ nextWorktree)
  then record r { headBranch = name ; index = nextIndex ; worktree = nextWorktree }
  else r
  where
    old = headTree r
    next = treeAt dest (commits r)
    paths = sortPaths (map proj₁ old ++ map proj₁ next ++ map proj₁ (index r))
    nextIndex = carryTree old next (index r) (index r) paths
    nextWorktree = carryTree old next (index r) (worktree r) paths

newBranchMap : PureGitRepo → List (String × Maybe ℕ)
newBranchMap r with headIndex r
... | nothing = removeName (headBranch r) (branchMap r)
... | just _ = branchMap r

switchBranch : String → Bool → PureGitRepo → PureGitRepo
switchBranch name create r with validBranch name | lookupName name (branchMap r)
... | false | _ = r
... | true | just dest = if create then r else checkoutExisting name dest r
... | true | nothing = if create ∧ all (λ p → not (collide name (proj₁ p))) (newBranchMap r)
  then record r { headBranch = name
    ; branchMap = putName name (headIndex r) (newBranchMap r) } else r

createTag : String → PureGitRepo → PureGitRepo
createTag name r with headIndex r
... | nothing = r
... | just n = if validRefName name ∧ all (λ p → not (collide name (proj₁ p))) (tagMap r)
  then record r { tagMap = putName name n (tagMap r) } else r

commitTree : String → ℕ → PureGitRepo → PureGitRepo
commitTree msg offset r = if not (primStringEquality msg "")
    ∧ all (λ c → not (toℕ c ≡ᵇ 0)) (toList msg) ∧ changed
  then record r
    { commits = commits r ++ (pureCommit (headIndex r) (index r) msg (baseEpochSec (config r) + offset) ∷ [])
    ; branchMap = putName (headBranch r) (just (length (commits r))) (branchMap r) }
  else r
  where
    changed = not (length (changedPaths (headTree r) (index r)) ≡ᵇ zero)

-- External processes are intentionally outside the closed world: their raw
-- output and arbitrary filesystem effects are observed through the transport boundary.
stepPureGit : GitStep → PureGitRepo → PureGitRepo × Maybe GitRepoSummary
stepPureGit (gitWriteFile p bs) r = record r { worktree = writeTree p bs (worktree r) } , nothing
stepPureGit (gitRemoveFile p) r = (if validGitPath p then record r { worktree = removeName p (worktree r) } else r) , nothing
stepPureGit gitStageAll r = record r { index = worktree r } , nothing
stepPureGit (gitStagePaths ps) r = (if all validGitPath ps ∧ allStagePathsExist ps (worktree r) (index r)
  then record r { index = stageSelected ps (worktree r) (index r) } else r) , nothing
stepPureGit (gitCommit msg offset) r = commitTree msg offset r , nothing
stepPureGit (gitSwitchBranch name create) r = switchBranch name create r , nothing
stepPureGit (gitCreateTag name) r = createTag name r , nothing
stepPureGit gitStatus r = r , just (projectSummary r)
stepPureGit (gitRunTarget exe args input timeout) r = r , nothing

runPureGit : List GitStep → PureGitRepo → PureGitRepo
runPureGit [] r = r
runPureGit (q ∷ qs) r = runPureGit qs (proj₁ (stepPureGit q r))

eqStrings : List String → List String → Bool
eqStrings [] [] = true
eqStrings (a ∷ as) (b ∷ bs) = primStringEquality a b ∧ eqStrings as bs
eqStrings _ _ = false

eqGitSummary : GitRepoSummary → GitRepoSummary → Bool
eqGitSummary a b = primStringEquality (currentBranch a) (currentBranch b)
  ∧ (commitCount a ≡ᵇ commitCount b) ∧ eqStrings (branchNames a) (branchNames b)
  ∧ eqStrings (tagNames a) (tagNames b) ∧ eqStrings (stagedPaths a) (stagedPaths b)
  ∧ eqStrings (modifiedPaths a) (modifiedPaths b) ∧ eqStrings (untrackedPaths a) (untrackedPaths b)
