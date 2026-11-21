{-# OPTIONS --safe #-}
module Test.Tools.GitConformance where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal using (Bytes; byte; bytes; SandboxTarget; localSandbox)
open import Context.Tools.GitSandbox

fixtureConfig : SandboxTarget → GitConfig
fixtureConfig t = gitConfig t "main" "Probe Author" "probe@example.invalid"
  1700000000 [] ("README.md" ∷ [])

initialBytes : Bytes
initialBytes = bytes "initial\n"

initialRepo : PureGitRepo
initialRepo = initPureGit (fixtureConfig localSandbox) (initialBytes ∷ [])

firstCommit : PureGitRepo
firstCommit = runPureGit (gitStageAll ∷ gitCommit "initial" 0 ∷ []) initialRepo

-- Three independent categories remain distinct, including filenames with spaces.
dirtySteps : List GitStep
dirtySteps = gitWriteFile "README.md" (bytes "modified\n")
  ∷ gitWriteFile "staged file.txt" (bytes "staged\n")
  ∷ gitWriteFile "untracked file.txt" (bytes "new\n")
  ∷ gitStagePaths ("staged file.txt" ∷ []) ∷ []

dirtyRepo : PureGitRepo
dirtyRepo = runPureGit dirtySteps firstCommit

branchSteps : List GitStep
branchSteps = gitSwitchBranch "feat" true
  ∷ gitWriteFile "README.md" (bytes "feature\n")
  ∷ gitStageAll ∷ gitCommit "feature" 5 ∷ gitCreateTag "v1.0"
  ∷ gitSwitchBranch "main" false ∷ []

returnedRepo : PureGitRepo
returnedRepo = runPureGit branchSteps firstCommit

initial-count : commitCount (projectSummary initialRepo) ≡ 0
initial-count = refl

initial-untracked : untrackedPaths (projectSummary initialRepo) ≡ ("README.md" ∷ [])
initial-untracked = refl

unborn-branch-is-symbolic : projectSummary initialRepo ≡
  gitSummary "main" 0 [] [] [] [] ("README.md" ∷ [])
unborn-branch-is-symbolic = refl

committed-count : commitCount (projectSummary firstCommit) ≡ 1
committed-count = refl

committed-untracked : untrackedPaths (projectSummary firstCommit) ≡ []
committed-untracked = refl

committed-summary : projectSummary firstCommit ≡ gitSummary "main" 1 ("main" ∷ []) [] [] [] []
committed-summary = refl

separate-staged : stagedPaths (projectSummary dirtyRepo) ≡ ("staged file.txt" ∷ [])
separate-staged = refl

separate-modified : modifiedPaths (projectSummary dirtyRepo) ≡ ("README.md" ∷ [])
separate-modified = refl

separate-untracked : untrackedPaths (projectSummary dirtyRepo) ≡ ("untracked file.txt" ∷ [])
separate-untracked = refl

returned-tree : worktree returnedRepo ≡ (("README.md" , initialBytes) ∷ [])
returned-tree = refl

returned-count : commitCount (projectSummary returnedRepo) ≡ 1
returned-count = refl

returned-branches : branchNames (projectSummary returnedRepo) ≡ ("feat" ∷ "main" ∷ [])
returned-branches = refl

returned-tags : tagNames (projectSummary returnedRepo) ≡ ("v1.0" ∷ [])
returned-tags = refl

returned-summary : projectSummary returnedRepo ≡
  gitSummary "main" 1 ("feat" ∷ "main" ∷ []) ("v1.0" ∷ []) [] [] []
returned-summary = refl

feature-commit : nthCommit 1 (commits returnedRepo) ≡ just
  (pureCommit (just 0) (("README.md" , bytes "feature\n") ∷ []) "feature" 1700000005)
feature-commit = refl

feature-chain : commitCount (projectSummary
  (proj₁ (stepPureGit (gitSwitchBranch "feat" false) returnedRepo))) ≡ 2
feature-chain = refl

staged-removal : stagedPaths (projectSummary (runPureGit
  (gitRemoveFile "README.md" ∷ gitStageAll ∷ []) firstCommit)) ≡ ("README.md" ∷ [])
staged-removal = refl

unstaged-removal : modifiedPaths (projectSummary
  (proj₁ (stepPureGit (gitRemoveFile "README.md") firstCommit))) ≡ ("README.md" ∷ [])
unstaged-removal = refl

reject-git-directory : validGitPath ".git" ≡ false
reject-git-directory = refl

reject-git-config : validGitPath ".git/config" ≡ false
reject-git-config = refl

reject-escape : validGitPath "../outside" ≡ false
reject-escape = refl

reject-absolute : validGitPath "/outside" ≡ false
reject-absolute = refl

reject-nul : validGitPath "a\NULb" ≡ false
reject-nul = refl

reject-branch-option : validBranch "-bad" ≡ false
reject-branch-option = refl

reject-empty-branch : validBranch "" ≡ false
reject-empty-branch = refl

reject-empty-commit : commits (proj₁ (stepPureGit (gitCommit "empty" 0)
  (initPureGit (gitConfig localSandbox "main" "Probe Author" "probe@example.invalid" 1700000000 [] []) []))) ≡ []
reject-empty-commit = refl

protected-write : worktree (proj₁ (stepPureGit (gitWriteFile ".git/config" (bytes "bad")) initialRepo))
  ≡ worktree initialRepo
protected-write = refl

protected-remove : worktree (proj₁ (stepPureGit (gitRemoveFile ".git") initialRepo)) ≡ worktree initialRepo
protected-remove = refl

checkout-preserves-untracked : untrackedPaths (projectSummary (runPureGit
  (gitWriteFile "untracked.txt" (bytes "keep") ∷ gitSwitchBranch "feat" false ∷ []) returnedRepo))
  ≡ ("untracked.txt" ∷ [])
checkout-preserves-untracked = refl

conflicting-checkout-rejected : currentBranch (projectSummary (runPureGit
  (gitWriteFile "README.md" (bytes "local edit") ∷ gitSwitchBranch "feat" false ∷ []) returnedRepo)) ≡ "main"
conflicting-checkout-rejected = refl

unborn-switch-does-not-create-old-ref : branchNames (projectSummary (runPureGit
  (gitSwitchBranch "feat" true ∷ gitStageAll ∷ gitCommit "first on feature" 0 ∷ []) initialRepo))
  ≡ ("feat" ∷ [])
unborn-switch-does-not-create-old-ref = refl
