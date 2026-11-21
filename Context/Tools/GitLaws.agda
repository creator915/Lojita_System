{-# OPTIONS --safe #-}
module Context.Tools.GitLaws where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Context.Terminal using (Bytes)
open import Context.Tools.FsSandbox using (eqStr; eqBytes)
open import Context.Tools.FsLaws using (eqStr-refl; ≢Str⇒eqStr≡false; eqBytes-refl)
open import Context.Tools.GitSandbox

-- 1. Association-map lens laws for Git trees, branches, and tags
lookupName-putName-same : ∀ {A : Set} (p : String) (v : A) (m : List (String × A)) →
  lookupName p (putName p v m) ≡ just v
lookupName-putName-same p _ [] rewrite eqStr-refl p = refl
lookupName-putName-same p v ((q , y) ∷ xs) with eqStr p q in eqPQ
... | true  rewrite eqStr-refl p = refl
... | false rewrite eqPQ = lookupName-putName-same p v xs

lookupName-putName-other : ∀ {A : Set} (p q : String) (v : A) (m : List (String × A)) →
  (p ≡ q → ⊥) →
  lookupName p (putName q v m) ≡ lookupName p m
lookupName-putName-other p q _ [] p≢q with eqStr p q in eqPQ
... | false = refl
... | true  = ⊥-elim (p≢q (Context.Tools.FsLaws.eqStr⇒≡ p q eqPQ))
lookupName-putName-other p q v ((k , y) ∷ xs) p≢q with eqStr q k in eqQK
... | true with eqStr p q in eqPQ | eqStr p k in eqPK
...   | true  | _     = ⊥-elim (p≢q (Context.Tools.FsLaws.eqStr⇒≡ p q eqPQ))
...   | false | true  = ⊥-elim (p≢q (Relation.Binary.PropositionalEquality.trans (Context.Tools.FsLaws.eqStr⇒≡ p k eqPK) (Relation.Binary.PropositionalEquality.sym (Context.Tools.FsLaws.eqStr⇒≡ q k eqQK))))
...   | false | false = refl
lookupName-putName-other p q v ((k , y) ∷ xs) p≢q | false with eqStr p k
... | true  = refl
... | false = lookupName-putName-other p q v xs p≢q

-- 2. PureGitRepo State Projection & Homomorphism Laws
stepPureGit-status-id : ∀ (r : PureGitRepo) →
  stepPureGit gitStatus r ≡ (r , just (projectSummary r))
stepPureGit-status-id _ = refl

stepPureGit-stageAll-index : ∀ (r : PureGitRepo) →
  index (proj₁ (stepPureGit gitStageAll r)) ≡ worktree r
stepPureGit-stageAll-index _ = refl

stepPureGit-stageAll-head : ∀ (r : PureGitRepo) →
  headBranch (proj₁ (stepPureGit gitStageAll r)) ≡ headBranch r
stepPureGit-stageAll-head _ = refl

eqMaybeBytes-refl : ∀ (mb : Maybe Bytes) → eqMaybeBytes mb mb ≡ true
eqMaybeBytes-refl nothing   = refl
eqMaybeBytes-refl (just bs) = eqBytes-refl bs

choosePaths-all-false : ∀ (f : String → Bool) (ps : List String) →
  (∀ p → f p ≡ false) → choosePaths f ps ≡ []
choosePaths-all-false _ []       _  = refl
choosePaths-all-false f (p ∷ ps) h rewrite h p = choosePaths-all-false f ps h

-- Right after `gitStageAll` (`git add -A`), `modifiedPaths` is unconditionally `[]`!
stepPureGit-stageAll-modified-empty : ∀ (r : PureGitRepo) →
  modifiedPaths (projectSummary (proj₁ (stepPureGit gitStageAll r))) ≡ []
stepPureGit-stageAll-modified-empty r =
  choosePaths-all-false
    (λ p → not (eqMaybeBytes (lookupName p (worktree r)) (lookupName p (worktree r))))
    (sortPaths (Data.List.map proj₁ (worktree r)))
    (λ p → cong not (eqMaybeBytes-refl (lookupName p (worktree r))))

private
  inSortPaths⇒present : ∀ (p : String) (t : GitTree) →
    present (lookupName p t) ≡ false →
    (∀ q → present (lookupName q t) ≡ true → (p ≡ q → ⊥))
  inSortPaths⇒present p t absP q presQ refl rewrite absP with presQ
  ... | ()

runPureGit-[] : ∀ (r : PureGitRepo) → runPureGit [] r ≡ r
runPureGit-[] _ = refl

runPureGit-++ : ∀ (xs ys : List GitStep) (r : PureGitRepo) →
  runPureGit (xs Data.List.++ ys) r ≡ runPureGit ys (runPureGit xs r)
runPureGit-++ []       _  _ = refl
runPureGit-++ (x ∷ xs) ys r = runPureGit-++ xs ys (proj₁ (stepPureGit x r))
