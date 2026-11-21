{-# OPTIONS --guardedness #-}
module H05_ExecOptStrictCSE where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (Main; run; putStrLn)

-- Forcing both alternatives at each recursive step gives these depth 35–40
-- examples exponential cost. The native backend must evaluate only the
-- selected alternative, including through wrappers, pairs and with clauses.

data Box : Set where
  box  : Bool → Box → Box
  leaf : ℕ → Box

data Wrap : Set where
  wrap : Bool → Box → Wrap

mkChain : ℕ → Box
mkChain zero    = leaf 1
mkChain (suc n) = box true (mkChain n)

choosePair : Bool → ℕ × ℕ → ℕ
choosePair true  (a , _) = a
choosePair false (_ , b) = b

-- 1. Mutual double-wrapper packing (mirrors `Code.Render` `spineR`/`renderArgE`/`operandArg`)
mutual
  evalBox : Bool → Box → ℕ
  evalBox fl (leaf n)  = n
  evalBox fl (box b x) = choosePair fl (wrapA fl (wrap b x) , wrapB fl (wrap b x))

  innerA : Bool → Box → ℕ
  innerA fl x = if fl then suc (evalBox fl x) else evalBox fl x

  innerB : Bool → Box → ℕ
  innerB fl x = if fl then evalBox fl x else suc (evalBox fl x)

  wrapA : Bool → Wrap → ℕ
  wrapA fl (wrap _ x) = innerA fl x

  wrapB : Bool → Wrap → ℕ
  wrapB fl (wrap _ x) = innerB fl x

-- 2. `with`-scrutinee duplicated call in fallback RHS (mirrors `Code.Render` `renderPat`)
tryZero : ℕ → Maybe ℕ
tryZero zero    = just 0
tryZero (suc _) = nothing

withWalk : Box → ℕ
withWalk (leaf n) = n
withWalk (box _ x) with tryZero (withWalk x)
... | just z  = z
... | nothing = suc (withWalk x)

-- 3. `pureFast` single-function sibling duplicate call
combine2 : ℕ → ℕ → ℕ
combine2 a b = if a ≡ᵇ b then suc a else a + b

pureDup : Box → ℕ
pureDup (leaf n)  = n
pureDup (box _ x) = combine2 (pureDup x) (pureDup x)

-- 4. Nested `with`-CSE (outer + inner hoisted vars must never collide)
nestedWith : Box → ℕ
nestedWith (leaf n) = n
nestedWith (box _ x) with tryZero (nestedWith x)
... | just z  = z
... | nothing with tryZero (suc (nestedWith x))
...   | just k  = k
...   | nothing = suc (nestedWith x)

-- 5. Capture-avoidance on single-clause wrapper inlining with shadowed `let` binder
addTenWrap : ℕ → ℕ
addTenWrap x =
  let y : ℕ
      y = 10
  in x + y

captureCheck : ℕ → ℕ
captureCheck y with tryZero y
... | just _  = addTenWrap y
... | nothing = addTenWrap y

-- 6. Single-branch `if` duplicate call CSE (`branchDup` depth 35 = 2^35 unoptimized)
branchDup : Bool → Box → ℕ
branchDup fl (leaf n)  = n
branchDup fl (box _ x) =
  if fl then combine2 (branchDup fl x) (branchDup fl x) else 0

main : Main
main = run (putStrLn
  ("p1=" ++ˢ show (evalBox true (mkChain 40))
   ++ˢ ",p2=" ++ˢ show (withWalk (mkChain 35))
   ++ˢ ",p3=" ++ˢ show (pureDup (mkChain 40))
   ++ˢ ",p4=" ++ˢ show (nestedWith (mkChain 30))
   ++ˢ ",p5=" ++ˢ show (captureCheck 3)
   ++ˢ ",p6=" ++ˢ show (branchDup true (mkChain 35))
   ++ˢ ",p7=" ++ˢ show (branchDup false (mkChain 35))))
