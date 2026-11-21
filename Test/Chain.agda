------------------------------------------------------------------------
-- Test/Chain.agda —— 长脚本的检查时间（README_code §16 的验收）
--   旧编码（类型里写 remove (at w)）：连续 unlink 15 步超过 300 s，create/unlink 交替 15 步耗尽内存
--   现在：下面两段各 40 步，整个文件几秒
--   ./check.sh Test/Chain.agda
------------------------------------------------------------------------
{-# OPTIONS --guardedness #-}
module Test.Chain where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Ownership

-- 40 个文件，一个一个删掉
unlink40 : Prog Ψ (Dir (("f0" , File ℕ) ∷ ("f1" , File ℕ) ∷ ("f2" , File ℕ) ∷ ("f3" , File ℕ) ∷ ("f4" , File ℕ) ∷ ("f5" , File ℕ) ∷ ("f6" , File ℕ) ∷ ("f7" , File ℕ) ∷ ("f8" , File ℕ) ∷ ("f9" , File ℕ) ∷ ("f10" , File ℕ) ∷ ("f11" , File ℕ) ∷ ("f12" , File ℕ) ∷ ("f13" , File ℕ) ∷ ("f14" , File ℕ) ∷ ("f15" , File ℕ) ∷ ("f16" , File ℕ) ∷ ("f17" , File ℕ) ∷ ("f18" , File ℕ) ∷ ("f19" , File ℕ) ∷ ("f20" , File ℕ) ∷ ("f21" , File ℕ) ∷ ("f22" , File ℕ) ∷ ("f23" , File ℕ) ∷ ("f24" , File ℕ) ∷ ("f25" , File ℕ) ∷ ("f26" , File ℕ) ∷ ("f27" , File ℕ) ∷ ("f28" , File ℕ) ∷ ("f29" , File ℕ) ∷ ("f30" , File ℕ) ∷ ("f31" , File ℕ) ∷ ("f32" , File ℕ) ∷ ("f33" , File ℕ) ∷ ("f34" , File ℕ) ∷ ("f35" , File ℕ) ∷ ("f36" , File ℕ) ∷ ("f37" , File ℕ) ∷ ("f38" , File ℕ) ∷ ("f39" , File ℕ) ∷ [])) (Dir []) ⊤
unlink40 = do
  unlink "f0"
  unlink "f1"
  unlink "f2"
  unlink "f3"
  unlink "f4"
  unlink "f5"
  unlink "f6"
  unlink "f7"
  unlink "f8"
  unlink "f9"
  unlink "f10"
  unlink "f11"
  unlink "f12"
  unlink "f13"
  unlink "f14"
  unlink "f15"
  unlink "f16"
  unlink "f17"
  unlink "f18"
  unlink "f19"
  unlink "f20"
  unlink "f21"
  unlink "f22"
  unlink "f23"
  unlink "f24"
  unlink "f25"
  unlink "f26"
  unlink "f27"
  unlink "f28"
  unlink "f29"
  unlink "f30"
  unlink "f31"
  unlink "f32"
  unlink "f33"
  unlink "f34"
  unlink "f35"
  unlink "f36"
  unlink "f37"
  unlink "f38"
  unlink "f39"

-- 同一个名字，建了删、建了删，40 次
churn40 : Prog Ψ (Dir []) (Dir []) ⊤
churn40 = do
  create "x" 0
  unlink "x"
  create "x" 1
  unlink "x"
  create "x" 2
  unlink "x"
  create "x" 3
  unlink "x"
  create "x" 4
  unlink "x"
  create "x" 5
  unlink "x"
  create "x" 6
  unlink "x"
  create "x" 7
  unlink "x"
  create "x" 8
  unlink "x"
  create "x" 9
  unlink "x"
  create "x" 10
  unlink "x"
  create "x" 11
  unlink "x"
  create "x" 12
  unlink "x"
  create "x" 13
  unlink "x"
  create "x" 14
  unlink "x"
  create "x" 15
  unlink "x"
  create "x" 16
  unlink "x"
  create "x" 17
  unlink "x"
  create "x" 18
  unlink "x"
  create "x" 19
  unlink "x"
  create "x" 20
  unlink "x"
  create "x" 21
  unlink "x"
  create "x" 22
  unlink "x"
  create "x" 23
  unlink "x"
  create "x" 24
  unlink "x"
  create "x" 25
  unlink "x"
  create "x" 26
  unlink "x"
  create "x" 27
  unlink "x"
  create "x" 28
  unlink "x"
  create "x" 29
  unlink "x"
  create "x" 30
  unlink "x"
  create "x" 31
  unlink "x"
  create "x" 32
  unlink "x"
  create "x" 33
  unlink "x"
  create "x" 34
  unlink "x"
  create "x" 35
  unlink "x"
  create "x" 36
  unlink "x"
  create "x" 37
  unlink "x"
  create "x" 38
  unlink "x"
  create "x" 39
  unlink "x"

-- refl 仍是 refl：包装里的 coherence 引理在具体脚本上算成 refl，subst 消失
_ : eval {Ψ = []} [] churn40 tt ≡ (tt , tt)
_ = refl
