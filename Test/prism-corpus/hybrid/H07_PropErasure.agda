{-# OPTIONS --prop --guardedness #-}
module H07_PropErasure where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Show using (show)
open import IO using (Main; run; putStrLn)

data Evidence : Prop where
  witnessed : Evidence

cost : ℕ → ℕ → ℕ
cost zero x = x
cost (suc n) x = cost n (suc x) + cost n (suc (suc x))

proof : ℕ → Evidence
proof zero = witnessed
proof (suc n) = proof n

ignore : Evidence → ℕ
ignore _ = 7

main : Main
main = run (putStrLn (show (ignore (proof (cost 42 5)))))
