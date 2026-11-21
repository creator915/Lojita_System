{-# OPTIONS --safe #-}
module N17_ImpredicativeSet where
-- Lean 4 `Prop` is impredicative, whereas Agda `Set₀` is predicative (`Set₁ != Set₀`)!
bad : Set
bad = (A : Set) → A → A
