{-# OPTIONS --safe #-}
module N23_SafeImportsUnsafe where
open import Context.Blueprint using (PortLift; keepPort)
open import Data.Nat using (ℕ)
-- Coinfective flag violation: `--safe` module importing non-`--safe` module!
bad : PortLift ℕ ℕ
bad = keepPort ℕ
