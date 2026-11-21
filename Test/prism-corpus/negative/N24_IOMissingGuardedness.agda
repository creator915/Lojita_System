module N24_IOMissingGuardedness where
-- `IO` in agda-stdlib uses `--guardedness` (infective flag): importing `IO` without `--guardedness` fails!
open import IO using (Main)
open import Data.Nat using (ℕ)
x : ℕ
x = 0
