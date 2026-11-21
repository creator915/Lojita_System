module N13_BadImportUsing where
open import Data.Nat using (ℕ)
-- Referencing a symbol that was excluded by `using (ℕ)` (`suc` not imported into scope)!
x : ℕ
x = suc 0
