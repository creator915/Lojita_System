(submission (kind plan) (why "gron stress") (main @proof) (moves) (subspecs ("Gen.T2.Root.Child" @sub)))
```agda proof
module Gen.T2.Root where
open import Data.Bool using (Bool; true)
flag : Bool
flag = true
```
```agda sub
module Gen.T2.Root.Child where
import Data.String.Unsafe
open import Data.Bool using (Bool)
postulate flag : Bool
```
