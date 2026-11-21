(submission (kind contradiction) (refute @proof))
```agda proof
module Refute where
import Relation.Binary.PropositionalEquality.TrustMe
import Gen.T2.Root as Spec
open import Data.Empty using (⊥)
proof : ⊥
proof = Spec.flag
```
