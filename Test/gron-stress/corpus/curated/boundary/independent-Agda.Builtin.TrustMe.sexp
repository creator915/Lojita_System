(submission (kind independent) (why "gron stress") (refute @proof))
```agda proof
module Refute where
import Agda.Builtin.TrustMe
import Gen.T2.Root as Spec
open import Context.Taboo using (SafeTaboo)
proof : SafeTaboo
proof = Spec.flag
```
