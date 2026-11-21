{-# OPTIONS --guardedness #-}
module Code.AgdaTool where

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; intersperse) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import OwnershipIO using (RunningIO)
open import OwnershipIO.FFI
open import Code hiding (Name; set)
open import Code.Render using (render)
open import Code.Transport using (CheckResult; pass; fail)
open import Code.Protocol public using (AgdaCheckReq; agdaCheck; mainCode; dependencies)

modulePath : Code → String
modulePath c = intersperse "/" (full (modName c)) ++ˢ ".agda"

parentPath : List String → String
parentPath [] = ""
parentPath (_ ∷ []) = ""
parentPath (s ∷ ss) = s ++ˢ "/" ++ˢ parentPath ss

writeCode : String → Code → IO.IO ⊤
writeCode dir c = mkdirP (dir ++ˢ "/" ++ˢ parentPath (full (modName c))) IO.>>= λ _ →
  F.writeFile (dir ++ˢ "/" ++ˢ modulePath c) (render c)

writeCodes : String → List Code → IO.IO ⊤
writeCodes dir [] = IO.return tt
writeCodes dir (c ∷ cs) = writeCode dir c IO.>>= λ _ → writeCodes dir cs

checkIn : List String → String → AgdaCheckReq → IO.IO CheckResult
checkIn incs dir req = writeCodes dir (dependencies req) IO.>>= λ _ →
  writeCode dir (mainCode req) IO.>>= λ _ →
  readProcessAt dir 120000 "agda" (concatMap (λ i → "-i" ∷ i ∷ []) ("." ∷ incs) ++ (modulePath (mainCode req) ∷ [])) "" IO.>>= λ where
    (procResult zero _ _) → IO.return pass
    (procResult (suc _) out err) → IO.return (fail (stripStdlibWarnings (out ++ˢ err)))

-- Every check has a fresh workspace: no stale child implementations can make
-- a failed conditional proof appear valid. Cleanup happens on pass and fail.
agdaTool : List String → String → RunningIO AgdaCheckReq CheckResult (⊤ × ⊤)
agdaTool incs scratch = record
  { onCall = λ req → freshDirectory scratch IO.>>= λ dir →
      checkIn incs dir req IO.>>= λ result → removeAll dir IO.>>= λ _ → IO.return result
  ; onStop = IO.return (tt , tt) }
