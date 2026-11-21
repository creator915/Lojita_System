{-# OPTIONS --guardedness #-}
module Test.IndependentSession where

import Test.IndependentPropagation

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (nothing)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import OwnershipIO.MetaFFI using (_>>_)
open import System.Environment.Primitive using (getArgs)
open import OwnershipIO using (RunningIO; onCall; onStop)
open import OwnershipIO.FFI using (newIORef; readIORef; writeIORef; failIO)
open import Code using (Code; modName; decls)
open import Code.Protocol using (dumpReq; dumped; dumpFailed; checkRequest; independenceCheck)
open import Code.Transport using (CheckResult; pass; fail; refuteStubOf; specΔ)
open import Backend.Switch using (switchCheck; leanPrism)
import Meta.Sandbox as Sandbox
open import Code.AI
open import Code.SessionProtocol using (refSpec; local)
open import Code.SessionRunner using (sessionConfig; driveTree; accepted; rejected; finished)

-- One recorded prompt per proposal lets the caller check the actual retry
-- diagnostic from the previous proposal. Exhaustion fails the test immediately.
script : List String → IO (RunningIO AIReq AIReply (⊤ × ⊤))
script files = do
  replies ← newIORef files
  return (record
    { onCall = λ where
        (propose prompt _ _) → readIORef replies >>= λ where
          [] → failIO ("unexpected retry:\n" ++ˢ prompt)
          (f ∷ rest) → do
            F.writeFile (f ++ˢ ".prompt") prompt
            reply ← F.readFile f
            writeIORef replies rest
            return (aiReply reply "scripted")
        (accept _) → return (aiReply "accepted" "scripted")
        (forkNode n) → return (aiReply "" n)
        (bindNode n _) → return (aiReply "bound" n)
    ; onStop = return (tt , tt) })

run : List String → IO ⊤
-- Exercise the same terminal check request with independently supplied task
-- Code and authored bytes, including a stale/mismatched specification.
run ("check-independent" ∷ repo ∷ ws ∷ base ∷ logical ∷ authored ∷ witness ∷ []) = do
  let scope : String → List Code → IO Code
      scope = λ src deps → Sandbox.sandboxDump (repo ++ˢ "/dump/dump") repo ws []
        (dumpReq src [] deps) >>= λ where
          (dumped c) → return c
          (dumpFailed msg) → failIO msg
  b ← F.readFile base >>= λ txt → scope txt []
  s ← F.readFile logical >>= λ txt → scope txt (b ∷ [])
  let stub = refuteStubOf (specΔ (modName s) (decls s) [])
  raw ← F.readFile authored
  src ← F.readFile witness
  w ← scope src (stub ∷ b ∷ [])
  switchCheck leanPrism repo ws []
    (checkRequest w (stub ∷ b ∷ []) (independenceCheck (modName s) [] raw src)) >>= λ where
      pass → F.putStrLn "INDEPENDENT_CONFIRMED"
      (fail err) → failIO err
run (repo ∷ ws ∷ epoch ∷ source ∷ replies) = do
  spec ← F.readFile source
  let cfg = sessionConfig repo ws "independence gate regression"
              (refSpec (local "/bin/false") [] 1000) (ScriptedBackend [])
              (λ _ → ServiceBackend (script replies))
  driveTree cfg epoch spec [] nothing >>= λ where
    (accepted msg) → F.putStrLn msg
    (rejected e) → failIO e
    (finished _) → failIO "unexpected finish"
run _ = failIO "expected repo workspace epoch spec replies..."

main : IO ⊤
main = getArgs >>= run
