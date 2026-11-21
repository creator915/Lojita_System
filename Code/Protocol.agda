module Code.Protocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_)
open import Data.String using (String)
open import Code
open import Code.Transport
open import Code.NodeTransport using (Bindings)
open import Code.Lift

record NodeTask : Set where
  constructor nodeTaskWithTransport
  field
    δ : SpecΔ
    parentFlags : List String
    maybeLift : Maybe (Code × LiftSpec)
    inheritedThread : Maybe String
    contextText : String
    baseModules : List Code
    transports : Bindings
    allowedAncestors : Maybe (List QName)
    rawSpecSource : String
    authoredSources : List (Code × String)
open NodeTask public

pattern mkNodeTask d fs l tid ctx bases = nodeTaskWithTransport d fs l tid ctx bases Data.List.[] Data.Maybe.nothing "" Data.List.[]

nodeTask : SpecΔ → List String → Maybe (Code × LiftSpec) → NodeTask
nodeTask d fs l = mkNodeTask d fs l Data.Maybe.nothing "" Data.List.[]

data CheckPurpose : Set where
  ordinaryCheck : CheckPurpose
  independenceCheck : QName → List String → (rawSpec witnessSource : String) → CheckPurpose
  narrowedSubspec : String → String → CheckPurpose

record AgdaCheckReq : Set where
  constructor checkRequest
  field
    mainCode : Code
    dependencies : List Code
    checkPurpose : CheckPurpose
open AgdaCheckReq public

agdaCheck : Code → List Code → AgdaCheckReq
agdaCheck c ds = checkRequest c ds ordinaryCheck

record DumpReq : Set where
  constructor scopeRequest
  field
    source : String
    sourceDeps : List (Name × String)
    codeDeps : List Code
    requireComplete : Bool
open DumpReq public

-- Specifications may contain signature-only goals. Implementations must
-- preserve Agda's scope diagnostics before that distinction is erased in Code.
dumpReq dumpSubmission : String → List (Name × String) → List Code → DumpReq
dumpReq src ds cs = scopeRequest src ds cs false
dumpSubmission src ds cs = scopeRequest src ds cs true

data DumpResult : Set where
  dumped : Code → DumpResult
  dumpFailed : String → DumpResult

data AIReq : Set where
  bindNode : Name → Maybe String → AIReq
  propose : (prompt : String) (retry : Bool) (planContext : String) → AIReq
  accept : String → AIReq
  forkNode : String → AIReq

record AIReply : Set where
  constructor aiReply
  field
    text : String
    threadId : String
open AIReply public
