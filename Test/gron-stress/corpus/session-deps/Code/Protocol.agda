module Code.Protocol where

open import Data.Bool using (Bool)
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
open NodeTask public

pattern mkNodeTask d fs l tid ctx bases = nodeTaskWithTransport d fs l tid ctx bases Data.List.[] Data.Maybe.nothing ""

nodeTask : SpecΔ → List String → Maybe (Code × LiftSpec) → NodeTask
nodeTask d fs l = mkNodeTask d fs l Data.Maybe.nothing "" Data.List.[]

data CheckPurpose : Set where
  ordinaryCheck : CheckPurpose
  independenceCheck : QName → List String → CheckPurpose
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
  constructor dumpReq
  field
    source : String
    sourceDeps : List (Name × String)
    codeDeps : List Code
open DumpReq public

data DumpResult : Set where
  dumped : Code → DumpResult
  dumpFailed : String → DumpResult

data AIReq : Set where
  bindNode : Name → Maybe String → AIReq
  propose : String → Bool → AIReq
  accept : String → AIReq
  forkNode : String → AIReq

record AIReply : Set where
  constructor aiReply
  field
    text : String
    threadId : String
open AIReply public
