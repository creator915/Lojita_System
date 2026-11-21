import AgdaMirror.Core
import AgdaMirror.Context
import AgdaMirror.World
import AgdaMirror.Protocol
import AgdaMirror.AxiomGuard
import Prism.Conservativity

/-!
# Compile-Time Zero-Axiom Verification of the Closed `AgdaMirror` Target Universe

The build checks the transitive axiom dependencies of the mirror declarations
listed below. Generated checks can also contain assumptions representing a
specification stub or an interface between Lean and an Agda-checked slice.
Those assumptions belong to the generated bundle.
-/

#agda_prism_guard_axioms
  AgdaMirror.AgdaTop
  AgdaMirror.AgdaBot
  AgdaMirror.botElim
  AgdaMirror.AgdaId
  AgdaMirror.idSym
  AgdaMirror.idTrans
  AgdaMirror.idCong
  AgdaMirror.idCong2
  AgdaMirror.idSubst
  AgdaMirror.agdaNot
  AgdaMirror.agdaAnd
  AgdaMirror.agdaOr
  AgdaMirror.agdaIte
  AgdaMirror.NotNot
  AgdaMirror.nnPure
  AgdaMirror.nnBind
  AgdaMirror.nnLEM
  AgdaMirror.FriedmanCont
  AgdaMirror.contCallCC
  AgdaMirror.AgdaSigma
  AgdaMirror.AgdaExists
  AgdaMirror.agdaAdd_eq_add
  AgdaMirror.agdaMul_eq_mul
  AgdaMirror.agdaSub_eq_sub
  AgdaMirror.agdaAppend_eq
  AgdaMirror.agdaDivHelper
  AgdaMirror.agdaModHelper
  AgdaMirror.agdaAdd
  AgdaMirror.agdaMul
  AgdaMirror.agdaSub
  AgdaMirror.agdaAppend
  AgdaMirror.agdaMap
  AgdaMirror.agdaReverse
  AgdaMirror.Context.PortLift
  AgdaMirror.Context.Commutes₁
  AgdaMirror.Context.PortRel
  AgdaMirror.Context.TransportsPoly
  AgdaMirror.Context.composeTransportsCut
  AgdaMirror.Context.transportLiftCube
  AgdaMirror.agdaBoolTDec
  AgdaMirror.agdaPred
  AgdaMirror.agdaNatDecEq
  AgdaMirror.maybePrime
  AgdaMirror.fromMaybe
  AgdaMirror.maybeWhen
  AgdaMirror.maybeIsJust
  AgdaMirror.maybeIsNothing
  AgdaMirror.maybeZipWith
  AgdaMirror.AgdaAny
  AgdaMirror.AgdaAll
  AgdaMirror.agdaTake
  AgdaMirror.agdaDrop
  AgdaMirror.agdaUpTo
  AgdaMirror.agdaZip
  AgdaMirror.AgdaPair
  AgdaMirror.pairMap1
  AgdaMirror.pairMap2
  AgdaMirror.agdaZipPair
  AgdaMirror.agdaTails
  AgdaMirror.agdaMapMaybe
  AgdaMirror.agdaLookup
  AgdaMirror.agdaLinesBy
  AgdaMirror.agdaWordsByList
  AgdaMirror.agdaToLower
  AgdaMirror.agdaIsAlpha
  AgdaMirror.agdaIsSpace
  AgdaMirror.agdaIsPrint
  AgdaMirror.agdaCharDecEq
  AgdaMirror.agdaStrDecEq
  AgdaMirror.agdaCharEqDecides
  AgdaMirror.agdaStrEqDecides
  AgdaMirror.agdaStrEq
  AgdaMirror.agdaStrAppend
  AgdaMirror.agdaSumMap
  AgdaMirror.agdaSumMap₁
  AgdaMirror.agdaSumMap₂
  AgdaMirror.AgdaPermutation
  AgdaMirror.agdaToWitness
  AgdaMirror.agdaToWitnessFalse
  AgdaMirror.agdaStrConcat
  AgdaMirror.agdaWordsBy
  AgdaMirror.agdaWords
  AgdaMirror.agdaLines
  AgdaMirror.agdaStrToListInjective
  AgdaMirror.agdaStrFromListInjective
  AgdaMirror.Context.SafeTaboo
  AgdaMirror.Context.SafeTaboo.bottom
  AgdaMirror.Context.SafeTaboo.primStrRefl
  AgdaMirror.Context.SafeTaboo.primCharRefl
  AgdaMirror.Context.SafeTaboo.strRoundtrip
  AgdaMirror.Context.SafeTaboo.listRoundtrip
  AgdaMirror.Context.SafeTaboo.funExtBool
  AgdaMirror.Context.SafeTaboo.wlpo
  AgdaMirror.Context.SafeTaboo.markov
  AgdaMirror.agdaDoes
  AgdaMirror.agdaIsYes
  AgdaMirror.agdaIsYesDoes
  AgdaMirror.agdaMapDec
  AgdaMirror.agdaDecTrue
  AgdaMirror.agdaDecFalse
  AgdaMirror.agdaCharToNatInjective
  AgdaMirror.agdaAppendAssoc
  AgdaMirror.agdaAppendIdentityR
  AgdaMirror.agdaNatEqbToEq
  AgdaMirror.agdaMulIdentityL
  AgdaMirror.agdaNatLtbToLt
  AgdaMirror.agdaNatLeTrans
  AgdaMirror.agdaNatLtIrrefl
  AgdaMirror.Context.Filter.classify
  AgdaMirror.Context.Filter.expected1
  AgdaMirror.Context.Filter.inputPort
  AgdaMirror.AgdaNatLeRel
  AgdaMirror.agdaNatLeDec
  AgdaMirror.agdaIntAdd
  AgdaMirror.agdaIntMul
  AgdaMirror.Clock.SimClock
  AgdaMirror.Clock.advanceClockAdd
  AgdaMirror.Clock.advanceClockComm
  AgdaMirror.Clock.advanceClockMonoLe
  AgdaMirror.Clock.traceSimClockAppend
  AgdaMirror.TermLaws.stepANSIAppend
  AgdaMirror.TermLaws.appendObsAssoc
  AgdaMirror.TermLaws.advanceAdd
  AgdaMirror.TermLaws.altScreenRoundtrip
  AgdaMirror.FuzzGen.fuzzCheck
  AgdaMirror.FsSandbox.stepVirtualFs
  AgdaMirror.NetSandbox.parseHttpReq
  AgdaMirror.NetSandbox.parseHttpResp
  AgdaMirror.GitSandbox.stepPureGit
  AgdaMirror.WebOperad.visualHitConsistent
  AgdaMirror.WebOperad.drawMachineSound
  AgdaMirror.World.decodeUtf8
  AgdaMirror.World.decodeUtf8Lossy
  AgdaMirror.World.SimWorld
  AgdaMirror.World.WorldProg
  AgdaMirror.World.liftWorld
  AgdaMirror.World.runWorldPure
  AgdaMirror.World.runReactivePure
  AgdaMirror.FsLaws.lookupInsertSame
  AgdaMirror.FsLaws.lookupInsertOther
  AgdaMirror.FsLaws.readAfterWriteSame
  AgdaMirror.FsLaws.readAfterWriteOther
  AgdaMirror.GitLaws.lookupNamePutNameSame
  AgdaMirror.GitLaws.lookupNamePutNameOther
  AgdaMirror.GitLaws.stepPureGitStageAllModifiedEmpty
  AgdaMirror.GitLaws.runPureGitAppend
  AgdaMirror.NetLaws.parseHttpReqEncodeRoundtrip
  AgdaMirror.NetLaws.parseHttpRespEncodeRoundtrip
  AgdaMirror.NetLaws.evalStubExchangeAppend
  AgdaMirror.WorldLaws.runWorldPureBind
  AgdaMirror.WorldLaws.liftWorldPreservesRun
  AgdaMirror.WorldLaws.progPreservesClock
  AgdaMirror.WorldLaws.progPreservesFs
  AgdaMirror.WorldLaws.progPreservesNet
  AgdaMirror.WorldLaws.progPreservesTty
  AgdaMirror.WorldLaws.runReactiveStepsAppend
  AgdaMirror.Protocol.Proto
  AgdaMirror.Protocol.dual
  AgdaMirror.Protocol.dualInvolutive
  AgdaMirror.Protocol.EndpointCore
  AgdaMirror.Protocol.Endpoint
  AgdaMirror.Protocol.mapEndpoint
  AgdaMirror.Protocol.liftProgToEndpoint
  AgdaMirror.Protocol.liftEndpoint
  AgdaMirror.Protocol.coupleEndpoints
  AgdaMirror.Protocol.composeReactive
  AgdaMirror.Protocol.coupleReactiveTurn
  AgdaMirror.Protocol.coupleReactive
  AgdaMirror.Protocol.coupleDone
  AgdaMirror.Protocol.coupleSendRecv
  AgdaMirror.Protocol.coupleRecvSend
  AgdaMirror.Protocol.coupleSelectLOffer
  AgdaMirror.Protocol.coupleSelectROffer
  AgdaMirror.Protocol.coupleOfferSelectL
  AgdaMirror.Protocol.coupleOfferSelectR
  AgdaMirror.Protocol.coupleStepLeft
  AgdaMirror.Protocol.couplePreservesClock
  AgdaMirror.Protocol.couplePreservesFs
  AgdaMirror.Protocol.couplePreservesNet
  AgdaMirror.Protocol.couplePreservesTty

#print axioms AgdaMirror.agdaStrToListInjective
#print axioms AgdaMirror.agdaStrFromListInjective

section
open AgdaMirror
variable (s : String) (cs : List Char)
-- The builtins compute on literals while each open conversion remains stuck.
example : agdaCharFromNat 0xd800 = '�' := rfl
example : agdaCharFromNat 0x110061 = 'a' := rfl
example : agdaStrAppend "λ" "🙂" = "λ🙂" := rfl
example : agdaStrEq "λ🙂" "λ🙂" = true := rfl
example : agdaStrEq "λ" "🙂" = false := rfl
#check_failure (AgdaId.refl : AgdaId (agdaStrEq s s) true)
#check_failure (AgdaId.refl : AgdaId (agdaStrAppend "" s) s)
#check_failure (AgdaId.refl : AgdaId (agdaStrAppend s "") s)
#check_failure (AgdaId.refl : AgdaId (agdaStrEq (agdaFromList ('a' :: cs)) (agdaFromList ('b' :: cs))) false)
#check_failure (AgdaId.refl : AgdaId (agdaFromList (agdaToList s)) s)
#check_failure (AgdaId.refl : AgdaId (agdaToList (agdaFromList cs)) cs)
end

-- Compile-time definitional reduction checks matching `agda-stdlib` unit tests:
example : AgdaMirror.agdaWords " abc  b   " = ["abc", "b"] := rfl
example : AgdaMirror.agdaLines "\nabc\n\nb\n\n\n" = ["", "abc", "", "b", "", ""] := rfl
example : AgdaMirror.agdaLines "" = [] := rfl
example : AgdaMirror.agdaLines "a\n" = ["a"] := rfl
example : AgdaMirror.agdaWordsBy (AgdaMirror.agdaCharDecEq '.') "Gen.T1.JSON" = ["Gen", "T1", "JSON"] := rfl
example : AgdaMirror.agdaUpTo 4 = [0, 1, 2, 3] := rfl
-- The builtin clauses inspect the second argument of subtraction and less-than first.
example (n : Nat) : AgdaMirror.agdaNatLt (AgdaMirror.agdaAdd 10 n) 10 = false := rfl
example (n : Nat) : AgdaMirror.agdaSub (AgdaMirror.agdaAdd 10 n) 10 = n := rfl

-- Verify `TransportsPoly (graphPort ...) (idPort ...)` unfolds in LHS pattern matching on `refl`
-- both with pure wildcards and with named LHS variables referenced on the RHS:
private def _testSquare :
    AgdaMirror.Context.TransportsPoly
      (AgdaMirror.Context.graphPort (fun (x : Bool) => AgdaMirror.AgdaPair.mk false x))
      (AgdaMirror.Context.idPort Bool)
      (fun _ => AgdaMirror.AgdaTop)
      (fun x => x)
      (fun p => p.proj₂)
  | _, _, _, AgdaMirror.AgdaId.refl => AgdaMirror.AgdaId.refl

private def _testNamedSquare :
    AgdaMirror.Context.TransportsPoly
      (AgdaMirror.Context.graphPort (fun (x : Bool) => AgdaMirror.AgdaPair.mk false x))
      (AgdaMirror.Context.idPort Bool)
      (fun _ => AgdaMirror.AgdaTop)
      (fun x => x)
      (fun p => p.proj₂)
  | x, _, _, AgdaMirror.AgdaId.refl =>
      AgdaMirror.idTrans (AgdaMirror.AgdaId.refl : AgdaMirror.AgdaId x x)
        (AgdaMirror.idSym (AgdaMirror.AgdaId.refl : AgdaMirror.AgdaId (AgdaMirror.AgdaPair.mk false x).proj₂ x))

-- Exercise F_chk and its in-memory kernel guards on the closed taboo attempts
-- and injected hybrid declarations during the build as well as verify-self.
run_cmd do
  let lib := (← Lean.findOLean `AgdaMirror.Core).parent.get!.parent.get!
  try Prism.Conservativity.verify lib.toString finally Prism.KernelDriver.close
