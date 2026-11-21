import AgdaMirror.Core
import AgdaMirror.Context
import AgdaMirror.World
import AgdaMirror.Protocol
import AgdaMirror.AxiomGuard

/-!
# Compile-Time Zero-Axiom Verification of the Closed `AgdaMirror` Target Universe

Verified once during `lake build`: since `EmitLean` never emits `axiom` or `sorry`
and enforces hygienic `_ag_` identifiers with `autoImplicit = false`, any module
importing only `AgdaMirror.Core` and `AgdaMirror.Context` that passes Lean's kernel
is transitively free of `Classical.choice` and `sorryAx` without paying the cost of
loading `import Lean` (`150 MB`) on every fast check!
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
  AgdaMirror.agdaCharDecEq
  AgdaMirror.agdaStrDecEq
  AgdaMirror.agdaStrConcat
  AgdaMirror.agdaWordsBy
  AgdaMirror.agdaWords
  AgdaMirror.agdaLines
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

-- Compile-time definitional reduction checks matching `agda-stdlib` unit tests:
example : AgdaMirror.agdaWords " abc  b   " = ["abc", "b"] := rfl
example : AgdaMirror.agdaLines "\nabc\n\nb\n\n\n" = ["", "abc", "", "b", "", ""] := rfl
example : AgdaMirror.agdaLines "" = [] := rfl
example : AgdaMirror.agdaLines "a\n" = ["a"] := rfl
example : AgdaMirror.agdaWordsBy (AgdaMirror.agdaCharDecEq '.') "Gen.T1.JSON" = ["Gen", "T1", "JSON"] := rfl
example : AgdaMirror.agdaUpTo 4 = [0, 1, 2, 3] := rfl

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
