{-# OPTIONS --guardedness #-}
module Test.CountermodelGateTest where

open import Data.Bool using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; unlines) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Function.Base using (case_of_)
open import IO.Primitive using (IO; return; _>>=_)
import IO.Primitive.Finite as F
open import System.Environment.Primitive using (getArgs)

open import OwnershipIO using (RunningIO)
open import OwnershipIO.FFI using (failIO; mkdirP; IORef; newIORef; readIORef; writeIORef)
open import OwnershipIO.MetaFFI using (_>>_; writeUTF8)
open import Backend.Mode using (BackendMode; parseBackendMode; leanPrism)
open import Backend.Switch using (switchDump; switchCheck)
open import Code using (Code; modName; decls; mkQ; _==ˢ_; _==ᴺ_; closedImplOK)
open import Code.Transport using (nullᵇ; CheckResult; pass; fail; specΔ; refuteStubOf)
open import Code.Protocol using (AIReq; AIReply; bindNode; forkNode; propose; accept; aiReply; dumpSubmission; agdaCheck; checkRequest; independenceCheck)
open import Code.Render using (render)
open import Code.Prompt using (showRefuteProblem)
open import Code.SessionProtocol
open import Code.SessionRunner using (sessionConfig; ActionResult; accepted; rejected; executeAction)
open import Code.AI using (ScriptedBackend; ServiceBackend)
import Code.Countermodel as CM

private
  assert : Bool → String → IO ⊤
  assert true  _ = return tt
  assert false e = failIO ("ASSERTION FAILED: " ++ˢ e)

  expectDump : BackendMode → String → String → List Code → String → IO Code
  expectDump mode repo scratch deps src =
    switchDump mode (repo ++ˢ "/dump/dump") repo scratch [] (dumpSubmission src [] deps) >>= λ where
      (Code.Protocol.dumped c)   → return c
      (Code.Protocol.dumpFailed e) → failIO ("unexpected dump failure:\n" ++ˢ e)

  -- Verify the full two-stage countermodel protocol through Backend.Switch in a chosen BackendMode.
  runCountermodelSwitch : BackendMode → String → String → Bool → List Code → String → String → String → IO String
  runCountermodelSwitch mode repo scratch expectOK bases specSrc modelSrc refuteSrc = do
    specC ← switchDump mode (repo ++ˢ "/dump/dump") repo scratch [] (Code.Protocol.dumpReq specSrc [] bases) >>= λ where
      (Code.Protocol.dumped c)   → return c
      (Code.Protocol.dumpFailed e) → failIO ("spec dump failed:\n" ++ˢ e)
    let stub = refuteStubOf (specΔ (modName specC) (decls specC) [])
    switchDump mode (repo ++ˢ "/dump/dump") repo scratch [] (dumpSubmission modelSrc [] (CM.countermodelLib ∷ [])) >>= λ where
      (Code.Protocol.dumpFailed e) →
        let tagged = "@model dump failed:\n" ++ˢ e in
        if expectOK then failIO tagged else return tagged
      (Code.Protocol.dumped modelC) → case CM.validCountermodel [] modelC of λ where
        ps@(_ ∷ _) →
          let tagged = "validCountermodel failed:\n" ++ˢ unlines (map showRefuteProblem ps) in
          if expectOK then failIO tagged else return tagged
        [] → case CM.firstBundleUnit modelC of λ where
          nothing → if expectOK then failIO "missing bundle unit" else return "missing bundle"
          (just bName) → switchCheck mode repo scratch [] (agdaCheck modelC (CM.countermodelLib ∷ [])) >>= λ where
            (fail e) →
              let tagged = "@model ordinaryCheck failed:\n" ++ˢ e in
              if expectOK then failIO tagged else return tagged
            pass → do
              let bridge  = CM.countermodelBridge (modName modelC) bName
                  allDeps = stub ∷ bases ++ (CM.countermodelLib ∷ modelC ∷ bridge ∷ [])
              switchDump mode (repo ++ˢ "/dump/dump") repo scratch [] (dumpSubmission refuteSrc [] allDeps) >>= λ where
                (Code.Protocol.dumpFailed e) →
                  let tagged = "@refute dump failed:\n" ++ˢ e in
                  if expectOK then failIO tagged else return tagged
                (Code.Protocol.dumped refuteC) →
                  case CM.validCountermodelRefute (modName specC) (map modName bases) (modName modelC) [] refuteC of λ where
                    ps@(_ ∷ _) →
                      let tagged = "validCountermodelRefute failed:\n" ++ˢ unlines (map showRefuteProblem ps) in
                      if expectOK then failIO tagged else return tagged
                    [] → switchCheck mode repo scratch []
                           (checkRequest refuteC allDeps (independenceCheck (modName specC) [] specSrc refuteSrc)) >>= λ where
                      (fail e) →
                        let tagged = "@refute independenceCheck failed:\n" ++ˢ e in
                        if expectOK then failIO tagged else return tagged
                      pass →
                        if expectOK then return "OK" else failIO "expected countermodel rejection, but check passed!"

  -- Drive a full SessionRunner tree action using scripted node replies:
  -- args: session <repo> <ws> <actionFile> <node1> <replyFile1> [<node2> <replyFile2> ...]
  addReply : String → String → List (String × List String) → List (String × List String)
  addReply n txt [] = (n , (txt ∷ [])) ∷ []
  addReply n txt ((k , rs) ∷ rest) =
    if k ==ˢ n then (k , (rs ++ (txt ∷ []))) ∷ rest
    else (k , rs) ∷ addReply n txt rest

  loadReplies : List String → IO (List (String × List String))
  loadReplies [] = return []
  loadReplies (n ∷ f ∷ rest) = F.readFile f >>= λ txt → loadReplies rest >>= λ more →
    return (addReply n txt more)
  loadReplies _ = failIO "odd reply arguments"

  takeReply : String → List (String × List String) → Maybe String × List (String × List String)
  takeReply _ [] = nothing , []
  takeReply n ((k , rs) ∷ rest) =
    if k ==ˢ n then (case rs of λ where
      []       → nothing , ((k , []) ∷ rest)
      (x ∷ xs) → just x  , ((k , xs) ∷ rest))
    else (let res , more = takeReply n rest in res , ((k , rs) ∷ more))

  popReply : IORef (List (String × List String)) → String → IO String
  popReply ref n = readIORef ref >>= λ tbl → case takeReply n tbl of λ where
    (nothing , _)    → failIO ("missing scripted reply for node " ++ˢ n)
    (just r  , tbl′) → writeIORef ref tbl′ >> return r

  nodeService : IORef (List (String × List String)) → IO (RunningIO AIReq AIReply (⊤ × ⊤))
  nodeService tblRef = newIORef "" >>= λ slotRef → return (record { onCall = handleReq slotRef ; onStop = return (tt , tt) })
    where
      handleReq : IORef String → AIReq → IO AIReply
      handleReq slotRef (bindNode n _) = writeIORef slotRef n >> return (aiReply "" n)
      handleReq _       (forkNode n)   = return (aiReply "" n)
      handleReq _       (accept _)     = return (aiReply "" "")
      handleReq slotRef (propose _ _ _) = readIORef slotRef >>= λ n → popReply tblRef n >>= λ txt → return (aiReply txt n)

  runSession : String → String → String → List String → IO ⊤
  runSession repo ws actionFile replyArgs = do
    actTxt ← F.readFile actionFile
    table  ← loadReplies replyArgs
    tblRef ← newIORef table
    case parseSessionAction actTxt of λ where
      nothing → failIO ("invalid session-action in " ++ˢ actionFile)
      (just act) → do
        let cfg = sessionConfig repo ws "Verify countermodel session." (refSpec (local "/bin/true") [] 10000)
                    (ScriptedBackend []) (λ _ → ServiceBackend (nodeService tblRef))
        executeAction cfg act >>= λ where
          (accepted msg) → F.putStrLn ("ACCEPTED: " ++ˢ msg)
          (Code.SessionRunner.finished msg) → F.putStrLn ("FINISHED: " ++ˢ msg)
          (rejected msg) → failIO ("REJECTED: " ++ˢ msg)

  loadBases : BackendMode → String → String → List String → IO (List Code)
  loadBases _ _ _ [] = return []
  loadBases mode repo scratch (f ∷ fs) = do
    txt ← F.readFile f
    bases ← loadBases mode repo scratch fs
    c ← expectDump mode repo scratch bases txt
    return (bases ++ (c ∷ []))

  cli : List String → IO ⊤
  cli ("self" ∷ []) = do
    assert (modName CM.countermodelLib ==ᴺ CM.countermodelMod) "countermodelLib modName"
    assert (nullᵇ (closedImplOK ("--safe" ∷ []) CM.countermodelLib)) "countermodelLib closedImplOK"
    let b = CM.countermodelBridge (mkQ ("DemoModel" ∷ [])) "bundle"
    assert (modName b ==ᴺ CM.bridgeMod) "bridge modName"
    assert (nullᵇ (closedImplOK ("--safe" ∷ []) b)) "bridge closedImplOK"
    F.putStrLn "COUNTERMODEL_SELF_OK"
  cli ("check" ∷ modeStr ∷ expectStr ∷ repo ∷ scratch ∷ specFile ∷ modelFile ∷ refuteFile ∷ baseFiles) = do
    let mode = maybe′ (λ m → m) leanPrism (parseBackendMode modeStr)
        expectOK = expectStr ==ˢ "pass"
    mkdirP scratch
    bases ← loadBases mode repo scratch baseFiles
    specSrc ← F.readFile specFile
    modelSrc ← F.readFile modelFile
    refuteSrc ← F.readFile refuteFile
    out ← runCountermodelSwitch mode repo scratch expectOK bases specSrc modelSrc refuteSrc
    F.putStrLn out
  cli ("session" ∷ repo ∷ ws ∷ actionFile ∷ replyArgs) =
    mkdirP ws >> runSession repo ws actionFile replyArgs
  cli _ = failIO "usage: CountermodelGateTest [self | check <mode> <pass|fail> <repo> <scratch> <spec> <model> <refute> [base...] | session <repo> <ws> <action> [<node> <reply>...]]"

main : IO ⊤
main = getArgs >>= cli
