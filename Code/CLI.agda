{-# OPTIONS --guardedness #-}
module Code.CLI where

open import Data.Nat using (zero)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; unlines) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import OwnershipIO using (dropModel; onCall)
open import OwnershipIO.FFI
open import OwnershipIO.MetaFFI using (withPrivateTemp; withTreeLock; replaceDuring)
open import Code
open import Code.Shape
open import Code.Tree using (codeOf; codesOf; HomeSt)
open import Code.Transport
open import Code.Protocol
open import Code.Lift
open import Code.Parse using (parseLift)
open import Code.Render using (render)
open import Code.Codecs
open import Code.Prompt using (showImplProblem; liftObstructionSummary)
open import Code.AI using (Backend; CodexCLIBackend; ScriptedBackend; defaultCodex; nodeCodex; sessionCodex)
open import Code.SessionRunner using (runNode; runScript; runSessionScript; runAutonomousSession; sessionConfig)
open import Code.SessionProtocol using (parseRefSpec)
open import Backend.Switch using (leanPrism; switchDumpTool; switchAgdaTool; switchNodeEnvironment)
import Store.CAS as CAS

failWith : String → IO.IO ⊤
failWith s = F.putStrLn s IO.>>= λ _ → exitFailure

runTaskIn : (repo : String) → Backend → String → String → List Code → Maybe (Code × LiftSpec) → IO.IO ⊤
runTaskIn repo backend specFile state bases lifting with Data.List.concatMap (λ c → closedImplOK (flagsOf c) c) bases
... | ps@(_ ∷ _) = failWith ("CLI: unsafe ancestor implementation:\n" ++ˢ unlines (map showImplProblem ps))
... | [] = enableLineBuffering IO.>>= λ _ → F.readFile specFile IO.>>= λ rawSrc →
  let dump = onCall (switchDumpTool leanPrism dumpBin repo (scratch ++ˢ "/dump") []) in
  dump (dumpReq rawSrc [] bases) IO.>>= λ where
    (dumpFailed e) → failWith e
    (dumped spec) → checkSpec rawSrc spec (specProblem (decls spec)) (specImplOK [] spec)
  where
    scratch = repo ++ˢ "/tmp/cli"
    dumpBin = repo ++ˢ "/dump/dump"
    cas = state ++ˢ "/cas"

    checkSpec : String → Code → Maybe String → List ImplProblem → IO.IO ⊤
    execute : String → Code → Maybe HomeValue → IO.IO ⊤
    checkSpec _ _ (just e) _ = failWith e
    checkSpec _ _ nothing ps@(_ ∷ _) = failWith ("CLI: specification closedImplOK:\n" ++ˢ unlines (map showImplProblem ps))
    checkSpec rawSrc spec nothing [] =
      onCall (switchAgdaTool leanPrism repo (scratch ++ˢ "/spec-check") [])
        (agdaCheck (specCheckOf (specΔ (modName spec) (decls spec) [])) bases) IO.>>= λ where
          (fail e) → failWith ("CLI: specification failed Agda typecheck:\n" ++ˢ e)
          pass → withTreeLock state (loadHome state IO.>>= execute rawSrc spec)

    persist : Verdict → HomeValue → IO.IO ⊤
    persist ok result = CAS.storeHomeCAS cas result IO.>>= λ key → CAS.loadHomeCAS cas key IO.>>= λ where
      nothing → failWith "CLI: cannot verify CAS snapshot"
      (just _) → (withPrivateTemp cas λ stage →
        CAS.writeRef stage "current" key IO.>>= λ _ →
        replaceDuring (stage ++ˢ "/refs/current") (cas ++ˢ "/refs/current") (storeHome state result))
        IO.>>= λ _ → F.putStrLn "just ok"
    persist (contradiction c) result = storeHome state result IO.>>= λ _ → F.putStrLn ("contradiction:\n" ++ˢ render c)
    persist (liftObstruction why culprits c) result = F.putStrLn (liftObstructionSummary why culprits ++ˢ "\n" ++ˢ render c)

    persist (independent why c) result = storeHome state result IO.>>= λ _ →
      F.putStrLn ("independent" ++ˢ (if why ==ˢ "" then "" else " — " ++ˢ why) ++ˢ ":\n" ++ˢ render c)

    execute rawSrc spec saved = start (chosen saved)
      where
        d = specΔ (modName spec) (decls spec) []
        chosen : Maybe HomeValue → HomeValue
        chosen nothing = node [] , stubOf d , [] , newIface d , tt
        chosen (just h) = h
        start : HomeValue → IO.IO ⊤
        start h@(sh , home) =
          let old = codeOf sh (dropModel (homeNoChan sh) home)
              seed = map (λ u → if elemᵇ _==ᴼ_ (unit (uname u)) (objects old)
                                   then keep (ext (uname u)) else Code.⊥ ⇝ ext (uname u)) (units (stubOf d))
              task = record (nodeTask (record d { δarrows = seed }) (flagsOf spec) lifting)
                { baseModules = bases ; rawSpecSource = rawSrc }
          in
          switchNodeEnvironment leanPrism backend repo dumpBin (scratch ++ˢ "/tools") [] IO.>>= λ env →
          runNode env task h IO.>>= λ { (verdict , result) → persist verdict result }

runTask : String → String → List Code → Maybe (Code × LiftSpec) → IO.IO ⊤
runTask specFile state bases lifting = currentDirectory IO.>>= λ repo →
  runTaskIn repo (CodexCLIBackend (nodeCodex repo (repo ++ˢ "/tmp/cli") [])) specFile state bases lifting

runLift : String → String → String → String → IO.IO ⊤
runLift spec state basePath liftFile = loadHome basePath IO.>>= λ where
    nothing → failWith "Cannot load the base HomeShape"
    (just (sh , home)) → F.readFile liftFile IO.>>= λ txt → parse sh home (parseLift txt)
  where
    parse : (sh : HomeShape) → OwnershipIO.ModelIO (HomeSt sh) → Maybe LiftSpec → IO.IO ⊤
    parse sh home nothing = failWith "Invalid LiftSpec"
    parse sh home (just l) = let m = dropModel (homeNoChan sh) home in runTask spec state (codesOf sh m) (just (codeOf sh m , l))

runFile : String → IO.IO ⊤
runFile file = currentDirectory IO.>>= λ cwd → F.readFile file IO.>>= λ src →
  runScript (cwd ++ˢ "/tmp/scripts") (cwd ∷ "/usr/share/agda-stdlib" ∷ []) src IO.>>= λ where
    (procResult zero out err) → F.putStrLn (out ++ˢ err)
    (procResult _ out err) → failWith (out ++ˢ err)

runSessionProbe : String → String → String → IO.IO ⊤
runSessionProbe workspace refFile scriptFile = currentDirectory IO.>>= λ repo →
  absolutePath workspace IO.>>= λ ws → F.readFile refFile IO.>>= λ config →
  F.readFile scriptFile IO.>>= λ src →
  dispatch repo ws src (parseRefSpec config)
  where
    dispatch : String → String → String → Maybe Code.SessionProtocol.RefSpec → IO.IO ⊤
    dispatch _ _ _ nothing = failWith "Invalid ref-target config"
    dispatch repo ws src (just ref) =
      runSessionScript (sessionConfig repo ws "" ref (ScriptedBackend []) (λ _ → ScriptedBackend [])) src IO.>>= λ where
        (procResult zero out err) → F.putStr (out ++ˢ err)
        (procResult _ out err) → failWith (out ++ˢ err)

runSession : String → String → String → IO.IO ⊤
runSession workspace goalFile refFile = currentDirectory IO.>>= λ repo →
  absolutePath workspace IO.>>= λ ws → absolutePath refFile IO.>>= λ absRef →
  F.readFile goalFile IO.>>= λ goal →
  F.readFile absRef IO.>>= λ config → dispatch repo ws absRef goal (parseRefSpec config)
  where
    dispatch : String → String → String → String → Maybe Code.SessionProtocol.RefSpec → IO.IO ⊤
    dispatch repo ws absRef goal nothing = failWith "Invalid ref-target config; use (ref-target (local \"/bin/cat\")) or (ref-target (docker \"image\" \"/executable\"))"
    dispatch repo ws absRef goal (just ref) = runAutonomousSession (sessionConfig repo ws goal ref
      (CodexCLIBackend (sessionCodex repo ws absRef))
      (λ name → CodexCLIBackend (nodeCodex repo (ws ++ˢ "/trees/" ++ˢ name) [])))
