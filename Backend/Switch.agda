{-# OPTIONS --guardedness #-}
module Backend.Switch where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Char.Base using (Char; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; reverse)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; intersperse; toList; fromList) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
import IO.Primitive as Prim
import IO.Primitive.Finite as PF
open import Agda.Builtin.Char using (primCharEquality)
open import Function.Base using (case_of_)

open import OwnershipIO using (RunningIO; EnvIO; onCall)
open import OwnershipIO.FFI using (mkdirP; fileExists; dirExists; listDirectory; absolutePath; failIO; readProcessAt; ProcResult; procResult; stripStdlibWarnings)
open import OwnershipIO.MetaFFI using (withPrivateTemp; writeUTF8; catchIO; copyReadOnly; sealDirectory)
open import Code using (Code; full; modName; eqList; anyᵇ; filterᵇ; _==ˢ_; closedImplOK; flagsOK; flagsOf; ImplProblem; flagEnvelopeViolation)
open import Code.SExpr using (SExpr; list; str; sym)
open import Code.Encode using (encodeCanonical; encodeCode)
open import Code.Parse using (parse)
open import Code.Render using (render)
open import Code.AgdaTool using (parentPath)
open import Code.Protocol using (AIReq; AIReply; AgdaCheckReq; agdaCheck; DumpReq; dumpReq; DumpResult; dumped; dumpFailed)
open import Code.Transport using (CheckResult; pass; fail; nullᵇ)
open import Code.Harness using (NodeΨ)
open import Code.AI using (Backend; aiService; isConcurrentBackend; withBackendAncestors)
open import Code.Driver using (nodeEnvironmentWith; nodeEnvironmentForBackend)
open import Meta.Boundary using (ModulePath; checkModulePaths; checkObjectModuleSafe)
import Meta.Sandbox as Sandbox
open Sandbox using (codeView)

open import Backend.Mode public
open import Backend.PrismFFI public using (lookupEnv; resolveBackendMode)

private
  infixl 1 _>>=_ _>>_
  _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → (A → Prim.IO B) → Prim.IO B
  _>>=_ = Prim._>>=_
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → Prim.IO B → Prim.IO B
  m >> n = m >>= λ _ → n
  return : ∀ {a} {A : Set a} → A → Prim.IO A
  return = Prim.return

  infixl 6 _/_
  _/_ : String → String → String
  a / b = a ++ˢ "/" ++ˢ b

  -- Exit codes emitted by `runtime/lean-prism/.lake/build/bin/agda2lean`:
  exitSyntaxErr : ℕ
  exitSyntaxErr = 10

  exitTypeErr : ℕ
  exitTypeErr = 11

  exitBot : ℕ
  exitBot = 20

  prismBinPath : String → String
  prismBinPath repo = repo / "runtime/lean-prism/.lake/build/bin/agda2lean"

  prismLibDir : String → String
  prismLibDir repo = repo / "runtime/lean-prism/.lake/build/lib/lean"

  prismIrDir : String → String
  prismIrDir repo = repo / "runtime/lean-prism/.lake/build/ir"

  harnessEnginePath : String → String
  harnessEnginePath repo = repo / "runtime/lean-prism/.lake/build/bin/harness-engine"

  dumpBinFlags : String → Prim.IO (List String)
  dumpBinFlags repo =
    let p = repo / "dump/dump" in
    fileExists p >>= λ ok →
      if ok then (absolutePath p >>= λ absP → return ("--dump-bin" ∷ absP ∷ []))
      else return []

  endsWithAgda : String → Bool
  endsWithAgda s = go (reverse (toList ".agda")) (reverse (toList s))
    where
      go : List Char → List Char → Bool
      go [] _ = true
      go (_ ∷ _) [] = false
      go (x ∷ xs) (y ∷ ys) = primCharEquality x y ∧ go xs ys

  {-# NON_TERMINATING #-}
  walkAgdaFiles : String → Prim.IO (List String)
  walkAgdaFiles dir = dirExists dir >>= λ ex →
    if not ex then return []
    else listDirectory dir >>= step
    where
      step : List String → Prim.IO (List String)
      step [] = return []
      step (n ∷ ns) =
        let p = dir / n in
        dirExists p >>= λ isD →
        (if isD then walkAgdaFiles p
         else return (if endsWithAgda p then p ∷ [] else [])) >>= λ here →
        step ns >>= λ more → return (here ++ more)

  walkAllDirs : List String → Prim.IO (List String)
  walkAllDirs [] = return []
  walkAllDirs (d ∷ ds) = walkAgdaFiles d >>= λ fs → walkAllDirs ds >>= λ more → return (fs ++ more)

  SourceUnit : Set
  SourceUnit = ModulePath × String

  rejectPath : ∀ {A : Set} → ModulePath → Prim.IO A
  rejectPath path = failIO ("sandbox: forbidden module name or import in " ++ˢ intersperse "." path)

  prepareSource : Bool → String → Prim.IO SourceUnit
  prepareSource allowMain src = OwnershipIO.MetaFFI.inspectSource src >>= λ where
    (just (path ∷ imports)) → if checkModulePaths allowMain path imports
      then return (path , src) else rejectPath path
    _ → failIO "sandbox: expected a named Agda module"

  prepareCode : Bool → Code → Prim.IO SourceUnit
  prepareCode allowMain c = if checkObjectModuleSafe allowMain c then
    (prepareSource allowMain (render c) >>= λ { unit@(path , _) →
      if eqList _==ˢ_ path (full (modName c)) then return unit else rejectPath path })
    else rejectPath (full (modName c))

  prepareAll : ∀ {A : Set} → (A → Prim.IO SourceUnit) → List A → Prim.IO (List SourceUnit)
  prepareAll _ [] = return []
  prepareAll f (x ∷ xs) = f x >>= λ u → prepareAll f xs >>= λ us → return (u ∷ us)

  relAgdaFile : ModulePath → String
  relAgdaFile path = intersperse "/" path ++ˢ ".agda"

  writeUnits : String → List SourceUnit → Prim.IO (List String)
  writeUnits _ [] = return []
  writeUnits dir ((path , src) ∷ rest) = do
    mkdirP (dir / parentPath path)
    let f = dir / relAgdaFile path
    writeUTF8 f src
    fs ← writeUnits dir rest
    return (f ∷ fs)

  depFlags : List String → List String
  depFlags [] = []
  depFlags (f ∷ fs) = "--dep" ∷ f ∷ depFlags fs

  loadFileUnit : String → Prim.IO SourceUnit
  loadFileUnit f = PF.readFile f >>= prepareSource false

  dedupUnits : List ModulePath → List SourceUnit → List SourceUnit
  dedupUnits _ [] = []
  dedupUnits seen (u@(p , _) ∷ us) =
    if anyᵇ (eqList _==ˢ_ p) seen
      then dedupUnits seen us
      else u ∷ dedupUnits (p ∷ seen) us

  collectAncestorUnits : (repo work : String) → List String → List ModulePath → Prim.IO (List SourceUnit)
  collectAncestorUnits repo work ancestors localPaths =
    if nullᵇ ancestors then return []
    else do
      mkdirP (work / "_ancestors")
      sealedDirs ← Sandbox.sealAncestorsTo repo (work / "_ancestors") ancestors
      agdaFiles ← walkAllDirs sealedDirs
      rawUnits ← prepareAll loadFileUnit agdaFiles
      return (dedupUnits localPaths rawUnits)

------------------------------------------------------------------------
-- §1  Prism Stream Interceptor for `DumpReq` (Raw Agda → Code)
------------------------------------------------------------------------

private
  prismDumpIntercept : (dumpBin repo scratch : String) → List String → DumpReq → Prim.IO DumpResult
  prismDumpIntercept dumpBin repo scratch ancestors req@(dumpReq src rawDeps codeDeps) =
    fileExists (prismBinPath repo) >>= λ hasBin →
    if not hasBin then
      Sandbox.sandboxDump dumpBin repo scratch ancestors req
    else
      catchIO runIntercept λ e → return (dumpFailed e)
    where
      runIntercept : Prim.IO DumpResult
      runIntercept = do
        mainU@(mainPath , _) ← prepareSource false src
        cUnits ← prepareAll (prepareCode false) codeDeps
        sUnits ← prepareAll (λ pair → prepareSource false (proj₂ pair)) rawDeps
        bin ← absolutePath (prismBinPath repo)
        withPrivateTemp scratch λ work → do
          let explicitUnits = cUnits ++ sUnits
              seenPaths = mainPath ∷ map proj₁ explicitUnits
          ancUnits ← collectAncestorUnits repo work ancestors seenPaths
          let srcDir = work / "agda_src"
          mkdirP srcDir
          depPaths ← writeUnits srcDir (ancUnits ++ explicitUnits)
          _ ← writeUnits srcDir (mainU ∷ [])
          let mainFile = srcDir / relAgdaFile mainPath
          readProcessAt work 60000 bin ("prism-dump" ∷ depFlags depPaths ++ ("--main" ∷ mainFile ∷ [])) "" >>= λ where
            (procResult zero out _) →
              case parse out of λ where
                nothing  → Sandbox.sandboxDump dumpBin repo scratch ancestors req
                (just c) →
                  if eqList _==ˢ_ (full (modName c)) mainPath ∧ checkObjectModuleSafe false c
                    then return (dumped c)
                    else rejectPath mainPath
            (procResult code out err) →
              if code ≡ᵇ exitBot then
                Sandbox.sandboxDump dumpBin repo scratch ancestors req
              else if code ≡ᵇ exitSyntaxErr then
                return (dumpFailed (stripStdlibWarnings (out ++ˢ err)))
              else
                Sandbox.sandboxDump dumpBin repo scratch ancestors req
        where open import Function.Base using (case_of_)

switchDump : BackendMode → (dumpBin repo scratch : String) → List String → DumpReq → Prim.IO DumpResult
switchDump legacyAgda dumpBin repo scratch ancestors req =
  Sandbox.sandboxDump dumpBin repo scratch ancestors req
switchDump leanPrism dumpBin repo scratch ancestors req =
  prismDumpIntercept dumpBin repo scratch ancestors req
switchDump shadowAudit dumpBin repo scratch ancestors req = do
  pRes ← prismDumpIntercept dumpBin repo scratch ancestors req
  aRes ← Sandbox.sandboxDump dumpBin repo scratch ancestors req
  verify pRes aRes
  where
    verify : DumpResult → DumpResult → Prim.IO DumpResult
    verify (dumped c₁) (dumped c₂) =
      if encodeCanonical c₁ ==ˢ encodeCanonical c₂
        then return (dumped c₁)
        else return (dumpFailed "SHADOW_AUDIT_VIOLATION: canonical Code mismatch between LeanPrism and LegacyAgda")
    verify (dumpFailed _) (dumpFailed e) = return (dumpFailed e)
    verify (dumped _) (dumpFailed e) =
      return (dumpFailed ("SHADOW_AUDIT_VIOLATION: LeanPrism accepted invalid Agda rejected by LegacyAgda:\n" ++ˢ e))
    verify (dumpFailed e) (dumped _) =
      return (dumpFailed ("SHADOW_AUDIT_VIOLATION: LeanPrism falsely rejected valid Agda:\n" ++ˢ e))

------------------------------------------------------------------------
-- §2  Prism Stream Interceptor for `AgdaCheckReq` (Code + Deps → CheckResult)
------------------------------------------------------------------------

private
  prismCheckIntercept : (repo scratch : String) → List String → AgdaCheckReq → Prim.IO CheckResult
  prismCheckIntercept repo scratch ancestors req@(agdaCheck mainC depCs) =
    fileExists (prismBinPath repo) >>= λ hasBin →
    if not hasBin then
      Sandbox.sandboxAgdaCheck repo scratch ancestors req
    else
      catchIO runIntercept λ e → return (fail e)
    where
      runIntercept : Prim.IO CheckResult
      runIntercept = do
        mainU@(mainPath , _) ← prepareCode false mainC
        depUnits ← prepareAll (prepareCode false) depCs
        bin ← absolutePath (prismBinPath repo)
        lib ← absolutePath (prismLibDir repo)
        dbFlags ← dumpBinFlags repo
        withPrivateTemp scratch λ work → do
          let seenPaths = mainPath ∷ map proj₁ depUnits
          ancUnits ← collectAncestorUnits repo work ancestors seenPaths
          let srcDir = work / "agda_src"
              leanWork = work / "lean_work"
          mkdirP srcDir
          mkdirP leanWork
          depPaths ← writeUnits srcDir (ancUnits ++ depUnits)
          _ ← writeUnits srcDir (mainU ∷ [])
          let mainFile = srcDir / relAgdaFile mainPath
          readProcessAt work 120000 bin
            ("prism-check" ∷ "--lib-dir" ∷ lib ∷ "--work-dir" ∷ leanWork
             ∷ dbFlags ++ depFlags depPaths ++ ("--main" ∷ mainFile ∷ [])) "" >>= λ where
            (procResult zero _ _) → return pass
            (procResult code out err) →
              if code ≡ᵇ exitBot then
                Sandbox.sandboxAgdaCheck repo scratch ancestors req
              else if (code ≡ᵇ exitSyntaxErr) then
                return (fail (stripStdlibWarnings (out ++ˢ err)))
              else if (code ≡ᵇ exitTypeErr) then
                return (fail (stripStdlibWarnings (out ++ˢ err)))
              else
                Sandbox.sandboxAgdaCheck repo scratch ancestors req

switchCheck : BackendMode → (repo scratch : String) → List String → AgdaCheckReq → Prim.IO CheckResult
switchCheck legacyAgda repo scratch ancestors req =
  Sandbox.sandboxAgdaCheck repo scratch ancestors req
switchCheck leanPrism repo scratch ancestors req =
  prismCheckIntercept repo scratch ancestors req
switchCheck shadowAudit repo scratch ancestors req = do
  pRes ← prismCheckIntercept repo scratch ancestors req
  aRes ← Sandbox.sandboxAgdaCheck repo scratch ancestors req
  verify pRes aRes
  where
    verify : CheckResult → CheckResult → Prim.IO CheckResult
    verify pass pass = return pass
    verify (fail _) (fail e) = return (fail e)
    verify pass (fail e) =
      return (fail ("SHADOW_AUDIT_VIOLATION: LeanPrism passed invalid module rejected by LegacyAgda:\n" ++ˢ e))
    verify (fail e) pass =
      return (fail ("SHADOW_AUDIT_VIOLATION: LeanPrism rejected valid module accepted by LegacyAgda:\n" ++ˢ e))

------------------------------------------------------------------------
-- §3  Prism Native Executable Compiler (`build-exe` Replacement + Entry Gate)
------------------------------------------------------------------------

-- Walk encoded AST of a candidate `build-exe` entrypoint to forbid shelling out
-- via `OwnershipIO.FFI.readProcess` / `readProcessAt` or touching internal host FFI.
mutual
  private
    allowedFFISymbol : String → Bool
    allowedFFISymbol "OwnershipIO.FFI.readStdin"           = true
    allowedFFISymbol "OwnershipIO.FFI.exitFailure"         = true
    allowedFFISymbol "OwnershipIO.FFI.enableLineBuffering" = true
    allowedFFISymbol _                                     = false

    startsWithPrefix : List Char → List Char → Bool
    startsWithPrefix []       _        = true
    startsWithPrefix (_ ∷ _)  []       = false
    startsWithPrefix (x ∷ xs) (y ∷ ys) = primCharEquality x y ∧ startsWithPrefix xs ys

    forbiddenEntrySExpr : SExpr → Maybe String
    forbiddenEntrySExpr (str s) =
      if startsWithPrefix (toList "OwnershipIO.FFI.") (toList s) ∧ not (allowedFFISymbol s)
        then just ("build-exe: forbidden host FFI primitive '" ++ˢ s ++ˢ "' (use OwnershipIO.WorldRunner instead of shelling out)")
        else nothing
    forbiddenEntrySExpr (sym _) = nothing
    forbiddenEntrySExpr (Code.SExpr.num _) = nothing
    forbiddenEntrySExpr (list xs) = forbiddenEntryList xs

    forbiddenEntryList : List SExpr → Maybe String
    forbiddenEntryList [] = nothing
    forbiddenEntryList (x ∷ xs) with forbiddenEntrySExpr x
    ... | just err = just err
    ... | nothing  = forbiddenEntryList xs

checkCandidateEntrySafe : Code → Maybe String
checkCandidateEntrySafe c =
  if not (checkObjectModuleSafe true c) then
    just ("build-exe: forbidden module name or import in " ++ˢ intersperse "." (full (modName c))
          ++ˢ " (only Gen.*, stdlib, Context.*, and OwnershipIO.WorldRunner are allowed)")
  else forbiddenEntrySExpr (encodeCode c)

private
  copyHostView : String → String → Prim.IO String
  copyHostView repo work = do
    let hostDir = work / "_world_runner"
    mkdirP (hostDir / "OwnershipIO")
    copyReadOnly (repo / "OwnershipIO/WorldRunner.agda") (hostDir / "OwnershipIO/WorldRunner.agda")
    copyReadOnly (repo / "OwnershipIO/FFI.agda") (hostDir / "OwnershipIO/FFI.agda")
    sealDirectory (hostDir / "OwnershipIO")
    sealDirectory hostDir
    return hostDir

  legacyCompileExe : (repo scratch outBin : String) → Code → List Code → Prim.IO CheckResult
  legacyCompileExe repo scratch outBin mainC depCs =
    catchIO buildLegacy λ e → return (fail e)
    where
      buildLegacy : Prim.IO CheckResult
      buildLegacy = case checkCandidateEntrySafe mainC of λ where
        (just err) → return (fail err)
        nothing → do
          mainU@(mainPath , _) ← prepareCode true mainC
          depUnits ← prepareAll (prepareCode false) depCs
          outAbs ← absolutePath outBin
          cliHostC ← absolutePath (repo / "runtime/cli_host.c")
          Sandbox.withWhitelistView repo scratch [] λ includes →
            withPrivateTemp scratch λ work → do
              hostDir ← copyHostView repo work
              writeUTF8 (work / "object.agda-lib") "name: object-view\ninclude: .\n"
              let config = work / ".agda"
                  buildDir = work / "build"
              mkdirP config
              mkdirP buildDir
              _ ← writeUnits work (depUnits ++ (mainU ∷ []))
              let incArgs = concatMap (λ i → "-i" ∷ i ∷ []) (work ∷ hostDir ∷ includes)
                  exeName = Data.List.Base.foldl (λ _ s → s) "Main" mainPath
              readProcessAt work 240000 "/usr/bin/env"
                (("AGDA_DIR=" ++ˢ config) ∷ "agda" ∷ "--no-libraries" ∷ "--compile"
                 ∷ "--ghc-flag=-O0" ∷ "--ghc-flag=-optl-static" ∷ "--ghc-flag=-optl-pthread"
                 ∷ ("--ghc-flag=" ++ˢ cliHostC)
                 ∷ "--compile-dir=build"
                 ∷ "--ghc-flag=-outputdir" ∷ "--ghc-flag=build"
                 ∷ incArgs ++ (("./" ++ˢ relAgdaFile mainPath) ∷ [])) "" >>= λ where
                (procResult (suc _) out err) → return (fail (stripStdlibWarnings (out ++ˢ err)))
                (procResult zero _ _) →
                  let built = buildDir / exeName in
                  fileExists built >>= λ ok →
                    if ok then (readProcessAt work 10000 "chmod" ("0755" ∷ built ∷ []) "" >>
                                OwnershipIO.FFI.atomicRename built outAbs >> return pass)
                    else return (fail "legacy build-exe: module did not produce executable binary")

  prismCompileExe : (repo scratch outBin : String) → Code → List Code → Prim.IO CheckResult
  prismCompileExe repo scratch outBin mainC depCs =
    case checkCandidateEntrySafe mainC of λ where
      (just err) → return (fail err)
      nothing →
        fileExists (prismBinPath repo) >>= λ hasBin →
        if not hasBin then
          legacyCompileExe repo scratch outBin mainC depCs
        else
          catchIO buildFast λ e → return (fail e)
    where
      buildFast : Prim.IO CheckResult
      buildFast = do
        mainU@(mainPath , _) ← prepareCode true mainC
        depUnits ← prepareAll (prepareCode false) depCs
        bin ← absolutePath (prismBinPath repo)
        lib ← absolutePath (prismLibDir repo)
        ir  ← absolutePath (prismIrDir repo)
        dbFlags ← dumpBinFlags repo
        outAbs ← absolutePath outBin
        withPrivateTemp scratch λ work → do
          let srcDir = work / "agda_src"
              leanWork = work / "lean_work"
          mkdirP srcDir
          mkdirP leanWork
          depPaths ← writeUnits srcDir depUnits
          _ ← writeUnits srcDir (mainU ∷ [])
          let mainFile = srcDir / relAgdaFile mainPath
          readProcessAt work 180000 bin
            ("prism-build" ∷ "--lib-dir" ∷ lib ∷ "--ir-dir" ∷ ir
             ∷ "--work-dir" ∷ leanWork ∷ "--out" ∷ outAbs
             ∷ dbFlags ++ depFlags depPaths ++ ("--main" ∷ mainFile ∷ [])) "" >>= λ where
            (procResult zero _ _) → return pass
            (procResult code out err) →
              if code ≡ᵇ exitBot then
                legacyCompileExe repo scratch outBin mainC depCs
              else
                return (fail (stripStdlibWarnings (out ++ˢ err)))

switchCompileExe : BackendMode → (repo scratch outBin : String) → Code → List Code → Prim.IO CheckResult
switchCompileExe legacyAgda repo scratch outBin mainC depCs =
  legacyCompileExe repo scratch outBin mainC depCs
switchCompileExe leanPrism repo scratch outBin mainC depCs =
  prismCompileExe repo scratch outBin mainC depCs
switchCompileExe shadowAudit repo scratch outBin mainC depCs = do
  pRes ← prismCompileExe repo scratch outBin mainC depCs
  aChk ← Sandbox.sandboxAgdaCheck repo scratch [] (agdaCheck mainC depCs)
  case pRes of λ where
    pass → case aChk of λ where
      pass     → return pass
      (fail e) → return (fail ("SHADOW_AUDIT_VIOLATION: LeanPrism built binary rejected by Agda:\n" ++ˢ e))
    (fail e) → return (fail e)
  where open import Function.Base using (case_of_)

-- Open-world session `build-exe` router: checks `closedImplOK` (with `--guardedness` allowed
-- for `IO`) and compiles `entryFile` + `exportedDepFiles` via `agda2lean prism-build` (`leanc -O3`)
-- in `leanPrism` mode without invoking legacy `agda`, falling back seamlessly to `legacyBuild`
-- only on module-level `exitBot` (`20`, e.g. if `entryFile` imports `Ownership`).
switchSessionCompileExe : BackendMode → (repo scratch outBin entryFile : String) → List String →
                          Prim.IO (Maybe String) → Prim.IO CheckResult → Prim.IO CheckResult
switchSessionCompileExe legacyAgda _ _ _ _ _ _ legacyBuild = legacyBuild
switchSessionCompileExe leanPrism repo scratch outBin entryFile depFiles _ legacyBuild =
  fileExists (prismBinPath repo) >>= λ hasBin →
  if not hasBin then legacyBuild
  else catchIO runSessionBuild λ e → return (fail e)
  where
    keepIOProblem : Code → ImplProblem → Bool
    keepIOProblem c flagEnvelopeViolation = not (flagsOK ("--guardedness" ∷ []) (flagsOf c))
    keepIOProblem _ _ = true

    mapAbs : List String → Prim.IO (List String)
    mapAbs [] = return []
    mapAbs (f ∷ fs) = absolutePath f >>= λ af → mapAbs fs >>= λ rest → return (af ∷ rest)

    runSessionBuild : Prim.IO CheckResult
    runSessionBuild = do
      mainSrc ← PF.readFile entryFile
      _ ← prepareSource true mainSrc
      bin ← absolutePath (prismBinPath repo)
      lib ← absolutePath (prismLibDir repo)
      ir  ← absolutePath (prismIrDir repo)
      dbFlags ← dumpBinFlags repo
      outAbs ← absolutePath outBin
      mainAbs ← absolutePath entryFile
      depAbs ← mapAbs depFiles
      mkdirP scratch
      withPrivateTemp scratch λ leanWork →
        readProcessAt leanWork 60000 bin
          ("prism-dump" ∷ dbFlags ++ depFlags depAbs ++ ("--main" ∷ mainAbs ∷ [])) "" >>= λ where
          (procResult zero dOut _) →
            case parse dOut of λ where
              nothing → legacyBuild
              (just entryC) →
                case checkCandidateEntrySafe entryC of λ where
                  (just gateErr) → return (fail gateErr)
                  nothing →
                    if not (nullᵇ (filterᵇ (keepIOProblem entryC) (closedImplOK [] entryC))) then
                      return (fail "closedImplOK []: source contains an axiom, hole, unsafe pragma or unclosed definition")
                    else
                      readProcessAt leanWork 180000 bin
                        ("prism-build" ∷ "--lib-dir" ∷ lib ∷ "--ir-dir" ∷ ir
                         ∷ "--work-dir" ∷ leanWork ∷ "--out" ∷ outAbs
                         ∷ dbFlags ++ depFlags depAbs ++ ("--main" ∷ mainAbs ∷ [])) "" >>= λ where
                        (procResult zero _ _) → return pass
                        (procResult code out err) →
                          if code ≡ᵇ exitBot then legacyBuild
                          else return (fail (stripStdlibWarnings (out ++ˢ err)))
          (procResult dCode dOut dErr) →
            if dCode ≡ᵇ exitBot then legacyBuild
            else if dCode ≡ᵇ exitSyntaxErr then return (fail (stripStdlibWarnings (dOut ++ˢ dErr)))
            else legacyBuild
      where open import Function.Base using (case_of_)
switchSessionCompileExe shadowAudit repo scratch outBin entryFile depFiles auditCheck legacyBuild = do
  aOpt ← auditCheck
  pRes ← switchSessionCompileExe leanPrism repo scratch outBin entryFile depFiles (return nothing) legacyBuild
  case aOpt of λ where
    nothing →
      case pRes of λ where
        pass     → return pass
        (fail e) → return (fail ("SHADOW_AUDIT_VIOLATION: LeanPrism rejected valid session Main accepted by LegacyAgda:\n" ++ˢ e))
    (just ae) →
      case pRes of λ where
        (fail _) → return (fail ae)
        pass     → return (fail ("SHADOW_AUDIT_VIOLATION: LeanPrism accepted invalid session Main rejected by LegacyAgda:\n" ++ˢ ae))
  where open import Function.Base using (case_of_)

------------------------------------------------------------------------
-- §4  Native Lean 4 `harness-engine` Host Router (Layer 2 Self-Compilation)
------------------------------------------------------------------------

private
  chompTrailingNewline : String → String
  chompTrailingNewline s with reverse (toList s)
  ... | '\n' ∷ revRest = fromList (reverse revRest)
  ... | _              = s

runHarnessEngine : BackendMode → (repo : String) → List String → Prim.IO String → Prim.IO String
runHarnessEngine legacyAgda _ _ legacyCompute = legacyCompute
runHarnessEngine leanPrism repo args legacyCompute =
  let bin = harnessEnginePath repo in
  fileExists bin >>= λ hasBin →
  if not hasBin then legacyCompute
  else
    readProcessAt "" 60000 bin args "" >>= λ where
      (procResult zero out _) → return (chompTrailingNewline out)
      _                       → legacyCompute
runHarnessEngine shadowAudit repo args legacyCompute = do
  let bin = harnessEnginePath repo
  hasBin ← fileExists bin
  legOut ← legacyCompute
  if not hasBin then return legOut
    else
      readProcessAt "" 60000 bin args "" >>= λ where
        (procResult zero out _) →
          let prismOut = chompTrailingNewline out in
          if prismOut ==ˢ legOut then return prismOut
          else failIO ("SHADOW_AUDIT_VIOLATION: harness-engine output differs from LegacyAgda on " ++ˢ intersperse " " args)
        (procResult _ out err) →
          failIO ("SHADOW_AUDIT_VIOLATION: harness-engine failed on valid input: " ++ˢ out ++ˢ err)

------------------------------------------------------------------------
-- §4  Drop-In `RunningIO` Tools & `EnvIO NodeΨ` Builders (Env-Var Hot-Switchable)
------------------------------------------------------------------------

switchDumpTool : BackendMode → (dumpBin repo scratch : String) → List String → RunningIO DumpReq DumpResult (⊤ × ⊤)
switchDumpTool defaultMode dumpBin repo scratch ancestorDirs = record
  { onCall = λ req → resolveBackendMode defaultMode >>= λ m → switchDump m dumpBin repo scratch ancestorDirs req
  ; onStop = return (tt , tt) }

switchAgdaTool : BackendMode → (repo scratch : String) → List String → RunningIO AgdaCheckReq CheckResult (⊤ × ⊤)
switchAgdaTool defaultMode repo scratch ancestorDirs = record
  { onCall = λ req → resolveBackendMode defaultMode >>= λ m → switchCheck m repo scratch ancestorDirs req
  ; onStop = return (tt , tt) }

switchNodeEnvironmentUsing : BackendMode → Prim.IO (RunningIO AIReq AIReply (⊤ × ⊤)) →
  (repo dumpBin scratch : String) → List String → Prim.IO (EnvIO NodeΨ)
switchNodeEnvironmentUsing defaultMode ai repo dumpBin scratch ancestorDirs = nodeEnvironmentWith ai
  (onCall (switchDumpTool defaultMode dumpBin repo (scratch ++ˢ "/dump") ancestorDirs))
  (onCall (switchAgdaTool defaultMode repo (scratch ++ˢ "/agda") ancestorDirs))

switchNodeEnvironment : BackendMode → Backend → (repo dumpBin scratch : String) → List String → Prim.IO (EnvIO NodeΨ)
switchNodeEnvironment defaultMode backend repo dumpBin scratch ancestorDirs =
  let b′ = withBackendAncestors repo ancestorDirs backend in
  nodeEnvironmentForBackend (isConcurrentBackend b′) (aiService b′)
    (onCall (switchDumpTool defaultMode dumpBin repo (scratch ++ˢ "/dump") ancestorDirs))
    (onCall (switchAgdaTool defaultMode repo (scratch ++ˢ "/agda") ancestorDirs))
