{-# OPTIONS --guardedness #-}
module Backend.Switch where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_; not)
open import Data.Char.Base using (Char; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; reverse)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; unlines; intersperse; toList; fromList) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
import IO.Primitive as Prim
import IO.Primitive.Finite as PF
open import Agda.Builtin.Char using (primCharEquality)
open import Function.Base using (case_of_)

open import OwnershipIO using (RunningIO; EnvIO; onCall)
open import OwnershipIO.FFI using (mkdirP; fileExists; dirExists; listDirectory; absolutePath; failIO; readProcessAt; ProcResult; procResult; stripStdlibWarnings)
open import OwnershipIO.MetaFFI using (withPrivateTemp; writeUTF8; catchIO; copyReadOnly; sealDirectory; inspectSourceDiag; appendNarrowingEvent)
open import Code using (Code; QName; RefuteProblem; validIndependenceWithBases; full; modName; eqList; anyᵇ; filterᵇ; hasWord; _==ˢ_; _==ᴺ_; closedImplOK; flagsOK; flagsOf; ImplProblem; flagEnvelopeViolation)
open import Code.SExpr using (SExpr; list; str; sym; showSExpr)
open import Code.Encode using (encodeCode; encodeCanonical)
open import Code.Parse using (parse)
open import Code.Render using (render)
import Code.Countermodel as CM
import Code.Namespace as NS
open import Code.Prompt using (showRefuteProblem)
open import Code.AgdaTool using (parentPath)
open import Code.Protocol using (AIReq; AIReply; AgdaCheckReq; CheckPurpose; agdaCheck; checkRequest; ordinaryCheck; independenceCheck; narrowedSubspec; checkPurpose; DumpReq; dumpReq; DumpResult; dumped; dumpFailed)
open import Code.Transport using (refuteStubOf; specΔ; CheckResult; pass; fail; nullᵇ)
open import Code.Harness using (NodeΨ)
open import Code.AI using (Backend; CodexCLIBackend; narrowLog; aiService; isConcurrentBackend; withBackendAncestors; withBackendNarrowLog)
open import Code.Driver using (nodeEnvironmentWith; nodeEnvironmentForBackend)
open import Meta.Boundary using (ModulePath; importPaths; checkModulePaths; checkObjectModuleSafe)
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

  prepareSource : String → Bool → String → Prim.IO SourceUnit
  prepareSource log allowMain src = OwnershipIO.MetaFFI.inspectSource src >>= λ where
    (just (path ∷ imports)) → if checkModulePaths allowMain path imports
      then return (path , src) else Sandbox.rejectModulePaths log path imports
    _ → inspectSourceDiag src >>= λ diag →
      failIO ("sandbox: expected a named Agda module — " ++ˢ diag)

  prepareCode : Bool → Code → Prim.IO SourceUnit
  prepareCode allowMain c = if checkObjectModuleSafe allowMain c then
    (let rendered = render c
         mName = intersperse "." (full (modName c))
     in OwnershipIO.MetaFFI.inspectSource rendered >>= λ where
       (just (path ∷ imports)) →
         if checkModulePaths allowMain path imports ∧ eqList _==ˢ_ path (full (modName c))
           then return (path , rendered) else Sandbox.rejectModulePaths "" path imports
       _ → inspectSourceDiag rendered >>= λ diag →
         appendNarrowingEvent "" "roundtrip_reparse_fail" mName diag >>
         failIO ("sandbox: expected a named Agda module — rendered AST of " ++ˢ mName
                 ++ˢ " failed Agda re-parse (renderer narrowing gate; rewrite the offending literal/syntax shown below):\n" ++ˢ diag))
    else Sandbox.rejectModulePaths "" (full (modName c)) (importPaths c)

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

  validateIR : String → Bool → Code → Prim.IO ⊤
  validateIR log allowMain c = if checkObjectModuleSafe allowMain c then return tt
    else Sandbox.rejectModulePaths log (full (modName c)) (importPaths c)

  validateDeps : String → List Code → Prim.IO ⊤
  validateDeps log [] = return tt
  validateDeps log (c ∷ cs) = validateIR log false c >> validateDeps log cs

  writeBundle : String → Code → List Code → Prim.IO String
  writeBundle dir mainC deps = do
    let path = dir / "bundle.sexp"
    writeUTF8 path (showSExpr (list (sym "bundle" ∷ map encodeCode (deps ++ (mainC ∷ [])))))
    return path

  -- Session callers provide sealed ancestors as Code. Older callers with only
  -- source directories scope those files once at the same frontend boundary.
  ancestorCodes : (log repo work : String) → List String → List ModulePath → Prim.IO (List Code)
  ancestorCodes _ _ _ [] _ = return []
  ancestorCodes log repo work dirs known = Sandbox.withWhitelistView repo work dirs λ where
      includes@(ctx ∷ std ∷ sealed) → do
        files ← walkAllDirs sealed
        bin ← absolutePath (repo / "dump/dump")
        load bin (concatMap (λ i → "-i" ∷ i ∷ []) includes) known files
      _ → failIO "sandbox: missing sealed include directories"
    where
      load : String → List String → List ModulePath → List String → Prim.IO (List Code)
      load bin args seen [] = return []
      load bin args seen (f ∷ fs) = do
        path , _ ← PF.readFile f >>= prepareSource log false
        if anyᵇ (eqList _==ˢ_ path) seen then load bin args seen fs else do
          readProcessAt work 60000 bin (args ++ (f ∷ [])) "" >>= λ where
            (procResult zero out _) → case parse out of λ where
              nothing → failIO "sandbox: invalid ancestor IR"
              (just c) → do
                validateIR log false c
                if eqList _==ˢ_ path (full (modName c)) then
                  (load bin args (path ∷ seen) fs >>= λ cs → return (c ∷ cs))
                  else failIO "sandbox: ancestor module name mismatch"
            (procResult _ out err) → failIO (stripStdlibWarnings (out ++ˢ err))

-- Every backend consumes the same scope-checked Code. Backend mode selects
-- the checking kernel after this boundary.
switchDumpWithLog : String → BackendMode → (dumpBin repo scratch : String) → List String → DumpReq → Prim.IO DumpResult
switchDumpWithLog log _ = Sandbox.sandboxDumpWithLog log

switchDump : BackendMode → (dumpBin repo scratch : String) → List String → DumpReq → Prim.IO DumpResult
switchDump = switchDumpWithLog ""

------------------------------------------------------------------------
-- §2  Prism Stream Interceptor for `AgdaCheckReq` (Code + Deps → CheckResult)
------------------------------------------------------------------------

private
  prismCheckIntercept : (log repo scratch : String) → List String → AgdaCheckReq → Prim.IO CheckResult
  prismCheckIntercept log repo scratch ancestors (checkRequest mainC depCs purpose) =
    fileExists (prismBinPath repo) >>= λ hasBin →
    if not hasBin then
      reportUnsupported "prism_check_unavailable" "Lean Prism binary is unavailable"
    else
      catchIO runIntercept λ e → return (fail e)
    where
      reportUnsupported : String → String → Prim.IO CheckResult
      reportUnsupported kind reason = case purpose of λ where
        (independenceCheck _ _ _ _) →
          appendNarrowingEvent log "independence_prism_required" (intersperse "." (full (modName mainC))) reason >>
          return (fail ("independence requires a scope-checked, kernel-audited witness. Rewrite the proof using FastFocus-supported syntax and run check_agda again:\n" ++ˢ reason))
        _ → appendNarrowingEvent log kind (intersperse "." (full (modName mainC))) reason >>
            return (fail ("Prism could not verify the projected module:\n" ++ˢ reason))

      -- Recompute the permitted assumption set from the authored task bytes.
      -- A discrepancy with the logical task is a failed witness transaction.
      witnessInput : QName → String → List Code → Code → Prim.IO SourceUnit
      witnessInput _ "" _ _ = failIO "INDEPENDENCE_SPEC_ERROR: missing authored SPECIFICATION source"
      witnessInput spec raw bases expected = Sandbox.sandboxDump (repo / "dump/dump") repo scratch ancestors
        (dumpReq raw [] bases) >>= λ where
          (dumpFailed e) → failIO e
          (dumped actual) →
            let stub = refuteStubOf (specΔ (modName actual) (Code.decls actual) []) in
            if not (eqList _==ˢ_ (full spec) (full (modName actual)) ∧ (encodeCanonical stub ==ˢ encodeCanonical expected))
            then failIO "INDEPENDENCE_SPEC_ERROR: authored SPECIFICATION and staged postulate stub disagree"
            else if encodeCanonical actual ==ˢ encodeCanonical stub
                 then prepareSource log false raw else prepareCode false stub

      checkedWitness : (Code → List RefuteProblem) → String → Prim.IO SourceUnit
      checkedWitness validate witness = Sandbox.sandboxDump (repo / "dump/dump") repo scratch ancestors
        (dumpReq witness [] depCs) >>= λ where
          (dumpFailed e) → failIO e
          (dumped actual) → case validate actual of λ where
            [] → if encodeCanonical actual ==ˢ encodeCanonical mainC
                 then prepareSource log false witness
                 else failIO "INDEPENDENCE_SPEC_ERROR: authored witness and staged proof disagree"
            ps@(_ ∷ _) → failIO ("Agda independent witness gate:\n" ++ˢ unlines (map showRefuteProblem ps))

      findMod : QName → List Code → Maybe Code
      findMod _ [] = nothing
      findMod q (c ∷ cs) = if modName c ==ᴺ q then just c else findMod q cs

      findBridgeModel : Code → List Code → Maybe Code
      findBridgeModel bridge [] = nothing
      findBridgeModel bridge (c ∷ cs) =
        if not (modName c ==ᴺ CM.countermodelMod) ∧ not (modName c ==ᴺ CM.bridgeMod)
           ∧ anyᵇ (_==ᴺ_ (modName c)) (NS.moduleImports bridge)
        then just c else findBridgeModel bridge cs

      inputs : String → List Code → CheckPurpose → List Code → Prim.IO (List String)
      inputs work inherited (independenceCheck spec flags raw witness) cs with findMod spec cs
      ... | nothing = failIO "INDEPENDENCE_SPEC_ERROR: missing specification"
      ... | just stub =
        let otherDeps = filterᵇ (λ d → not (modName d ==ᴺ spec)) cs in
        case findMod CM.bridgeMod otherDeps of λ where
          nothing → do
            s ← witnessInput spec raw otherDeps stub
            ds ← prepareAll (prepareCode false) (inherited ++ otherDeps)
            w ← checkedWitness (validIndependenceWithBases spec (map modName (inherited ++ otherDeps)) flags) witness
            paths ← writeUnits work (s ∷ ds)
            files ← writeUnits work (w ∷ [])
            case files of λ where
              (file ∷ []) → return ("--independence-spec" ∷ intersperse "." (full spec) ∷ "--main" ∷ file ∷ depFlags paths)
              _ → failIO "INDEPENDENCE_SPEC_ERROR: missing witness source"
          (just bridge) → case findMod CM.countermodelMod otherDeps of λ where
            nothing → failIO "INDEPENDENCE_SPEC_ERROR: missing Countermodel library"
            (just cmLib) → case findBridgeModel bridge otherDeps of λ where
              nothing → failIO "INDEPENDENCE_SPEC_ERROR: missing countermodel module"
              (just modelC) → case CM.validCountermodel flags modelC of λ where
                ps@(_ ∷ _) → failIO ("validCountermodel:\n" ++ˢ unlines (map showRefuteProblem ps))
                [] → case CM.firstBundleUnit modelC of λ where
                  nothing → failIO "INDEPENDENCE_SPEC_ERROR: missing CountermodelBundle export"
                  (just bName) →
                    if not ((encodeCanonical cmLib ==ˢ encodeCanonical CM.countermodelLib)
                            ∧ (encodeCanonical bridge ==ˢ encodeCanonical (CM.countermodelBridge (modName modelC) bName)))
                    then failIO "INDEPENDENCE_SPEC_ERROR: forged Countermodel or CountermodelCheck dependency"
                    else do
                      let isAux = λ d → (modName d ==ᴺ CM.countermodelMod) ∨ (modName d ==ᴺ CM.bridgeMod) ∨ (modName d ==ᴺ modName modelC)
                          taskBases = filterᵇ (λ d → not (isAux d)) otherDeps
                      s ← witnessInput spec raw taskBases stub
                      ds ← prepareAll (prepareCode false) (inherited ++ otherDeps)
                      w ← checkedWitness (CM.validCountermodelRefute spec (map modName (inherited ++ taskBases)) (modName modelC) flags) witness
                      paths ← writeUnits work (s ∷ ds)
                      files ← writeUnits work (w ∷ [])
                      case files of λ where
                        (file ∷ []) → return ("--independence-spec" ∷ intersperse "." (full spec) ∷ "--main" ∷ file ∷ depFlags paths)
                        _ → failIO "INDEPENDENCE_SPEC_ERROR: missing witness source"
      inputs work inherited _ cs = writeBundle work mainC (inherited ++ cs) >>= λ bundle →
        return ("--sexpr-bundle" ∷ bundle ∷ [])

      rejectTypeError : String → Prim.IO CheckResult
      rejectTypeError detail =
        (if hasWord "INDEPENDENCE_AXIOM_ERROR:" detail
         then appendNarrowingEvent log "independence_axiom" (intersperse "." (full (modName mainC))) detail
         else return tt) >> return (fail detail)

      runIntercept : Prim.IO CheckResult
      runIntercept = do
        validateIR log false mainC
        validateDeps log depCs
        bin ← absolutePath (prismBinPath repo)
        lib ← absolutePath (prismLibDir repo)
        withPrivateTemp scratch λ work → do
          let known = map (λ c → full (modName c)) (mainC ∷ depCs)
          inherited ← ancestorCodes log repo work ancestors known
          args ← inputs work inherited purpose depCs
          readProcessAt work 120000 bin
            ("prism-check" ∷ "--lib-dir" ∷ lib ∷ "--work-dir" ∷ (work / "lean_work")
             ∷ args) "" >>= λ where
            (procResult zero _ _) → return pass
            (procResult code out err) →
              if code ≡ᵇ exitBot then (case purpose of λ where
                ordinaryCheck → if Code.elemᵇ _==ˢ_ "--without-K" (flagsOf mainC)
                                   ∧ Code.elemᵇ _==ˢ_ "--safe" (flagsOf mainC)
                  then Sandbox.sandboxAgdaCheck repo scratch ancestors (agdaCheck mainC depCs)
                  else reportUnsupported "prism_unsupported" (out ++ˢ err)
                _ → reportUnsupported "prism_unsupported" (out ++ˢ err))
              else if (code ≡ᵇ exitSyntaxErr) then
                return (fail (stripStdlibWarnings (out ++ˢ err)))
              else if (code ≡ᵇ exitTypeErr) then
                rejectTypeError (stripStdlibWarnings (out ++ˢ err))
              else
                reportUnsupported "prism_check_unavailable" (out ++ˢ err)

switchCheckWithLog : String → BackendMode → (repo scratch : String) → List String → AgdaCheckReq → Prim.IO CheckResult
switchCheckWithLog log _ _ _ _ (checkRequest c _ (narrowedSubspec kind detail)) =
  Sandbox.recordSubspecRejection log c kind detail
switchCheckWithLog log _ repo scratch ancestors req@(checkRequest _ _ (independenceCheck _ _ _ _)) =
  prismCheckIntercept log repo scratch ancestors req
switchCheckWithLog log legacyAgda repo scratch ancestors req =
  Sandbox.sandboxAgdaCheck repo scratch ancestors req
switchCheckWithLog log leanPrism repo scratch ancestors req =
  prismCheckIntercept log repo scratch ancestors req
switchCheckWithLog log shadowAudit repo scratch ancestors req = do
  pRes ← prismCheckIntercept log repo scratch ancestors req
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

switchCheck : BackendMode → (repo scratch : String) → List String → AgdaCheckReq → Prim.IO CheckResult
switchCheck = switchCheckWithLog ""

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
        validateIR "" true mainC
        validateDeps "" depCs
        bin ← absolutePath (prismBinPath repo)
        lib ← absolutePath (prismLibDir repo)
        ir  ← absolutePath (prismIrDir repo)
        outAbs ← absolutePath outBin
        withPrivateTemp scratch λ work → do
          bundle ← writeBundle work mainC depCs
          readProcessAt work 180000 bin
            ("prism-build" ∷ "--lib-dir" ∷ lib ∷ "--ir-dir" ∷ ir
             ∷ "--work-dir" ∷ (work / "lean_work") ∷ "--out" ∷ outAbs
             ∷ "--sexpr-bundle" ∷ bundle ∷ []) "" >>= λ where
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
      _ ← prepareSource "" true mainSrc
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
          ("prism-dump" ∷ "--write-bundle" ∷ (leanWork / "bundle.sexp") ∷ dbFlags ++ depFlags depAbs ++ ("--main" ∷ mainAbs ∷ [])) "" >>= λ where
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
                         ∷ "--sexpr-bundle" ∷ (leanWork / "bundle.sexp") ∷ []) "" >>= λ where
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
switchNodeEnvironment defaultMode backend repo dumpBin scratch ancestorDirs = do
  envLog ← lookupEnv "CODETRANSPORT_NARROW_LOG"
  let log = case envLog of λ where
        (just path) → path
        nothing → defaultLog backend
      b′ = withBackendNarrowLog log (withBackendAncestors repo ancestorDirs backend)
  nodeEnvironmentForBackend (isConcurrentBackend b′) (aiService b′)
    (λ req → resolveBackendMode defaultMode >>= λ mode →
       switchDumpWithLog log mode dumpBin repo (scratch ++ˢ "/dump") ancestorDirs req)
    (λ req → resolveBackendMode defaultMode >>= λ mode →
       switchCheckWithLog log mode repo (scratch ++ˢ "/agda") ancestorDirs req)
  where
    defaultLog : Backend → String
    defaultLog (CodexCLIBackend cfg) = narrowLog cfg
    defaultLog _ = scratch ++ˢ "/narrowing-events.jsonl"
