{-# OPTIONS --guardedness #-}
module Meta.Sandbox where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
import Data.Nat.Show as Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; intersperse) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
open import OwnershipIO.FFI using (mkdirP; absolutePath; failIO; readProcessAt; ProcResult; procResult; stripStdlibWarnings)
open import OwnershipIO.MetaFFI
open import Code using (Code; full; modName; eqList; _==ˢ_)
open import Code.SExpr using (SExpr; list; sym)
open import Code.Encode using (encodeCode)
open import Code.Parse using (decodeQ; parse)
open import Code.Render using (render)
open import Code.AgdaTool using (parentPath)
open import Code.Protocol using (AgdaCheckReq; agdaCheck; DumpReq; dumpReq; DumpResult; dumped; dumpFailed)
open import Code.Transport using (CheckResult; pass; fail)
open import Meta.Boundary public

private
  -- Walk the structural encoding so local modules, where blocks and extended
  -- lambdas receive the same import check as the top level.
  mutual
    importsIn : SExpr → List ModulePath
    importsIn (list (sym "import" ∷ q ∷ rest)) with decodeQ q
    ... | just name = full name ∷ importsInList rest
    ... | nothing = [] ∷ importsInList rest
    importsIn (list xs) = importsInList xs
    importsIn _ = []

    importsInList : List SExpr → List ModulePath
    importsInList [] = []
    importsInList (x ∷ xs) = importsIn x ++ importsInList xs

instance
  codeView : ModuleView Code
  codeView = moduleView (λ c → full (modName c)) (λ c → importsIn (encodeCode c))

private
  infixl 6 _/_
  _/_ : String → String → String
  a / b = a ++ˢ "/" ++ˢ b

  inReservedTree : String → String → List String → IO Bool
  inReservedTree repo src [] = return false
  inReservedTree repo src (n ∷ ns) = pathWithin (repo / n) src >>= λ where
    true → return true
    false → inReservedTree repo src ns

  checkAncestor : String → String → IO ⊤
  checkAncestor repo src = pathWithin src repo >>= λ where
    true → failIO "sandbox: ancestor includes the repository root"
    false → pathWithin (repo / "Verification/Generated") src >>= λ where
      true → return tt
      false → inReservedTree repo src reservedPrefixes >>= λ where
        true → failIO "sandbox: ancestor is a harness source directory"
        false → return tt

  copyAncestors : String → String → ℕ → List String → IO (List String)
  copyAncestors repo tmp index [] = return []
  copyAncestors repo tmp index (src ∷ rest) = do
    checkAncestor repo src
    let dst = tmp / ("ancestor-" ++ˢ Nat.show index)
    copySourceTree src dst ("Context" ∷ reservedPrefixes)
    dirs ← copyAncestors repo tmp (suc index) rest
    return (dst ∷ dirs)

sealAncestorsTo : (repo tmp : String) → List String → IO (List String)
sealAncestorsTo repo tmp ancestors = copyAncestors repo tmp 0 ancestors

withWhitelistView : ∀ {a} {A : Set a} → (repo scratch : String) → List String →
                    (List String → IO A) → IO A
withWhitelistView repo scratch ancestors use = withPrivateTemp scratch λ tmp → do
  -- Agda puts interfaces under the nearest project's _build/. Populate the
  -- sealed Context view and precompiled _build cache from a digest-keyed cache.
  populateContextCache repo tmp
  sealed ← copyAncestors repo tmp 0 ancestors
  use ((tmp / "context") ∷ "/usr/share/agda-stdlib" ∷ sealed)

private
  Source = ModulePath × String

  reject : ∀ {A : Set} → ModulePath → IO A
  reject path = failIO ("sandbox: forbidden module name or import in " ++ˢ intersperse "." path)

  -- Inspect all input before writing any filename or invoking either tool.
  -- Parsing the rendered source also checks raw pragma and presentation text
  -- in constructed ASTs, using the exact bytes that the tool will receive.
  prepareSource : String → IO Source
  prepareSource src = inspectSource src >>= λ where
    (just (path ∷ imports)) → if checkModulePaths false path imports
      then return (path , src) else reject path
    _ → failIO "sandbox: expected a named Agda module"

  prepareCode : Code → IO Source
  prepareCode c = if checkObjectModuleSafe false c then
    (prepareSource (render c) >>= λ { unit@(path , _) →
      if eqList _==ˢ_ path (full (modName c)) then return unit else reject path })
    else reject (full (modName c))

  prepareAll : ∀ {A : Set} → (A → IO Source) → List A → IO (List Source)
  prepareAll f [] = return []
  prepareAll f (x ∷ xs) = do
    unit ← f x
    rest ← prepareAll f xs
    return (unit ∷ rest)

  fileName : ModulePath → String
  fileName path = intersperse "/" path ++ˢ ".agda"

  writeSources : String → List Source → IO ⊤
  writeSources dir [] = return tt
  writeSources dir ((path , src) ∷ rest) = do
    mkdirP (dir / parentPath path)
    writeUTF8 (dir / fileName path) src
    writeSources dir rest

  runTool : (repo scratch : String) → List String → String → List String →
            Source → List Source → IO ProcResult
  runTool repo scratch ancestors bin flags main@(path , _) deps =
    withWhitelistView repo scratch ancestors λ includes → withPrivateTemp scratch λ work → do
      -- dump disables default libraries, but Agda can also discover a project
      -- file above cwd. Give this workspace its own empty library boundary.
      writeUTF8 (work / "object.agda-lib") "name: object-view\ninclude: .\n"
      let config = work / ".agda"
      mkdirP config
      writeSources work (deps ++ (main ∷ []))
      let args = concatMap (λ i → "-i" ∷ i ∷ []) (work ∷ includes)
      -- An empty Agda configuration also isolates trusted executables used
      -- by reflection, including when type-checking transitive dependencies.
      readProcessAt work 120000 "/usr/bin/env"
        (("AGDA_DIR=" ++ˢ config) ∷ bin ∷ flags ++ args ++ (("./" ++ˢ fileName path) ∷ [])) ""

sandboxAgdaCheck : (repo scratch : String) → List String → AgdaCheckReq → IO CheckResult
sandboxAgdaCheck repo scratch ancestors (agdaCheck c deps) = catchIO check λ e → return (fail e)
  where
  check : IO CheckResult
  check = do
    main ← prepareCode c
    sources ← prepareAll prepareCode deps
    runTool repo scratch ancestors "agda" ("--no-libraries" ∷ []) main sources >>= λ where
      (procResult zero _ _) → return pass
      (procResult (suc _) out err) → return (fail (stripStdlibWarnings (out ++ˢ err)))

sandboxDump : (dumpBin repo scratch : String) → List String → DumpReq → IO DumpResult
sandboxDump dumpBin repo scratch ancestors (dumpReq src raw codes) = catchIO dump λ e → return (dumpFailed e)
  where
  dump : IO DumpResult
  dump = do
    main ← prepareSource src
    cs ← prepareAll prepareCode codes
    ds ← prepareAll (λ pair → prepareSource (proj₂ pair)) raw
    bin ← absolutePath dumpBin
    runTool repo scratch ancestors bin [] main (cs ++ ds) >>= λ where
      (procResult (suc _) out err) → return (dumpFailed (out ++ˢ err))
      (procResult zero out _) → caseOutput (parse out) (proj₁ main)
    where
    caseOutput : Maybe Code → ModulePath → IO DumpResult
    caseOutput nothing path = return (dumpFailed "sandbox: unsupported dump output")
    caseOutput (just c) path = if eqList _==ˢ_ (full (modName c)) path
      then (if checkObjectModuleSafe false c then return (dumped c) else reject path)
      else reject path
