{-# OPTIONS --guardedness #-}
module Code.SessionWorkspace where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; length)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; unlines; words; wordsBy; intersperse; toList; fromList) renaming (_++_ to _++ˢ_)
import Data.Char as Char
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import OwnershipIO using (dropModel; onCall)
open import OwnershipIO.MetaFFI using (replaceDuring)
open import OwnershipIO.FFI
open import Code
import Store.CAS as CAS
import Meta.Sandbox as Sandbox
open import Store.Verify using (verifyCommitDAG)
import Code.NodeTransport as NT
open import Code.TreeSnapshot using (freezeHome)
open import Code.Codecs using (HomeValue; loadHome; storeGeneration; homeNoChan)
open import Code.SExpr using (SExpr; list; str; parseSExpr; showSExpr)
open import Code.SessionProtocol using (strings)
open import Code.Render using (render)
open import Code.Store using (putCode)
open import Code.Driver using (dumpTool; writeSource)
open import Code.Protocol using (dumpReq; dumpFailed; dumped)
open import Code.AgdaTool using (modulePath; parentPath)
open import Code.Transport using (nullᵇ)

private
  infixl 1 _>>=_ _>>_
  _>>=_ = IO._>>=_
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → IO.IO A → IO.IO B → IO.IO B
  m >> n = m >>= λ _ → n

-- A tree name is a single path component, not an arbitrary filesystem path.
safeTree : String → Bool
safeTree s = not (s ==ˢ "") ∧ allᵇ (λ c → Char.isAlpha c ∨ Char.isDigit c ∨ (Char.toℕ c Data.Nat.≡ᵇ 95) ∨ (Char.toℕ c Data.Nat.≡ᵇ 45)) (toList s)

readIfExists : String → IO.IO String
readIfExists path = fileExists path >>= λ b → if b then F.readFile path else IO.return ""

atomicText : String → String → IO.IO ⊤
atomicText path text = F.writeFile (path ++ˢ ".new") text >> atomicRename (path ++ˢ ".new") path

entries : String → IO.IO (List String)
entries dir = dirExists dir >>= λ b → if b then listDirectory dir else IO.return []

successfulTrees : String → IO.IO (List String)
successfulTrees ws = entries (ws ++ˢ "/trees") >>= collect
  where
    collect : List String → IO.IO (List String)
    collect [] = IO.return []
    collect (n ∷ ns) = readIfExists (ws ++ˢ "/trees/" ++ˢ n ++ˢ "/verdict") >>= λ v →
      collect ns >>= λ rest → IO.return (if v ==ˢ "ok" then n ∷ rest else rest)

includeDirs : String → String → IO.IO (List String)
includeDirs repo ws = successfulTrees ws >>= λ trees →
  IO.return (map (λ n → ws ++ˢ "/generated/" ++ˢ n) trees
    ++ (repo ∷ "/usr/share/agda-stdlib" ∷ []))

includeArgs : List String → List String
includeArgs = concatMap (λ i → "-i" ∷ i ∷ [])

-- Agda rejects duplicate module paths rather than shadowing them. A source
-- update (or a new Main) therefore gets a read-only include view that omits
-- exactly its old .agda/.agdai. All unrelated modules retain their own paths.
maskSource : String → String → List String → IO.IO ⊤
maskSource src dst [] = IO.return tt
maskSource src dst (part ∷ parts) = mkdirP dst >> entries src >>= copy
  where
    copy : List String → IO.IO ⊤
    copy [] = IO.return tt
    copy (n ∷ ns) = choose parts n >> copy ns
      where
        choose : List String → String → IO.IO ⊤
        choose [] n = if (n ==ˢ part) ∨ (n ==ˢ (part ++ˢ "i")) then IO.return tt
          else linkPath (src ++ˢ "/" ++ˢ n) (dst ++ˢ "/" ++ˢ n)
        choose rest n = if n ==ˢ part then maskSource (src ++ˢ "/" ++ˢ n) (dst ++ˢ "/" ++ˢ n) parts
          else linkPath (src ++ˢ "/" ++ˢ n) (dst ++ˢ "/" ++ˢ n)

withoutSource : String → String → List String → IO.IO (List String)
withoutSource scratch file [] = IO.return []
withoutSource scratch file (inc ∷ incs) = fileExists (inc ++ˢ "/" ++ˢ file) >>= λ exists →
  (if exists then (freshDirectory scratch >>= λ dir → maskSource inc dir (wordsBy ('/' Char.≟_) file) >> IO.return dir)
   else IO.return inc) >>= λ selected → withoutSource scratch file incs >>= λ rest → IO.return (selected ∷ rest)

recordFiles : String → List String → IO.IO ⊤
recordFiles path names = atomicText path (showSExpr (list (map str names)))

-- Publish current, ancestry, verdict, exports and the CAS ref as one writer.
-- The generation and CAS objects are immutable and may be staged in advance.
publishGeneration : ∀ {A : Set} → String → String → List String → String → HomeValue →
                    (String → IO.IO A) → IO.IO A
publishGeneration {A} ws path bases verdict result finish = withTempDirectory (ws ++ˢ "/tmp/publish") λ stage → do
  generation ← storeGeneration path result
  F.writeFile (stage ++ˢ "/current") generation
  recordFiles (stage ++ˢ "/bases.sexp") bases
  F.writeFile (stage ++ˢ "/verdict") verdict
  let install = λ file → replaceDuring {A = A} (stage ++ˢ "/" ++ˢ file) (path ++ˢ "/" ++ˢ file)
  install "current" (install "bases.sexp" (install "verdict" (finish stage)))

readNames : String → IO.IO (Maybe (List String))
readNames path = readIfExists path >>= λ txt → IO.return (decode (parseSExpr txt))
  where
    decode : Maybe SExpr → Maybe (List String)
    decode (just (list xs)) = strings xs
    decode _ = nothing

-- The queue follows each saved tree's direct bases. A visited set handles
-- diamonds; fuel from the filesystem bounds missing/cyclic metadata safely.
data BaseResult : Set where
  basesLoaded : List Code → BaseResult
  basesFailed : String → BaseResult

consistentCodes : List Code → Bool
consistentCodes [] = true
consistentCodes (c ∷ cs) = allᵇ (λ d → if modName c ==ᴺ modName d then eqCode c d else true) cs ∧ consistentCodes cs

record SealedTree : Set where
  constructor sealedTree
  field
    treeEpoch tip : String
    snapshot : NT.Frozen
open SealedTree public

uniqueCodes : List Code → List Code
uniqueCodes = nubᵇ (λ a b → modName a ==ᴺ modName b)

treeRef : String → String
treeRef name = "trees/" ++ˢ name

partialTreeRef : String → String
partialTreeRef name = "partial/" ++ˢ name

record PartialSealed : Set where
  constructor partialSealed
  field
    sealed : SealedTree
    ancestorCodes : List Code
    surfaces : List (Code × String)

-- A partial commit supplies child implementations. Its shell is only the
-- ownership container for those children, including in a descendant's DAG.
preservedCodes : NT.Frozen → List Code
preservedCodes snap = concatMap (λ { (_ , kid) → NT.exported kid }) (NT.children snap)

-- Group receipts by immutable partial tip (or "empty" for a childless
-- obstruction). Moving a named ref loses neither history nor parent kind.
obstructionDir : String → String → String
obstructionDir ws group = ws ++ˢ "/obstructions/" ++ˢ group

previousObstruction : String → String → IO.IO Bool
previousObstruction ws stamp = sha256 stamp >>= λ digest → entries (ws ++ˢ "/obstructions") >>= find digest
  where
    find : String → List String → IO.IO Bool
    find digest [] = IO.return false
    find digest (g ∷ gs) = readIfExists (obstructionDir ws g ++ˢ "/" ++ˢ digest ++ˢ ".sexp") >>= λ saved →
      if saved ==ˢ stamp then IO.return true else find digest gs

-- Workspaces produced before V3 have only current/verdict/bases.sexp. Import
-- those successful generations once. An existing broken ref is always an error.
resolveTips : String → ℕ → List String → IO.IO (Maybe (List CAS.Hash))
resolveTree : String → ℕ → String → IO.IO (Maybe CAS.Hash)
resolveTips ws fuel [] = IO.return (just [])
resolveTips ws fuel (n ∷ ns) = resolveTree ws fuel n CAS.>>=? λ key →
  resolveTips ws fuel ns CAS.>>=? λ rest → IO.return (just (key ∷ rest))
resolveTree ws zero n = IO.return nothing
resolveTree ws (suc fuel) n = if safeTree n then
  (readIfExists (path ++ˢ "/verdict") >>= λ v → if v ==ˢ "ok" then
    (fileExists (dir ++ˢ "/refs/" ++ˢ treeRef n) >>= λ present → if present then
      (CAS.readRef dir (treeRef n) CAS.>>=? λ key → CAS.getCommit dir key CAS.>>=? λ c →
       IO.return (Data.Maybe.when (CAS.epoch c ==ˢ n) key))
      else migrate)
    else IO.return nothing)
  else IO.return nothing
  where
    dir = ws ++ˢ "/store"
    path = ws ++ˢ "/trees/" ++ˢ n
    migrate : IO.IO (Maybe CAS.Hash)
    migrate = loadHome path CAS.>>=? λ h → readNames (path ++ˢ "/bases.sexp") CAS.>>=? λ bs →
      resolveTips ws fuel bs CAS.>>=? λ ps → do
        key ← CAS.storeTreeCommit dir ps n "import legacy session tree" h
        valid ← verifyCommitDAG dir key
        if valid then (CAS.writeRef dir (treeRef n) key >> IO.return (just key)) else IO.return nothing

private
  readMany : ∀ {A : Set} → CAS.Reader (List A) → List CAS.Hash → IO.IO (Maybe (List A))
  readMany read [] = IO.return (just [])
  readMany read (k ∷ ks) = read k CAS.>>=? λ xs → readMany read ks CAS.>>=? λ ys → IO.return (just (xs ++ ys))

  ParentTip = CAS.Hash → CAS.CommitObj → IO.IO (Maybe CAS.Hash)

  -- Same-epoch parents record history. Only a vertical edge contributes
  -- modules, and a partial transport always follows its pinned provenance.
  ancestry : ParentTip → (CAS.CommitObj → IO.IO (Maybe HomeValue)) → String → CAS.Reader (List SealedTree) → CAS.Reader (List SealedTree)
  ancestry select readHome dir read key = CAS.getCommit dir key CAS.>>=? λ c →
    readHome c CAS.>>=? λ { (sh , h) →
      readMany (parent (CAS.epoch c)) (CAS.parents c) CAS.>>=? λ ancestors →
      IO.return (just (sealedTree (CAS.epoch c) key (freezeHome sh (dropModel (homeNoChan sh) h))
        ∷ nubᵇ (λ a b → tip a ==ˢ tip b) ancestors)) }
    where
      parent : String → CAS.Reader (List SealedTree)
      parent e k = CAS.getCommit dir k CAS.>>=? λ c →
        if CAS.epoch c ==ˢ e then IO.return (just []) else select k c CAS.>>=? read

  verifiedReader : ParentTip → String → IO.IO (CAS.Reader (List SealedTree))
  verifiedReader select dir = do
    readHome ← CAS.newCommitHomeReader dir
    read ← CAS.newDAGReader dir CAS.commitK (ancestry select readHome dir)
    IO.return λ key → verifyCommitDAG dir key >>= λ valid → if valid then read key else IO.return nothing

  closureEntries : String → List SealedTree → IO.IO (List SealedTree × List Code)
  closureEntries ws [] = IO.return ([] , [])
  closureEntries ws (t ∷ ts) = entries (obstructionDir ws (tip t)) >>= λ receipts →
    closureEntries ws ts >>= λ { (complete , cs) → IO.return (if nullᵇ receipts
      then (t ∷ complete , NT.exported (snapshot t) ++ cs)
      else (complete , preservedCodes (snapshot t) ++ cs)) }

loadPartialBases : String → IO.IO (List PartialSealed)
loadPartialBases ws = verifiedReader (λ k _ → IO.return (just k)) dir >>= λ read → entries (dir ++ˢ "/refs/partial") >>= collect read
  where
    dir = ws ++ˢ "/store"
    safe : Code → Bool
    safe c = nullᵇ (closedImplOK [] c) ∧ Sandbox.checkObjectModuleSafe false c

    load : CAS.Reader (List SealedTree) → String → IO.IO (Maybe PartialSealed)
    load read name = CAS.readRef dir (partialTreeRef name) CAS.>>=? λ key → read key CAS.>>=? λ where
      [] → IO.return nothing
      (t ∷ parents) → CAS.commitSurfaces dir key CAS.>>=? λ views →
        closureEntries ws parents >>= λ { (_ , cs) →
          let modules = NT.exported (snapshot t) ++ cs
          in IO.return (Data.Maybe.when ((treeEpoch t ==ˢ name) ∧ not (nullᵇ (NT.children (snapshot t)))
                ∧ allᵇ safe modules ∧ consistentCodes modules) (partialSealed t (uniqueCodes cs) views)) }

    collect : CAS.Reader (List SealedTree) → List String → IO.IO (List PartialSealed)
    collect read [] = IO.return []
    collect read (n ∷ ns) = (if safeTree n then load read n else IO.return nothing) >>= λ entry →
      collect read ns >>= λ rest → IO.return (maybe′ (_∷ rest) rest entry)

record BaseClosure : Set where
  constructor closure
  field
    directTips : List CAS.Hash
    sealedBases : List SealedTree
    baseCodes : List Code
open BaseClosure public

-- Resolve vertical edges of complete workspace trees to live tips. A partial
-- parent pins only its preserved children, even if its epoch later succeeds.
loadCurrentClosure : String → List String → IO.IO (Maybe (BaseClosure × Bool))
loadCurrentClosure ws names = entries (ws ++ˢ "/trees") >>= λ trees →
  resolveTips ws (suc (length trees)) names CAS.>>=? λ ps → newIORef false >>= λ moved →
  verifiedReader (liveParent moved) dir >>= λ read → readMany read ps CAS.>>=? λ all →
  closureEntries ws (nubᵇ (λ a b → tip a ==ˢ tip b) all) >>= λ { (bs , cs) →
    readIORef moved >>= λ changed →
    IO.return (Data.Maybe.when (consistentCodes cs) (closure ps bs (uniqueCodes cs) , changed)) }
  where
    dir = ws ++ˢ "/store"
    liveParent : IORef Bool → ParentTip
    liveParent moved k c = if safeTree name then
      (readIfExists (ws ++ˢ "/trees/" ++ˢ name ++ˢ "/verdict") >>= λ verdict →
       if verdict ==ˢ "ok" then (entries (obstructionDir ws k) >>= λ receipts →
         if nullᵇ receipts then current else pinned) else pinned)
      else pinned
      where
        name = CAS.epoch c
        pinned = IO.return (just k)
        current = fileExists (dir ++ˢ "/refs/" ++ˢ treeRef name) >>= λ present →
          if present then (CAS.readRef dir (treeRef name) CAS.>>=? λ tip′ →
            if tip′ ==ˢ k then pinned else
              (CAS.getCommit dir tip′ CAS.>>=? λ latest → verifyCommitDAG dir tip′ >>= λ valid →
               if valid ∧ (CAS.epoch latest ==ˢ name)
               then writeIORef moved true >> IO.return (just tip′) else IO.return nothing))
          else pinned

loadClosure : String → List String → IO.IO (Maybe BaseClosure)
loadClosure ws names = loadCurrentClosure ws names >>= λ result → IO.return (Data.Maybe.map proj₁ result)

loadBases : String → List String → IO.IO BaseResult
loadBases ws bases = loadClosure ws bases >>= λ loaded →
  IO.return (maybe′ (λ b → basesLoaded (baseCodes b)) (basesFailed "baseTrees: missing, conflicting or invalid ancestor") loaded)

firstWord : List String → String
firstWord [] = ""
firstWord (x ∷ _) = x

shaFile : String → IO.IO String
shaFile path = readProcessAt "" 30000 "sha256sum" (path ∷ []) "" >>= λ where
  (procResult zero out _) → IO.return (firstWord (words out))
  (procResult _ out err) → failIO ("sha256sum failed: " ++ˢ out ++ˢ err)

viewText : List (Code × String) → Code → String
viewText views c = maybe′ (λ text → text) (render c) (authoredSurface views c)

publishedViews : String → String → IO.IO (List (Code × String))
publishedViews ws tree = let store = ws ++ˢ "/store" in
  CAS.readRef store (treeRef tree) >>= λ where
    nothing → IO.return []
    (just key) → CAS.commitSurfaces store key >>= λ where
      nothing → failIO "invalid pinned source presentation"
      (just views) → IO.return views

writeViews : String → List (Code × String) → List Code → IO.IO ⊤
writeViews dir views [] = IO.return tt
writeViews dir views (c ∷ cs) = do
  mkdirP (dir ++ˢ "/" ++ˢ parentPath (full (modName c)))
  F.writeFile (dir ++ˢ "/" ++ˢ modulePath c) (viewText views c)
  writeViews dir views cs

exportCodes : String → String → List (Code × String) → List Code → IO.IO String
exportCodes ws tree views [] = IO.return ""
exportCodes ws tree views (c ∷ cs) = putCode (ws ++ˢ "/store/objects") c >>= λ canonical →
  sha256 (viewText views c) >>= λ source → exportCodes ws tree views cs >>= λ rest →
  IO.return ("module\t" ++ˢ tree ++ˢ "/" ++ˢ intersperse "." (full (modName c)) ++ˢ "\t" ++ˢ canonical ++ˢ "\t" ++ˢ source ++ˢ "\n" ++ˢ rest)

-- A sealed tree pins both its semantic home and its own source spellings.
-- Legacy export folders can only attest to the bytes they contain.
private
  SealedExports = List (Code × String)

  lookupExport : String → SealedExports → Maybe (Code × String)
  lookupExport rel [] = nothing
  lookupExport rel ((c , src) ∷ cs) = if rel ==ˢ modulePath c then just (c , src) else lookupExport rel cs

  pinnedExports : String → String → IO.IO (Maybe SealedExports)
  pinnedExports ws n = fileExists (dir ++ˢ "/refs/" ++ˢ treeRef n) >>= λ present →
    if present then (load >>= λ where
      nothing → failIO ("invalid sealed exports: " ++ˢ n)
      (just cs) → IO.return (just cs))
    else IO.return nothing
    where
      dir = ws ++ˢ "/store"
      load : IO.IO (Maybe SealedExports)
      load = CAS.readRef dir (treeRef n) CAS.>>=? λ key → CAS.getCommit dir key CAS.>>=? λ commit →
        if CAS.epoch commit ==ˢ n then (CAS.newCommitHomeReader dir >>= λ read → read commit CAS.>>=? λ where
          (sh , h) → CAS.commitSurfaces dir key CAS.>>=? λ views →
            let cs = NT.exported (freezeHome sh (dropModel (homeNoChan sh) h))
            in IO.return (Data.Maybe.when (consistentCodes cs) (map (λ c → c , viewText views c) (uniqueCodes cs))))
        else IO.return nothing

-- Compare an overlapping implementation with that tree's own verified IR
-- and source, including the canonical spelling of a synthesized export.
exportsAgree : String → String → List Code → IO.IO Bool
exportsAgree ws tree cs = successfulTrees ws >>= trees
  where
    overlaps : String → List Code → IO.IO (List Code)
    overlaps dir [] = IO.return []
    overlaps dir (c ∷ rest) = fileExists (dir ++ˢ "/" ++ˢ modulePath c) >>= λ present →
      overlaps dir rest >>= λ more → IO.return (if present then c ∷ more else more)

    matches : Maybe SealedExports → Code → String → Bool
    matches nothing c text = text ==ˢ render c
    matches (just xs) c text with lookupExport (modulePath c) xs
    ... | nothing = false
    ... | just (old , expected) = (text ==ˢ expected) ∧ eqCode (surfaceCode c) (surfaceCode old)

    files : String → Maybe SealedExports → List Code → IO.IO Bool
    files dir pinned [] = IO.return true
    files dir pinned (c ∷ rest) = F.readFile (dir ++ˢ "/" ++ˢ modulePath c) >>= λ src →
      if matches pinned c src then files dir pinned rest else IO.return false

    trees : List String → IO.IO Bool
    trees [] = IO.return true
    trees (n ∷ ns) = if n ==ˢ tree then trees ns else
      (let dir = ws ++ˢ "/generated/" ++ˢ n in overlaps dir cs >>= λ where
        [] → trees ns
        shared → pinnedExports ws n >>= λ pinned → files dir pinned shared >>= λ ok →
          if ok then trees ns else IO.return false)

moduleSummary : Code → String
moduleSummary c = render (record c { decls = filterᵇ signature (decls c) }) ++ˢ childNote
  where
    signature : Decl → Bool
    signature (fun _ _ _) = false
    signature _ = true
    kids : List Import
    kids = filterᵇ (λ i → not (nullᵇ (assumes i))) (imports c)
    childNote : String
    childNote with kids
    ... | [] = ""
    ... | _ ∷ _ = "\n-- child subpackages of " ++ˢ intersperse "." (full (modName c))
      ++ˢ " (must appear in LiftSpec child-map when lifting " ++ˢ intersperse "." (full (modName c)) ++ˢ "): "
      ++ˢ intersperse ", " (map (λ i → intersperse "." (full (imod i))) kids) ++ˢ "\n"

-- A checked source is retained exactly, while canonical object hashes are
-- derived from the AST. IO imports are allowed for executable entry modules.
data SourceResult : Set where
  sourceOK : Code → SourceResult
  sourceFailed : String → SourceResult

checkSourceWith : Bool → String → String → List String → String → IO.IO SourceResult
checkSourceWith allowIO repo scratch incs src = withTempDirectory scratch λ dir → writeSource dir src >>= prepare dir
  where
    keepProblem : Code → ImplProblem → Bool
    keepProblem c flagEnvelopeViolation = not (allowIO ∧ flagsOK ("--guardedness" ∷ []) (flagsOf c))
    keepProblem _ _ = true
    checked : Code.Protocol.DumpResult → IO.IO SourceResult
    checked (dumpFailed e) = IO.return (sourceFailed e)
    checked (dumped c) = IO.return (if nullᵇ (filterᵇ (keepProblem c) (closedImplOK [] c)) then sourceOK c else
      sourceFailed "closedImplOK []: source contains an axiom, hole, unsafe pragma or unclosed definition")
    prepare : String → Maybe String → IO.IO SourceResult
    prepare dir nothing = IO.return (sourceFailed "source: missing or unsafe module name")
    prepare dir (just file) = withoutSource (dir ++ˢ "/includes") file incs >>= λ masked →
      readProcessAt dir 120000 "agda" (includeArgs ("." ∷ masked) ++ (file ∷ [])) "" >>= λ where
        (procResult zero _ _) → onCall (dumpTool (repo ++ˢ "/dump/dump") (dir ++ˢ "/dump") masked) (dumpReq src [] []) >>= checked
        (procResult _ out err) → IO.return (sourceFailed (stripStdlibWarnings (out ++ˢ err)))

checkSource : String → String → List String → String → IO.IO SourceResult
checkSource = checkSourceWith false

-- IO programs need guardedness to import the ownership interpreter. All other
-- closedImplOK [] problems, including termination/FFI bypasses, remain fatal.
checkIOSource : String → String → List String → String → IO.IO SourceResult
checkIOSource = checkSourceWith true

-- Walk only directories owned by the session; no shell interpolation occurs.
{-# NON_TERMINATING #-}
filesBelow : String → IO.IO (List String)
filesBelow dir = entries dir >>= collect
  where
    collect : List String → IO.IO (List String)
    collect [] = IO.return []
    collect (n ∷ ns) = dirExists (dir ++ˢ "/" ++ˢ n) >>= λ isDir →
      (if isDir then filesBelow (dir ++ˢ "/" ++ˢ n) else IO.return ((dir ++ˢ "/" ++ˢ n) ∷ [])) >>= λ found →
      collect ns >>= λ rest → IO.return (found ++ rest)

endsWith : String → String → Bool
endsWith suffix text = charPrefix (Data.List.reverse (toList suffix)) (Data.List.reverse (toList text))
  where
    charPrefix : List Char.Char → List Char.Char → Bool
    charPrefix [] _ = true
    charPrefix (_ ∷ _) [] = false
    charPrefix (x ∷ xs) (y ∷ ys) = (Char.toℕ x Data.Nat.≡ᵇ Char.toℕ y) ∧ charPrefix xs ys

sourcesIn : String → IO.IO (List String)
sourcesIn dir = filesBelow dir >>= λ fs → IO.return (filterᵇ (endsWith ".agda") fs)

-- Agda needs one file per module path. A different spelling is accepted only
-- when both sealed trees attest to their bytes and to the same frontend IR.
withOpenIncludes : ∀ {A : Set} → String → String → (List String → IO.IO A) → IO.IO A
withOpenIncludes repo ws use = withTempDirectory (ws ++ˢ "/tmp/export-view") λ dir → do
  cache ← newIORef []
  successfulTrees ws >>= collect cache dir []
  use (dir ∷ repo ∷ "/usr/share/agda-stdlib" ∷ [])
  where
    lookup : ∀ {A : Set} → String → List (String × A) → Maybe A
    lookup name [] = nothing
    lookup name ((n , x) ∷ xs) = if name ==ˢ n then just x else lookup name xs

    Cache = IORef (List (String × Maybe SealedExports))
    Owners = List (String × String)

    pinned : Cache → String → IO.IO (Maybe SealedExports)
    pinned cache n = readIORef cache >>= λ entries → maybe′ IO.return
      (pinnedExports ws n >>= λ xs → writeIORef cache ((n , xs) ∷ entries) >> IO.return xs) (lookup n entries)

    verified : Cache → String → String → String → IO.IO (Maybe Code)
    verified cache n rel text = pinned cache n CAS.>>=? λ exports → IO.return
      (lookupExport rel exports Data.Maybe.>>= λ { (c , src) → Data.Maybe.when (text ==ˢ src) (surfaceCode c) })

    sameModule : Cache → String → String → String → String → String → IO.IO Bool
    sameModule cache rel n old text other = do
      match ← verified cache n rel text CAS.>>=? λ c → verified cache old rel other CAS.>>=? λ d → IO.return (just (eqCode c d))
      IO.return (maybe′ (λ b → b) false match)

    copyFiles : Cache → String → String → String → Owners → List String → IO.IO Owners
    copyFiles cache n src dst seen [] = IO.return seen
    copyFiles cache n src dst seen (file ∷ fs) = do
      let relative = fromList (Data.List.drop (suc (length (toList src))) (toList file))
          to = dst ++ˢ "/" ++ˢ relative
          parent = parentPath (wordsBy ('/' Char.≟_) relative)
      text ← F.readFile file
      owners ← caseOwner relative to parent text (lookup relative seen)
      copyFiles cache n src dst owners fs
      where
        caseOwner : String → String → String → String → Maybe String → IO.IO Owners
        caseOwner rel to parent text nothing = mkdirP (dst ++ˢ "/" ++ˢ parent) >> F.writeFile to text >> IO.return ((rel , n) ∷ seen)
        caseOwner rel to parent text (just old) = F.readFile to >>= λ other →
          if text ==ˢ other then IO.return seen else (sameModule cache rel n old text other >>= λ ok →
            if ok then IO.return seen else failIO ("ambiguous exported module: " ++ˢ rel))

    collect : Cache → String → Owners → List String → IO.IO ⊤
    collect cache dst seen [] = IO.return tt
    collect cache dst seen (n ∷ ns) = let src = ws ++ˢ "/generated/" ++ˢ n in
      sourcesIn src >>= copyFiles cache n src dst seen >>= λ next → collect cache dst next ns

treeManifestFiles : String → IO.IO (List String)
treeManifestFiles ws = entries (ws ++ˢ "/trees") >>= collect
  where
    collect : List String → IO.IO (List String)
    collect [] = IO.return []
    collect (n ∷ ns) = let file = ws ++ˢ "/trees/" ++ˢ n ++ˢ "/modules.tsv" in
      fileExists file >>= λ exists → collect ns >>= λ rest →
      IO.return (if exists then file ∷ rest else rest)

hashSources : List String → IO.IO String
hashSources [] = IO.return ""
hashSources (f ∷ fs) = shaFile f >>= λ h → hashSources fs >>= λ rest → IO.return (f ++ˢ "\t" ++ˢ h ++ˢ "\n" ++ˢ rest)

fingerprint : String → IO.IO String
fingerprint ws = sourcesIn (ws ++ˢ "/generated") >>= λ generated → treeManifestFiles ws >>= λ manifests →
  hashSources (generated ++ manifests) >>= sha256

threadManifest : String → IO.IO String
threadManifest ws = filesBelow (ws ++ˢ "/threads") >>= λ fs → collect (filterᵇ (λ f → endsWith ".id" f ∨ endsWith ".thread" f) fs)
  where
    collect : List String → IO.IO String
    collect [] = IO.return ""
    collect (p ∷ ps) = F.readFile p >>= λ tid → collect ps >>= λ rest →
      IO.return ("thread_id\t" ++ˢ p ++ˢ "\t" ++ˢ tid ++ˢ "\n" ++ˢ rest)

treeManifests : String → List String → IO.IO String
treeManifests ws [] = IO.return ""
treeManifests ws (n ∷ ns) = readIfExists (ws ++ˢ "/trees/" ++ˢ n ++ˢ "/modules.tsv") >>= λ here →
  treeManifests ws ns >>= λ rest → IO.return (here ++ˢ rest)
