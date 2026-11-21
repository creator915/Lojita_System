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

  -- Follow pinned commits. A previous revision of the same named tree is
  -- historical provenance, not an additional module search path.
  ancestry : (CAS.CommitObj → IO.IO (Maybe HomeValue)) → String → CAS.Reader (List SealedTree) → CAS.Reader (List SealedTree)
  ancestry readHome dir read key = CAS.getCommit dir key CAS.>>=? λ c →
    readHome c CAS.>>=? λ { (sh , h) →
      readMany (parent (CAS.epoch c)) (CAS.parents c) CAS.>>=? λ ancestors →
      IO.return (just (sealedTree (CAS.epoch c) key (freezeHome sh (dropModel (homeNoChan sh) h))
        ∷ nubᵇ (λ a b → tip a ==ˢ tip b) ancestors)) }
    where
      parent : String → CAS.Reader (List SealedTree)
      parent e k = CAS.getCommit dir k CAS.>>=? λ c →
        if CAS.epoch c ==ˢ e then IO.return (just []) else read k

record BaseClosure : Set where
  constructor closure
  field
    directTips : List CAS.Hash
    sealedBases : List SealedTree
    baseCodes : List Code
open BaseClosure public

loadClosure : String → List String → IO.IO (Maybe BaseClosure)
loadClosure ws names = entries (ws ++ˢ "/trees") >>= λ trees →
  resolveTips ws (suc (length trees)) names CAS.>>=? λ ps →
  CAS.newCommitHomeReader dir >>= λ readHome →
  CAS.newDAGReader dir CAS.commitK (ancestry readHome dir) >>= λ read →
  readMany (verified read) ps CAS.>>=? λ all →
    let bs = nubᵇ (λ a b → tip a ==ˢ tip b) all
        cs = concatMap (λ b → NT.exported (snapshot b)) bs
    in IO.return (Data.Maybe.when (consistentCodes cs) (closure ps bs (uniqueCodes cs)))
  where
    dir = ws ++ˢ "/store"
    verified : CAS.Reader (List SealedTree) → CAS.Reader (List SealedTree)
    verified read key = verifyCommitDAG dir key >>= λ valid → if valid then read key else IO.return nothing

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

exportCodes : String → String → List Code → IO.IO String
exportCodes ws tree [] = IO.return ""
exportCodes ws tree (c ∷ cs) = putCode (ws ++ˢ "/store/objects") c >>= λ canonical →
  sha256 (render c) >>= λ source → exportCodes ws tree cs >>= λ rest →
  IO.return ("module\t" ++ˢ tree ++ˢ "/" ++ˢ intersperse "." (full (modName c)) ++ˢ "\t" ++ˢ canonical ++ˢ "\t" ++ˢ source ++ˢ "\n" ++ˢ rest)

-- Check existing public names before changing either the tree ref or exports.
exportsAgree : String → String → List Code → IO.IO Bool
exportsAgree ws tree cs = successfulTrees ws >>= trees
  where
    files : String → List Code → IO.IO Bool
    files dir [] = IO.return true
    files dir (c ∷ rest) = let path = dir ++ˢ "/" ++ˢ modulePath c in fileExists path >>= λ exists →
      if exists then (F.readFile path >>= λ text → if text ==ˢ render c then files dir rest else IO.return false)
      else files dir rest
    trees : List String → IO.IO Bool
    trees [] = IO.return true
    trees (n ∷ ns) = if n ==ˢ tree then trees ns else
      files (ws ++ˢ "/generated/" ++ˢ n) cs >>= λ ok → if ok then trees ns else IO.return false

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

-- Each export is a complete tree. Agda rejects even byte-identical modules
-- on two include paths, so present shared exports once to scripts and Main.
withOpenIncludes : ∀ {A : Set} → String → String → (List String → IO.IO A) → IO.IO A
withOpenIncludes repo ws use = withTempDirectory (ws ++ˢ "/tmp/export-view") λ dir →
  successfulTrees ws >>= collect dir >> use (dir ∷ repo ∷ "/usr/share/agda-stdlib" ∷ [])
  where
    copyFiles : String → String → List String → IO.IO ⊤
    copyFiles src dst [] = IO.return tt
    copyFiles src dst (file ∷ fs) = do
      let relative = fromList (Data.List.drop (suc (length (toList src))) (toList file))
          to = dst ++ˢ "/" ++ˢ relative
          parent = parentPath (wordsBy ('/' Char.≟_) relative)
      text ← F.readFile file
      present ← fileExists to
      if present then (F.readFile to >>= λ other → if text ==ˢ other then IO.return tt else
        failIO ("ambiguous exported module: " ++ˢ relative)) else
        (mkdirP (dst ++ˢ "/" ++ˢ parent) >> F.writeFile to text)
      copyFiles src dst fs
    collect : String → List String → IO.IO ⊤
    collect dst [] = IO.return tt
    collect dst (n ∷ ns) = let src = ws ++ˢ "/generated/" ++ˢ n in
      sourcesIn src >>= copyFiles src dst >> collect dst ns

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
