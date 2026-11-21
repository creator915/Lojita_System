{-# OPTIONS --guardedness #-}
module Store.CAS where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.Char as Char using (toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; all; length; take)
open import Data.Maybe.Base as M using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; pred; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; intersperse; wordsBy) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
open import OwnershipIO using (ModelIO; ModelsIO)
open import OwnershipIO.FFI using (dirExists; fileExists; listDirectory; atomicRename;
                                 sha256; failIO; IORef; newIORef; readIORef; writeIORef)
open import OwnershipIO.MetaFFI using (withPrivateTemp; readUTF8; readVerifiedUTF8; writeUTF8; _>>_)
open import Code using (Code; Name; _==ˢ_; eqCode; eqDecls)
open import Code.SExpr using (SExpr; sym; str; list; showSExpr; parseSExpr)
import Code.Encode as E
import Code.Parse as P
open import Code.Tree using (HomeShape; node; HomeSt; Interface; KidsCtx; Leaves)
open import Code.Transport using (Memory)
open import Code.Codecs using (HomeValue; eqMemory)
open import Store.Object public

private
  toSExpr : Form → SExpr
  toSExpr (quoted s) = str s
  toSExpr (tagged t xs) = list (sym t ∷ fields xs)
    where
    fields : List Form → List SExpr
    fields [] = []
    fields (x ∷ rest) = toSExpr x ∷ fields rest

  mutual
    fromSExpr : SExpr → Maybe Form
    fromSExpr (str s) = just (quoted s)
    fromSExpr (list (sym t ∷ xs)) = M.map (tagged t) (fromFields xs)
    fromSExpr _ = nothing

    fromFields : List SExpr → Maybe (List Form)
    fromFields [] = just []
    fromFields (x ∷ xs) = M.zipWith _∷_ (fromSExpr x) (fromFields xs)

  wire : Format Form
  wire = format (λ x → showSExpr (toSExpr x)) (λ s → parseSExpr s M.>>= fromSExpr)

open Objects {Code} {Interface} {Memory}
  (format E.encodeCanonical P.parse)
  (format (λ i → showSExpr (E.canonical (E.encodeDecls i))) P.parseDecls)
  (format (λ m → showSExpr (E.canonical (E.encodeMemory m))) P.parseMemory)
  wire public

private
  infixl 6 _/_
  _/_ : String → String → String
  a / b = a ++ˢ "/" ++ˢ b

  kindDir : String → Kind → String
  kindDir dir k = dir / "objects" / kindName k

objectPath : String → Kind → Hash → String
objectPath dir k key = kindDir dir k / (key ++ˢ ".sexp")

infixl 1 _>>=?_
_>>=?_ : ∀ {A B : Set} → IO (Maybe A) → (A → IO (Maybe B)) → IO (Maybe B)
action >>=? next = action >>= λ where
  nothing → return nothing
  (just a) → next a

private
  publish : (parent path bytes key : String) → IO ⊤
  publish parent path bytes key = withPrivateTemp parent λ tmp → do
    let staged = tmp / "object"
    writeUTF8 staged bytes
    readVerifiedUTF8 staged key >>= λ where
      nothing → failIO "CAS: staged bytes failed SHA-256 verification"
      (just _) → atomicRename staged path

putWith : String → (k : Kind) → Format (Payload k) → Payload k → IO Hash
putWith dir k f value = put (encode f value)
  where
  put : String → IO Hash
  put bytes with decode f bytes
  ... | nothing = failIO ("CAS: invalid " ++ˢ kindName k ++ˢ " object")
  ... | just _ = do
    key ← sha256 bytes
    let path = objectPath dir k key
    exists ← fileExists path
    if exists then (readVerifiedUTF8 path key >>= λ where
      nothing → failIO ("CAS: corrupt existing object " ++ˢ path)
      (just _) → return key)
      else (publish (kindDir dir k) path bytes key >>= λ _ → return key)

getWith : String → (k : Kind) → Format (Payload k) → Hash → IO (Maybe (Payload k))
getWith dir k f key = if validHash key then
  (readVerifiedUTF8 (objectPath dir k key) key >>=? λ bytes → return (decode f bytes))
  else return nothing

putObject : String → (k : Kind) → Payload k → IO Hash
putObject dir k = putWith dir k (objectFormat k)

getObject : String → (k : Kind) → Hash → IO (Maybe (Payload k))
getObject dir k = getWith dir k (objectFormat k)

putCommit : String → CommitObj → IO Hash
putCommit dir = putObject dir commitK

getCommit : String → Hash → IO (Maybe CommitObj)
getCommit dir = getObject dir commitK

getHomeNode : String → Hash → IO (Maybe HomeNodeObj)
getHomeNode dir = getObject dir homeK

private
  refParts : String → List String
  refParts = wordsBy ('/' Char.≟_)

  validRef : String → Bool
  validRef name = not (name ==ˢ "") ∧ (intersperse "/" parts ==ˢ name) ∧ all component parts
    where
    parts = refParts name
    component : String → Bool
    component s = not ((s ==ˢ ".") ∨ (s ==ˢ "..")) ∧
      all (λ c → not ((toℕ c <ᵇ 32) ∨ primCharEquality c '\\')) (toList s)

writeRef : String → String → Hash → IO ⊤
writeRef dir name key = if validRef name ∧ validHash key then
  (let parts = refParts name
       parent = intersperse "/" (take (pred (length parts)) parts)
   in sha256 key >>= publish (dir / "refs" / parent) (dir / "refs" / name) key)
  else failIO "CAS: invalid ref name or digest"

readRef : String → String → IO (Maybe Hash)
readRef dir name = if validRef name then
  (readUTF8 (dir / "refs" / name) >>=? λ key → return (M.when (validHash key) key))
  else return nothing

private
  -- The semantic CAS erases QName.shown. Its companion Merkle tree uses
  -- lossless leaf encodings so old and new aliases can coexist. Both roots
  -- are pinned by the commit; neither view is selected by a mutable hint.
  Formats = (k : Kind) → Format (Payload k)
  displayFormat : Formats
  displayFormat codeK = format (λ c → showSExpr (E.encodeCode c)) P.parse
  displayFormat ifaceK = format (λ ds → showSExpr (E.encodeDecls ds)) P.parseDecls
  displayFormat memK = format (λ m → showSExpr (E.encodeMemory m)) P.parseMemory
  displayFormat homeK = objectFormat homeK
  displayFormat commitK = objectFormat commitK

  -- Presentation leaves may carry the exact source bytes accepted by the
  -- frontend. The commit pins this pair, so simultaneous spellings of the
  -- same semantic Code never overwrite each other. Old bare-Code leaves
  -- remain readable.
  putDisplay : String → List (Code × String) → Code → IO Hash
  putDisplay dir views c with Code.authoredPoint views c
  ... | nothing = putWith dir codeK (displayFormat codeK) c
  ... | just (ir , src) = do
    let bytes = showSExpr (list (sym "surface" ∷ E.encodeCode c ∷ E.encodeCode ir ∷ str src ∷ []))
    key ← sha256 bytes
    publish (kindDir dir codeK) (objectPath dir codeK key) bytes key
    return key

  Display = Code × Maybe (Code × String)

  readDisplay : String → Hash → IO (Maybe Display)
  readDisplay dir key = if validHash key then
    (readVerifiedUTF8 (objectPath dir codeK key) key >>=? λ bytes → return (unpack bytes (parseSExpr bytes)))
    else return nothing
    where
      unpack : String → Maybe SExpr → Maybe Display
      unpack bytes (just (list (sym "surface" ∷ term ∷ scoped ∷ str src ∷ []))) =
        P.decodeCode term M.>>= λ c → P.decodeCode scoped M.>>= λ ir →
          let encoded = showSExpr (list (sym "surface" ∷ E.encodeCode c ∷ E.encodeCode ir ∷ str src ∷ []))
          in M.when ((bytes ==ˢ encoded) ∧ eqCode (Code.surfaceCode c) ir) (c , just (ir , src))
      unpack bytes (just (list (sym "surface" ∷ term ∷ str src ∷ []))) = P.decodeCode term M.>>= λ c →
        let encoded = showSExpr (list (sym "surface" ∷ E.encodeCode c ∷ str src ∷ []))
        in M.when (bytes ==ˢ encoded) (c , just (c , src))
      unpack bytes _ = M.map (_, nothing) (decode (displayFormat codeK) bytes)

  mutual
    storeNode : Formats → (Code → IO Hash) → String → (sh : HomeShape) → ModelIO (HomeSt sh) → IO Hash
    storeNode fmt saveCode dir (node ks) model = storeKids fmt saveCode dir ks model >>= putObject dir homeK

    storeKids : Formats → (Code → IO Hash) → String → (ks : List (Name × HomeShape)) →
                ModelsIO (KidsCtx ks ++ Leaves) → IO HomeNodeObj
    storeKids fmt saveCode dir [] (c , m , i , _) = do
      ch ← saveCode c
      ih ← putWith dir ifaceK (fmt ifaceK) i
      mh ← putWith dir memK (fmt memK) m
      return (homeNode ch ih mh [])
    storeKids fmt saveCode dir ((n , sh) ∷ ks) (child , rest) = do
      key ← storeNode fmt saveCode dir sh child
      h ← storeKids fmt saveCode dir ks rest
      return (record h { kids = (n , key) ∷ kids h })

storeHomeCAS : String → HomeValue → IO Hash
storeHomeCAS dir (sh , model) = storeNode objectFormat (putObject dir codeK) dir sh model

storeTreeWithSurfaces : List (Code × String) → String → List Hash → String → String → HomeValue → IO Hash
storeTreeWithSurfaces sources dir ps e reason h@(sh , model) = do
  root ← storeHomeCAS dir h
  let views = dir / "presentation"
  view ← storeNode displayFormat (putDisplay views sources) views sh model
  putCommit dir (commitWithView ps root e reason (just view))

storeTreeCommit : String → List Hash → String → String → HomeValue → IO Hash
storeTreeCommit = storeTreeWithSurfaces []

-- A fresh traversal takes its depth bound from the number of objects on disk.
-- Each successful address is memoized across siblings and merge parents. A
-- pending entry rejects back edges. No cache survives a new verification.
Reader : Set → Set
Reader A = Hash → IO (Maybe A)

newDAGReader : ∀ {A : Set} → String → Kind → (Reader A → Reader A) → IO (Reader A)
newDAGReader {A} dir k step = do
  exists ← dirExists (kindDir dir k)
  names ← if exists then listDirectory (kindDir dir k) else return []
  cache ← newIORef []
  return (walk cache (length names))
  where
  Cache = List (Hash × Maybe A)
  lookup : Hash → Cache → Maybe (Maybe A)
  lookup h [] = nothing
  lookup h ((key , value) ∷ xs) = if h ==ˢ key then just value else lookup h xs

  walk : IORef Cache → ℕ → Reader A
  walk cache depth key = readIORef cache >>= λ entries → visit (lookup key entries) entries depth
    where
    visit : Maybe (Maybe A) → Cache → ℕ → IO (Maybe A)
    visit (just known) _ _ = return known
    visit nothing _ zero = return nothing
    visit nothing entries (suc n) = do
      writeIORef cache ((key , nothing) ∷ entries)
      step (walk cache n) key >>=? λ a → do
        current ← readIORef cache
        writeIORef cache ((key , just a) ∷ current)
        return (just a)

private
  assemble : List (Name × HomeValue) → ModelsIO Leaves → HomeValue
  assemble [] leaves = node [] , leaves
  assemble ((n , sh , child) ∷ cs) leaves with assemble cs leaves
  ... | node ks , rest = node ((n , sh) ∷ ks) , child , rest

  loadKids : Reader HomeValue → List Kid → IO (Maybe (List (Name × HomeValue)))
  loadKids read [] = return (just [])
  loadKids read ((n , h) ∷ ks) = read h >>=? λ child →
    loadKids read ks >>=? λ cs → return (just ((n , child) ∷ cs))

  loadNode : Formats → Reader Code → String → Reader HomeValue → Reader HomeValue
  loadNode fmt readCode dir read key = getHomeNode dir key >>=? λ h →
    readCode (codeHash h) >>=? λ c →
    getWith dir ifaceK (fmt ifaceK) (specHash h) >>=? λ i →
    getWith dir memK (fmt memK) (memHash h) >>=? λ m →
    loadKids read (kids h) >>=? λ cs → return (just (assemble cs (c , m , i , tt)))

newHomeReader : String → IO (Reader HomeValue)
newHomeReader dir = newDAGReader dir homeK (loadNode objectFormat (getObject dir codeK) dir)

loadHomeCAS : String → Hash → IO (Maybe HomeValue)
loadHomeCAS dir key = newHomeReader dir >>= λ read → read key

private
  mutual
    sameTree : (a b : HomeShape) → ModelIO (HomeSt a) → ModelIO (HomeSt b) → Bool
    sameTree (node ks) (node js) h h′ = sameKids ks js h h′

    sameKids : (ks js : List (Name × HomeShape)) →
      ModelsIO (KidsCtx ks ++ Leaves) → ModelsIO (KidsCtx js ++ Leaves) → Bool
    sameKids [] [] (c , m , i , _) (c′ , m′ , i′ , _) = eqCode c c′ ∧ eqMemory m m′ ∧ eqDecls i i′
    sameKids ((n , sh) ∷ ks) ((p , sh′) ∷ js) (x , xs) (y , ys) =
      (n ==ˢ p) ∧ sameTree sh sh′ x y ∧ sameKids ks js xs ys
    sameKids _ _ _ _ = false

-- Read canonical leaves first, then check the display tree against them.
-- Older commits with no companion tree retain their original wire format.
newCommitHomeReader : String → IO (CommitObj → IO (Maybe HomeValue))
newCommitHomeReader dir = do
  semantic ← newHomeReader dir
  let views = dir / "presentation"
  display ← newDAGReader views homeK (loadNode displayFormat (λ key → readDisplay views key >>= λ v → return (M.map Data.Product.proj₁ v)) views)
  return λ c → semantic (rootHome c) >>=? λ h → selectView display (presentation c) h
  where
    selectView : Reader HomeValue → Maybe Hash → HomeValue → IO (Maybe HomeValue)
    selectView _ nothing h = return (just h)
    selectView read (just key) (sh , m) = read key >>=? λ { shown@(sh′ , m′) → return (M.when (sameTree sh sh′ m m′) shown) }

-- The caller opens a verified commit. Source associations are pinned by
-- its presentation root and addressed by their own SHA-256 leaves.
commitSurfaces : String → Hash → IO (Maybe (List (Code × String)))
commitSurfaces dir tip = getCommit dir tip >>=? λ c → fromView (presentation c)
  where
    views = dir / "presentation"
    kidsOf : Reader (List (Code × String)) → List Kid → IO (Maybe (List (Code × String)))
    kidsOf read [] = return (just [])
    kidsOf read ((_ , key) ∷ ks) = read key >>=? λ first → kidsOf read ks >>=? λ rest → return (just (first ++ rest))
    step : Reader (List (Code × String)) → Reader (List (Code × String))
    step read key = getHomeNode views key >>=? λ h → readDisplay views (codeHash h) >>=? λ where
      (c , nothing) → kidsOf read (kids h)
      (c , just point) → kidsOf read (kids h) >>=? λ more → return (just (point ∷ more))
    fromView : Maybe Hash → IO (Maybe (List (Code × String)))
    fromView nothing = return (just [])
    fromView (just key) = newDAGReader views homeK step >>= λ read → read key
