{-# OPTIONS --guardedness #-}
module Code.Codecs where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership using (Dir)
open import OwnershipIO
open import OwnershipIO.FFI
open import Code hiding (Name; set)
open import Code.SExpr using (showSExpr)
open import Code.Encode
open import Code.Parse using (parse; parseMemory; parseDecls; parseShape)
open import Code.Render using (render)
open import Code.Transport using (Memory)
open import Code.Tree using (Interface; Home; HomeShape; node; HomeSt; HomeCtx; KidsCtx; Leaves)

codeCodec : Codec Code
codeCodec = record { ext = ".sexp" ; encode = λ c → showSExpr (encodeCode c) ; decode = parse ; views = (".agda" , render) ∷ [] }

memoryCodec : Codec Memory
memoryCodec = record { ext = ".sexp" ; encode = λ m → showSExpr (encodeMemory m) ; decode = parseMemory ; views = [] }

ifaceCodec : Codec Interface
ifaceCodec = record { ext = ".sexp" ; encode = λ ds → showSExpr (encodeDecls ds) ; decode = parseDecls ; views = [] }

homeCodecs : (sh : HomeShape) → Codecs (HomeSt sh)
kidsCodecs : (ks : List (Code.Name × HomeShape)) → CodecsAll (KidsCtx ks ++ Leaves)
homeCodecs (node ks) = kidsCodecs ks
kidsCodecs [] = codeCodec , memoryCodec , ifaceCodec , tt
kidsCodecs ((n , sh) ∷ ks) = homeCodecs sh , kidsCodecs ks

homeNoChan : (sh : HomeShape) → NoChan (HomeSt sh)
kidsNoChan : (ks : List (Code.Name × HomeShape)) → NoChanAll (KidsCtx ks ++ Leaves)
homeNoChan (node ks) = kidsNoChan ks
kidsNoChan [] = tt , tt , tt , tt
kidsNoChan ((_ , sh) ∷ ks) = homeNoChan sh , kidsNoChan ks

HomeValue : Set
HomeValue = Σ HomeShape (λ sh → ModelIO (HomeSt sh))

-- Immutable generations plus one atomically replaced manifest commit the
-- entire dynamic tree (shape and all three leaf types) together.
storeGeneration : String → HomeValue → IO.IO String
storeGeneration path (sh , m) = freshDirectory (path ++ˢ "/versions") IO.>>= λ generation →
  store generation {HomeSt sh} (homeCodecs sh) m IO.>>= λ _ →
  F.writeFile (generation ++ˢ "/shape.sexp") (showSExpr (encodeShape sh)) IO.>>= λ _ →
  IO.return generation

storeHome : String → HomeValue → IO.IO ⊤
storeHome path h = storeGeneration path h IO.>>= λ generation →
  F.writeFile (path ++ˢ "/current.new") generation IO.>>= λ _ →
  atomicRename (path ++ˢ "/current.new") (path ++ˢ "/current")

loadShape : String → Maybe HomeShape → IO.IO (Maybe HomeValue)
loadShape dir nothing = IO.return nothing
loadShape dir (just sh) = load dir {HomeSt sh} (homeCodecs sh) IO.>>= λ where
  nothing → IO.return nothing
  (just m) → IO.return (just (sh , m))

loadHome : String → IO.IO (Maybe HomeValue)
loadHome path = fileExists (path ++ˢ "/current") IO.>>= λ where
  false → IO.return nothing
  true → F.readFile (path ++ˢ "/current") IO.>>= λ generation →
    F.readFile (generation ++ˢ "/shape.sexp") IO.>>= λ txt → loadShape generation (parseShape txt)

eqMemory : Memory → Memory → Bool
eqMemory [] [] = true
eqMemory ((o , ns) ∷ m) ((o′ , ns′) ∷ m′) = (o ==ᴼ o′) ∧ eqList _==ˢ_ ns ns′ ∧ eqMemory m m′
eqMemory _ _ = false
