{-# OPTIONS --guardedness #-}
module Test.StoreCAS where

open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_; length; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat.Base using (ℕ; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String; toList; fromList; replicate) renaming (_++_ to _++ˢ_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO.Primitive using (IO; return; _>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import OwnershipIO using (ModelIO; ModelsIO)
open import OwnershipIO.FFI using (failIO; listDirectory; removeAll)
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp; readUTF8; writeUTF8)
open import Code using (Code; Name; code; qn; mkQ; sig; plain; def; fun; clause; head; rhs;
                       lit; natL; eqCode; eqDecls; eqList; _==ˢ_; unit)
open import Code.Tree using (HomeShape; node; HomeSt; KidsCtx; Leaves; Interface)
open import Code.Transport using (Memory)
open import Code.Codecs using (HomeValue; eqMemory)
import Code.Store as Legacy
import Code.Parse as Parse
open import Store.CAS
open import Store.Verify

private
  assert : String → Bool → IO ⊤
  assert label true = return tt
  assert label false = failIO ("StoreCAS: " ++ˢ label)

  require : ∀ {A : Set} → String → Maybe A → IO A
  require label nothing = failIO ("StoreCAS: missing " ++ˢ label)
  require label (just a) = return a

  zeroHash = replicate 64 '0'

  _ : validHash (replicate 64 'f') ≡ true
  _ = refl
  _ : validHash (replicate 64 'F') ≡ false
  _ = refl
  _ : validHash (replicate 63 '0') ≡ false
  _ = refl
  _ : validHash (replicate 65 '0') ≡ false
  _ = refl
  _ : validHash (replicate 64 'ａ') ≡ false
  _ = refl

  iface : String → Interface
  iface shown = sig plain "value" (def (qn ("Data" ∷ "Nat" ∷ "ℕ" ∷ []) shown)) ∷ []

  memory : Name → String → Memory
  memory n shown = (unit (qn (n ∷ "value" ∷ []) shown) , "搬运\n\"note\"\t\\" ∷ n ∷ []) ∷ []

  program : Name → ℕ → Code
  program n v = code (qn (n ∷ []) "presentation") [] (iface "ℕ" ++
    (fun plain "value" (clause (head (mkQ (n ∷ "value" ∷ [])) []) (rhs (lit (natL v))) [] ∷ []) ∷ []))

  leaves : Name → ℕ → ModelsIO Leaves
  leaves n v = program n v , memory n "local.value" , iface "local.ℕ" , tt

  branchB = node (("Inner" , node []) ∷ [])
  bModel : ModelIO (HomeSt branchB)
  bModel = leaves "Inner" 7 , leaves "B" 6

  tree : ℕ → HomeValue
  tree v = node (("A" , node []) ∷ ("B" , branchB) ∷ []) ,
           leaves "A" v , bModel , leaves "Root" 0

  reversedTree : HomeValue
  reversedTree = node (("B" , branchB) ∷ ("A" , node []) ∷ []) ,
                 bModel , leaves "A" 1 , leaves "Root" 0

  -- Compare both dependent shapes and every code, memory and interface leaf.
  mutual
    sameTree : (sh sh′ : HomeShape) → ModelIO (HomeSt sh) → ModelIO (HomeSt sh′) → Bool
    sameTree (node ks) (node js) = sameKids ks js

    sameKids : (ks js : List (Name × HomeShape)) → ModelsIO (KidsCtx ks ++ Leaves) →
               ModelsIO (KidsCtx js ++ Leaves) → Bool
    sameKids [] [] (c , m , i , _) (c′ , m′ , i′ , _) =
      eqCode c c′ ∧ eqMemory m m′ ∧ eqDecls i i′
    sameKids ((n , sh) ∷ ks) ((p , sh′) ∷ js) (x , xs) (y , ys) =
      (n ==ˢ p) ∧ sameTree sh sh′ x y ∧ sameKids ks js xs ys
    sameKids _ _ _ _ = false

  sameHome : HomeValue → HomeValue → Bool
  sameHome (sh , m) (sh′ , m′) = sameTree sh sh′ m m′

  kidHash : Name → List Kid → Maybe Hash
  kidHash _ [] = nothing
  kidHash n ((p , h) ∷ ks) = if n ==ˢ p then just h else kidHash n ks
    where open import Data.Bool.Base using (if_then_else_)

  changedByte : List Char → List Char
  changedByte [] = []
  changedByte ('1' ∷ cs) = '9' ∷ cs
  changedByte (c ∷ cs) = c ∷ changedByte cs

  history : String → Hash → Hash → IO Hash
  history dir old new = do
    first ← putCommit dir (commit [] old "T0" "建树")
    let reason = "move \"A\"\nkeep B"
    next ← putCommit dir (commit (first ∷ []) new "T1" reason)
    sibling ← putCommit dir (commit (first ∷ []) new "T1-other" "")
    tip ← putCommit dir (commit (next ∷ sibling ∷ []) new "T2" "merge")
    c ← getCommit dir next >>= require "commit"
    assert "commit fields" (eqList _==ˢ_ (parents c) (first ∷ []) ∧
      (rootHome c ==ˢ new) ∧ (epoch c ==ˢ "T1") ∧ (why c ==ˢ reason))
    writeRef dir "heads/main" first
    writeRef dir "heads/main" tip
    ref ← readRef dir "heads/main" >>= require "ref"
    assert "atomic ref replacement" (ref ==ˢ tip)
    verifyCommitDAG dir ref >>= assert "complete merge history"
    missing ← putCommit dir (commit (first ∷ zeroHash ∷ []) new "" "")
    verifyCommitDAG dir missing >>= λ ok → assert "missing second parent" (not ok)
    return tip

  runTests : String → IO ⊤
  runTests dir = do
    old ← storeHomeCAS dir (tree 1)
    saved ← loadHomeCAS dir old >>= require "old home"
    assert "complete round trip" (sameHome (tree 1) saved)
    sorted ← storeHomeCAS dir reversedTree
    assert "permuting child slots preserves the root" (old ==ˢ sorted)
    assert "interface canonicalizes shown" (encodeIfaceBlob (iface "X") ==ˢ encodeIfaceBlob (iface "Y"))
    assert "memory canonicalizes shown" (encodeMemBlob (memory "A" "X") ==ˢ encodeMemBlob (memory "A" "Y"))
    putStrLn "PASS  HomeValue round trip, canonical order and presentation"

    before ← listDirectory (dir ++ˢ "/objects/home")
    new ← storeHomeCAS dir (tree 2)
    after ← listDirectory (dir ++ˢ "/objects/home")
    oldNode ← getHomeNode dir old >>= require "old node"
    newNode ← getHomeNode dir new >>= require "new node"
    oldB ← require "old B" (kidHash "B" (kids oldNode))
    newB ← require "new B" (kidHash "B" (kids newNode))
    oldA ← require "old A" (kidHash "A" (kids oldNode))
    newA ← require "new A" (kidHash "A" (kids newNode))
    assert "B shares its object, A and root changed"
      ((oldB ==ˢ newB) ∧ not (oldA ==ˢ newA) ∧ not (old ==ˢ new))
    assert "only two new home objects" (length after ≡ᵇ ℕ.suc (ℕ.suc (length before)))
    a ← getHomeNode dir oldA >>= require "A"
    legacy ← Legacy.putCode (dir ++ˢ "/legacy") (program "A" 1)
    assert "Code.Store SHA-256 compatibility" (legacy ==ˢ codeHash a)
    putStrLn "PASS  Merkle sharing and legacy code hash"

    tip ← history dir old new
    putStrLn "PASS  named refs, merge parents and missing-parent rejection"
    let path = objectPath dir codeK (codeHash a)
    bytes ← readUTF8 path >>= require "code blob"
    let damaged = fromList (changedByte (toList bytes))
    assert "one ASCII byte changed in still-decodable code"
      (not (damaged ==ˢ bytes) ∧ is-just (Parse.parse damaged))
    writeUTF8 path damaged
    loadHomeCAS dir old >>= λ h → assert "damaged leaf rejected" (is-nothing h)
    verifyCommitDAG dir tip >>= λ ok → assert "damage in parent history rejected" (not ok)
    fresh ← loadHomeCAS dir new >>= require "unaffected new root"
    assert "new branch still readable" (sameHome (tree 2) fresh)
    writeUTF8 path bytes
    verifyCommitDAG dir tip >>= assert "restored bytes verified on a fresh traversal"
    removeAll (objectPath dir homeK newB)
    loadHomeCAS dir new >>= λ h → assert "missing shared home rejected" (is-nothing h)
    verifyCommitDAG dir tip >>= λ ok → assert "missing shared home invalidates commit" (not ok)
    putStrLn "PASS  one-byte tampering and missing descendants rejected"
    where import Data.Nat.Base as ℕ

main : IO ⊤
main = withPrivateTemp "/tmp" runTests
