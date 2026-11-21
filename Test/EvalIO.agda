{-# OPTIONS --guardedness #-}
module Test.EvalIO where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Maybe using (nothing; just)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import Ownership hiding (_>>=_; _>>_; Home; set)
open import OwnershipIO
open import OwnershipIO.FFI
open import Code using (QName; Decl; Expr; eqCode; eqDecls; eqList; _==ˢ_;
  mkQ; decls; plain; sig; fun; clause; head; rhs; def; set)
open import Code.Codecs
open import Code.Tree using (HomeSt; node; codesOf; memoryOf)
open import Test.HarnessPure using (homeX; taskX; onePlan; pureEnv; impl; grownTree)
open import Code.Harness using (nodeAgent; NodeΨ)
open import Code.SessionRunner using (runNode)
open import Code.Store using (putCode; getCode)
open import Code.Encode using (encodeCanonical; encodeShape)
open import Code.SExpr using (showSExpr)
open import Code.Transport using (ok; contradiction; SpecΔ; specΔ; child; newIface; stubOf; satisfies; withTests; localizeTo)
open import Code.Render using (render)

report : String → IO.IO Bool → IO.IO Bool
report label action = action IO.>>= λ b → F.putStrLn ((if b then "PASS " else "FAIL ") ++ˢ label) IO.>>= λ _ → IO.return b

t1 : IO.IO Bool
t1 = evalIO (liftEnv {{nc = (λ _ → tt , tt , tt , tt) , tt}} ((λ _ → provide [] worker) ∷ [])) delegated tt IO.>>= λ r → IO.return (proj₂ r ≡ᵇ 42)

t2 : IO.IO Bool
t2 = evalIO (liftEnv {{nc = (λ _ → (tt , tt) , (λ _ → tt)) , tt}} ((λ _ → provide [] (daemon dbServer)) ∷ [])) system tt IO.>>= λ r → IO.return (proj₂ r ≡ᵇ 7)

tLegacyWake : IO.IO Bool
tLegacyWake = evalIO (liftEnv {{nc = (λ _ → (tt , tt , tt) , ((tt , tt , tt) , tt)) , tt}}
  ((λ _ → provide [] mockAgent) ∷ [])) wake (("old code" , "the test" , tt) , tt) IO.>>= λ r →
  IO.return ((proj₂ r ==ˢ "ok") ∧ (proj₁ (proj₁ (proj₁ r)) ==ˢ "new spec")
    ∧ (proj₁ (proj₂ (proj₁ (proj₁ r))) ==ˢ "the test"))

t3 : IO.IO Bool
t3 with grownTree
... | sh , home = storeHome "tmp/tests/store" (sh , liftModel (homeNoChan sh) home) IO.>>= λ _ → loadHome "tmp/tests/store" IO.>>= λ where
  nothing → IO.return false
  (just (sh′ , m)) → IO.return ((showSExpr (encodeShape sh) ==ˢ showSExpr (encodeShape sh′))
    ∧ eqList eqCode (codesOf sh home) (codesOf sh′ (dropModel (homeNoChan sh′) m))
    ∧ eqMemory (memoryOf sh home) (memoryOf sh′ (dropModel (homeNoChan sh′) m)))

t4 : IO.IO Bool
t4 = sha256 "abc" IO.>>= λ h → putCode "tmp/tests/objects" (impl "X") IO.>>= λ key → getCode "tmp/tests/objects" key IO.>>= λ where
  nothing → IO.return false
  (just c) → IO.return ((h ==ˢ "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
                      ∧ (encodeCanonical c ==ˢ encodeCanonical (impl "X")))

-- A runtime test, deliberately not a refl proof: test-evalio.sh compiles at
-- -O0, where lifted tables and beta-expanded lets used to explode by depth 3.
-- The law reaches 35 concrete helpers; 30 unrelated declarations widen the
-- tables, and an optional test exercises withTests' append path.
private
  deepModule : QName
  deepModule = mkQ ("DeepSpec" ∷ [])

  deepName : String → QName
  deepName n = mkQ ("DeepSpec" ∷ n ∷ [])

  helperName : ℕ → String
  helperName n = "helper" ++ˢ show n

  deepFunction : String → Expr → List Decl
  deepFunction n body = sig plain n (set 1)
    ∷ fun plain n (clause (head (deepName n) []) (rhs body) [] ∷ []) ∷ []

  helperBody : ℕ → Expr
  helperBody zero = set 0
  helperBody (suc n) = def (deepName (helperName n))

  helperChain : ℕ → List Decl
  helperChain zero = []
  helperChain (suc n) = deepFunction (helperName n) (helperBody n) ++ helperChain n

  extraDecls : ℕ → List Decl
  extraDecls zero = []
  extraDecls (suc n) = sig plain ("extra" ++ˢ show n) (set 0) ∷ extraDecls n

  deepCore deepIface : List Decl
  deepCore = sig plain "law" (def (deepName (helperName 34))) ∷ (helperChain 35 ++ extraDecls 30)
  deepIface = deepCore ++ deepFunction "example" (def (deepName (helperName 34)))

  deepSpec : SpecΔ
  deepSpec = specΔ deepModule deepIface []

  deepSharing : SpecΔ → List Decl → Bool
  deepSharing δ expectedCore with stubOf δ
  ... | stub with withTests stub (newIface δ)
  ... | tested =
    -- String length forces the entire render, not just its first constructor.
    not (Data.String.length (render stub) ≡ᵇ 0)
    ∧ eqDecls (decls stub) (localizeTo (child δ) expectedCore)
    ∧ satisfies δ stub
    ∧ eqDecls (decls tested) (localizeTo (child δ) (newIface δ))
    ∧ satisfies δ tested

  -- A generous ceiling makes a recomputation regression fail instead of
  -- hanging the suite. Force the Bool inside the timeout, despite lazy IO.
  postulate sharingWithinBudget : Bool → IO.IO Bool

  {-# FOREIGN GHC import qualified Control.Exception as SharingException #-}
  {-# FOREIGN GHC import qualified System.Timeout as SharingTimeout #-}
  {-# COMPILE GHC sharingWithinBudget = \b -> fmap (maybe False id) (SharingTimeout.timeout 5000000 (SharingException.evaluate b)) #-}

tDeepSharing : IO.IO Bool
tDeepSharing = sharingWithinBudget (deepSharing deepSpec deepCore)

main : IO.IO ⊤
main = report "pure/IO resource delegation" t1 IO.>>= λ a →
  report "indexed service compatibility" t2 IO.>>= λ b →
  report "dynamic generation store/load" t3 IO.>>= λ c →
  report "SHA-256 and canonical content store" t4 IO.>>= λ d →
  report "legacy wake preserves the returned home" tLegacyWake IO.>>= λ e →
  report "35-deep spec helper sharing at -O0" tDeepSharing IO.>>= λ f →
  if a ∧ b ∧ c ∧ d ∧ e ∧ f then F.putStrLn "ALL PASS" else exitFailure
