{-# OPTIONS --safe #-}
module Backend.Mode where

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- §1  Pluggable Backend Modes & Environment Parsing
------------------------------------------------------------------------

data BackendMode : Set where
  legacyAgda  : BackendMode   -- 100% original dump + agda + MAlonzo pipeline
  leanPrism   : BackendMode   -- O(n) Prism interceptor -> Lean 4 + C, with ⊥ fallback to legacyAgda
  shadowAudit : BackendMode   -- Dual execution: cross-checks leanPrism against legacyAgda

private
  _==ˢ_ : String → String → Bool
  _==ˢ_ = primStringEquality

parseBackendMode : String → Maybe BackendMode
parseBackendMode s =
  if s ==ˢ "legacy"      then just legacyAgda  else
  if s ==ˢ "agda"        then just legacyAgda  else
  if s ==ˢ "legacy-agda" then just legacyAgda  else
  if s ==ˢ "prism"       then just leanPrism   else
  if s ==ˢ "lean"        then just leanPrism   else
  if s ==ˢ "lean4"       then just leanPrism   else
  if s ==ˢ "lean-prism"  then just leanPrism   else
  if s ==ˢ "audit"       then just shadowAudit else
  if s ==ˢ "dual"        then just shadowAudit else
  if s ==ˢ "shadow"      then just shadowAudit else
  nothing

showBackendMode : BackendMode → String
showBackendMode legacyAgda  = "legacy-agda"
showBackendMode leanPrism   = "lean-prism"
showBackendMode shadowAudit = "shadow-audit"

------------------------------------------------------------------------
-- §2  Three-Valued Partial Evaluator Wire Contract (T : Agda → Lean4 + ⊥)
------------------------------------------------------------------------

data PrismWire (A : Set) : Set where
  wireOK        : A → PrismWire A         -- Exit 0  : Translated & Verified in Lean 4
  wireSyntaxErr : String → PrismWire A    -- Exit 10 : Provable Agda lexical/layout/mixfix/scope error
  wireTypeErr   : String → PrismWire A    -- Exit 11 : Rejected by Lean 4 kernel / structural / axiom gate
  wireBot       : String → PrismWire A    -- Exit 20 : Long-tail ⊥ -> route seamlessly to legacyAgda

-- Pure routing semantics of the stream interceptor:
routeWire : ∀ {A R : Set} → (A → R) → (String → R) → R → PrismWire A → R
routeWire onOK _     _        (wireOK a)        = onOK a
routeWire _    onErr _        (wireSyntaxErr e) = onErr e
routeWire _    onErr _        (wireTypeErr e)   = onErr e
routeWire _    _     fallback (wireBot _)       = fallback

dispatchPure : ∀ {A R : Set} → BackendMode → (A → R) → (String → R) → R → PrismWire A → R
dispatchPure legacyAgda  _    _     legacy _    = legacy
dispatchPure leanPrism   onOK onErr legacy wire = routeWire onOK onErr legacy wire
dispatchPure shadowAudit _    _     legacy _    = legacy

------------------------------------------------------------------------
-- §3  Formal Conservation & Seamless-Fallback Theorems (--safe)
------------------------------------------------------------------------

-- Theorem 1: Whenever the partial evaluator emits ⊥ (`wireBot`), `leanPrism`
-- reduces judgmentally (`refl`) to the exact `legacyAgda` result.
bot-falls-back-exact :
  ∀ {A R : Set} (onOK : A → R) (onErr : String → R) (legacy : R) (reason : String) →
  dispatchPure leanPrism onOK onErr legacy (wireBot reason) ≡ legacy
bot-falls-back-exact _ _ _ _ = refl

-- Theorem 2: Switching mode to `legacyAgda` reduces judgmentally (`refl`)
-- to the original backend regardless of `PrismWire`.
legacy-mode-exact :
  ∀ {A R : Set} (onOK : A → R) (onErr : String → R) (legacy : R) (w : PrismWire A) →
  dispatchPure legacyAgda onOK onErr legacy w ≡ legacy
legacy-mode-exact _ _ _ _ = refl

-- Boolean decision view for acceptance soundness proofs:
acceptsWire : ∀ {A : Set} → Bool → PrismWire A → Bool
acceptsWire _      (wireOK _)        = true
acceptsWire _      (wireSyntaxErr _) = false
acceptsWire _      (wireTypeErr _)   = false
acceptsWire legacy (wireBot _)       = legacy

-- Soundness Specification of Partial Evaluator T:
--   1. `noFalseAccept`: If Agda rejects `x` (`legacy ≡ false`), `T(x)` is NEVER `wireOK`.
--   2. `noFalseReject`: If Agda accepts `x` (`legacy ≡ true`), `T(x)` is NEVER `wireSyntaxErr` or `wireTypeErr`.
record ConservativePrism {A : Set} (legacy : Bool) (w : PrismWire A) : Set where
  field
    noFalseAccept : legacy ≡ false → ∀ a → w ≡ wireOK a → ⊥
    noFalseReject : legacy ≡ true  → (∀ e → w ≡ wireSyntaxErr e → ⊥)
                                   × (∀ e → w ≡ wireTypeErr e   → ⊥)

-- Theorem 3 (Exact Validity Equivalence): Under `ConservativePrism`, the
-- intercepted verdict `acceptsWire legacy w` is propositionally equal (`≡`)
-- to the ground-truth Agda verdict `legacy` on ALL four `PrismWire` branches!
intercept-sound-and-complete :
  ∀ {A : Set} (legacy : Bool) (w : PrismWire A) →
  ConservativePrism legacy w →
  acceptsWire legacy w ≡ legacy
intercept-sound-and-complete true  (wireOK _)        _  = refl
intercept-sound-and-complete false (wireOK a)        cp with ConservativePrism.noFalseAccept cp refl a refl
... | ()
intercept-sound-and-complete false (wireSyntaxErr _) _  = refl
intercept-sound-and-complete true  (wireSyntaxErr e) cp with Data.Product.proj₁ (ConservativePrism.noFalseReject cp refl) e refl
... | ()
intercept-sound-and-complete false (wireTypeErr _)   _  = refl
intercept-sound-and-complete true  (wireTypeErr e)   cp with Data.Product.proj₂ (ConservativePrism.noFalseReject cp refl) e refl
... | ()
intercept-sound-and-complete legacy (wireBot _)      _  = refl

------------------------------------------------------------------------
-- §4  Unit-SCC Optic Lens Gluing (`Whole ≅ FastFocus ×_∂ SlowResidual`, --safe)
------------------------------------------------------------------------

-- Combined verification verdict of `Lens.put` Layer 1:
--   `fastOK` : Lean 4 kernel checks `⊢ F₁ : ∂_F₁` and `∂_F₁ , ∂_S ⊢ F₂`
--   `slowOK` : Agda checks parameterized residual `∂_F₁ ⊢ S : ∂_S` (`true` when `S = ∅`)
glueVerdict : (fastOK slowOK : Bool) → Bool
glueVerdict fastOK slowOK = fastOK ∧ slowOK

glueWire : ∀ {A : Set} → A → (fastOK slowOK : Bool) → PrismWire A
glueWire a true  true  = wireOK a
glueWire _ false _     = wireTypeErr "Lean4 FastFocus kernel rejected F₁/F₂"
glueWire _ true  false = wireTypeErr "Agda SlowSlice checker rejected S"

-- Theorem 4: When `SlowResidual = ∅` (`slowOK = true`), lens gluing reduces to `fastOK`.
pure-fast-zero-residual : ∀ (fastOK : Bool) → glueVerdict fastOK true ≡ fastOK
pure-fast-zero-residual true  = refl
pure-fast-zero-residual false = refl

-- Theorem 5 (Cut-Gluing Conservation): Whenever Cut-Elimination equates whole-module
-- well-typedness (`wholeOK`) with `fastOK ∧ slowOK`, `glueWire` satisfies `ConservativePrism`
-- and therefore `acceptsWire wholeOK (glueWire a fastOK slowOK) ≡ wholeOK`!
lens-cut-conservative :
  ∀ {A : Set} (a : A) (wholeOK fastOK slowOK : Bool) →
  wholeOK ≡ glueVerdict fastOK slowOK →
  ConservativePrism wholeOK (glueWire a fastOK slowOK)
lens-cut-conservative a .(true)  true  true  refl = record
  { noFalseAccept = λ ()
  ; noFalseReject = λ _ → (λ _ ()) , (λ _ ()) }
lens-cut-conservative a .(false) false slowOK refl = record
  { noFalseAccept = λ _ _ ()
  ; noFalseReject = λ () }
lens-cut-conservative a .(false) true  false refl = record
  { noFalseAccept = λ _ _ ()
  ; noFalseReject = λ () }

lens-cut-sound-and-complete :
  ∀ {A : Set} (a : A) (wholeOK fastOK slowOK : Bool) →
  wholeOK ≡ glueVerdict fastOK slowOK →
  acceptsWire wholeOK (glueWire a fastOK slowOK) ≡ wholeOK
lens-cut-sound-and-complete a wholeOK fastOK slowOK eq =
  intercept-sound-and-complete wholeOK (glueWire a fastOK slowOK)
    (lens-cut-conservative a wholeOK fastOK slowOK eq)
