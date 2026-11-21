import AgdaMirror.Utf8
import AgdaMirror.CharClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `AgdaMirror.Core`: Intensional, Axiom-Free Agda Kernel Mirror in Lean 4

Design invariants:
1. **Predicative, Intensional Identity (`AgdaId` in `Type u`)**:
   Never maps Agda's `Set` propositions into Lean's impredicative, proof-irrelevant
   `Prop` (`Sort 0`). Two open variables `p q : AgdaId x y` are *not* judgmentally
   equal in Lean's kernel, matching Agda's `_≡_` 1-to-1; yet as a 0-field single
   constructor, `AgdaId.refl` compiles to an unboxed scalar constant in LCNF.
2. **Exact Agda Definitional Reduction Order + Native Lowering**:
   `agdaAdd`, `agdaMul`, `agdaSub`, `agdaAppend`, etc. recurse on the exact same
   argument as `Agda.Builtin.*` / `agda-stdlib` during kernel `isDefEq` checking
   (so `0 + m ≡ m` is `refl` while `n + 0 ≡ n` is stuck on open `n`), and lower
   with audited pointwise correctness proofs to GMP/native operations in C codegen.
3. **Zero Dirty Axioms**:
   Verified free of `Classical.choice`, `propext`, `Quot.sound`, and `sorryAx`.
-/

namespace AgdaMirror

universe u v w z

-- §1 Unit, Empty, and Intensional Propositional Equality in `Type u`

structure AgdaTop : Type where
  tt ::

instance : Inhabited AgdaTop := ⟨.tt⟩

structure PolyTop : Type u where
  tt ::

instance : Inhabited PolyTop.{u} := ⟨.tt⟩

inductive AgdaBot : Type where

def botElim {A : Type u} (b : AgdaBot) : A :=
  nomatch b

inductive AgdaId {A : Type u} (x : A) : A → Type u where
  | refl : AgdaId x x

def AgdaNotEq {A : Type u} (x y : A) : Type u := AgdaId x y → AgdaBot

def idSym {A : Type u} {x y : A} : AgdaId x y → AgdaId y x
  | .refl => .refl

def idTrans {A : Type u} {x y z : A} : AgdaId x y → AgdaId y z → AgdaId x z
  | .refl, .refl => .refl

def idCong {A : Type u} {B : Type v} (f : A → B) {x y : A} : AgdaId x y → AgdaId (f x) (f y)
  | .refl => .refl

def idCong2 {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} :
    AgdaId x₁ x₂ → AgdaId y₁ y₂ → AgdaId (f x₁ y₁) (f x₂ y₂)
  | .refl, .refl => .refl

def idSubst {A : Type u} (P : A → Type v) {x y : A} : AgdaId x y → P x → P y
  | .refl, px => px

-- §2 Booleans & Decidability (matching `Data.Bool.Base` & `Relation.Nullary`)

def agdaNot : Bool → Bool
  | true  => false
  | false => true

@[macro_inline] def agdaAnd (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false

@[macro_inline] def agdaOr (a b : Bool) : Bool :=
  match a with
  | true  => true
  | false => b

def agdaXor : Bool → Bool → Bool
  | true,  b => agdaNot b
  | false, b => b

@[macro_inline] def agdaIte {A : Type u} (c : Bool) (t f : A) : A :=
  match c with
  | true  => t
  | false => f

def AgdaT : Bool → Type
  | true  => AgdaTop
  | false => AgdaBot

def AgdaNeg (P : Type u) : Type u := P → AgdaBot

inductive AgdaReflects (P : Type u) : Bool → Type u where
  | positive : P → AgdaReflects P true
  | negative : (P → AgdaBot) → AgdaReflects P false

structure AgdaDec (P : Type u) : Type u where
  does : Bool
  proof : AgdaReflects P does

@[match_pattern] def AgdaDec.yes {P : Type u} (p : P) : AgdaDec P := ⟨true, .positive p⟩
@[match_pattern] def AgdaDec.no {P : Type u} (np : AgdaNeg P) : AgdaDec P := ⟨false, .negative np⟩

def agdaDoes {P : Type u} (d : AgdaDec P) : Bool := d.does

def agdaIsYes {P : Type u} : AgdaDec P → Bool
  | ⟨true, _⟩ => true
  | ⟨false, _⟩ => false

def agdaIsYesDoes {P : Type u} : (d : AgdaDec P) → AgdaId (agdaIsYes d) (agdaDoes d)
  | ⟨true, _⟩ => .refl
  | ⟨false, _⟩ => .refl

def agdaDecIsTrue {P : Type u} (q : AgdaDec P) := AgdaT (agdaIsYes q)

def agdaDecIsFalse {P : Type u} (q : AgdaDec P) := AgdaT (agdaNot (agdaIsYes q))

def agdaToWitness {P : Type u} : {Q : AgdaDec P} → agdaDecIsTrue Q → P
  | .yes p, _ => p
  | .no _, h => nomatch h

def agdaToWitnessFalse {P : Type u} : {Q : AgdaDec P} → agdaDecIsFalse Q → AgdaNeg P
  | .yes _, h => nomatch h
  | .no np, _ => np

def agdaMapDec {P : Type u} {Q : Type v} (toQ : P → Q) (fromQ : Q → P) (d : AgdaDec P) : AgdaDec Q :=
  ⟨d.does, mapProof d.proof⟩
where
  mapProof {b : Bool} : AgdaReflects P b → AgdaReflects Q b
    | .positive p => .positive (toQ p)
    | .negative np => .negative (fun q => np (fromQ q))

def agdaDecTrue {P : Type u} : (d : AgdaDec P) → P → AgdaId (agdaDoes d) true
  | .yes _, _ => .refl
  | .no np, p => botElim (np p)

def agdaDecFalse {P : Type u} : (d : AgdaDec P) → AgdaNeg P → AgdaId (agdaDoes d) false
  | .yes p, np => botElim (np p)
  | .no _, _ => .refl

def agdaBoolTDec : (b : Bool) → AgdaDec (AgdaT b)
  | true  => .yes .tt
  | false => .no (fun h => h)

def agdaEqToId {A : Type u} {x y : A} (h : x = y) : AgdaId x y :=
  h ▸ .refl

theorem agdaIdToEq {A : Type u} {x y : A} : AgdaId x y → x = y
  | .refl => rfl

-- §3 Constructive Classical Logic via Double-Negation & Friedman Continuation Monads

def NotNot (A : Type u) : Type u := (A → AgdaBot) → AgdaBot

def nnPure {A : Type u} (a : A) : NotNot A :=
  fun k => k a

def nnBind {A : Type u} {B : Type v} (m : (A → AgdaBot) → AgdaBot) (f : A → (B → AgdaBot) → AgdaBot) :
    (B → AgdaBot) → AgdaBot :=
  fun kb => m (fun a => f a kb)

def FriedmanCont (R : Type w) (A : Type u) : Type (max u w) := (A → R) → R

def contPure {R : Type w} {A : Type u} (a : A) : FriedmanCont R A :=
  fun k => k a

def contBind {R : Type w} {A : Type u} {B : Type v}
    (m : FriedmanCont R A) (f : A → FriedmanCont R B) : FriedmanCont R B :=
  fun kb => m (fun a => f a kb)

def contCallCC {R : Type w} {A : Type u} {B : Type v}
    (f : (A → FriedmanCont R B) → FriedmanCont R A) : FriedmanCont R A :=
  fun k => f (fun a _ => k a) k

-- §4 Sigma, Cartesian Product (η-enabled `structure`), Sum, Maybe

structure AgdaSigma (A : Type u) (B : A → Type v) : Type (max u v) where
  mk ::
  proj₁ : A
  proj₂ : B proj₁

instance {A : Type u} {B : A → Type v} [Inhabited A] [Inhabited (B default)] :
    Inhabited (AgdaSigma A B) := ⟨⟨default, default⟩⟩

abbrev AgdaExists {A : Type u} (B : A → Type v) : Type (max u v) := AgdaSigma A B

abbrev AgdaProd (A : Type u) (B : Type v) : Type (max u v) :=
  AgdaSigma A (fun _ => B)

def prodMap1 {A : Type u} {B : Type v} {C : Type w} (f : A → C) (p : AgdaProd A B) : AgdaProd C B :=
  AgdaSigma.mk (f p.proj₁) p.proj₂

def prodMap2 {A : Type u} {B : Type v} {C : Type w} (g : B → C) (p : AgdaProd A B) : AgdaProd A C :=
  AgdaSigma.mk p.proj₁ (g p.proj₂)

-- Non-dependent η-enabled pair structure (used when dependent `Σ` is absent from bundle,
-- unlocking Lean's kernel nested-inductive compiler on `List (A × Self)` types!)
structure AgdaPair (A : Type u) (B : Type v) : Type (max u v) where
  mk ::
  proj₁ : A
  proj₂ : B

instance {A : Type u} {B : Type v} [Inhabited A] [Inhabited B] :
    Inhabited (AgdaPair A B) := ⟨⟨default, default⟩⟩

instance {A : Type u} {B : Type v} [Nonempty A] [Nonempty B] :
    Nonempty (AgdaPair A B) :=
  let ⟨a⟩ := ‹Nonempty A›
  let ⟨b⟩ := ‹Nonempty B›
  ⟨⟨a, b⟩⟩

def pairMap1 {A : Type u} {B : Type v} {C : Type w} (f : A → C) (p : AgdaPair A B) : AgdaPair C B :=
  AgdaPair.mk (f p.proj₁) p.proj₂

def pairMap2 {A : Type u} {B : Type v} {C : Type w} (g : B → C) (p : AgdaPair A B) : AgdaPair A C :=
  AgdaPair.mk p.proj₁ (g p.proj₂)

inductive AgdaSum (A : Type u) (B : Type v) : Type (max u v) where
  | inj₁ : A → AgdaSum A B
  | inj₂ : B → AgdaSum A B

def agdaSumMap {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    (f : A → C) (g : B → D) : AgdaSum A B → AgdaSum C D
  | .inj₁ a => .inj₁ (f a)
  | .inj₂ b => .inj₂ (g b)

def agdaSumMap₁ {A : Type u} {B : Type v} {C : Type w} (f : A → C) : AgdaSum A B → AgdaSum C B :=
  agdaSumMap f id

def agdaSumMap₂ {A : Type u} {B : Type v} {D : Type w} (g : B → D) : AgdaSum A B → AgdaSum A D :=
  agdaSumMap id g

inductive AgdaPermutation {A : Type u} : List A → List A → Type u where
  | refl {xs} : AgdaPermutation xs xs
  | prep {xs ys} (x : A) : AgdaPermutation xs ys → AgdaPermutation (x :: xs) (x :: ys)
  | swap {xs ys} (x y : A) : AgdaPermutation xs ys → AgdaPermutation (x :: y :: xs) (y :: x :: ys)
  | trans {xs ys zs} : AgdaPermutation xs ys → AgdaPermutation ys zs → AgdaPermutation xs zs

-- Pure constructive Excluded Middle inside NotNot (0 axioms!)
def nnLEM (A : Type u) : NotNot (AgdaSum A (AgdaNeg A)) :=
  fun k => k (.inj₂ (fun a => k (.inj₁ a)))

inductive AgdaMaybe (A : Type u) : Type u where
  | just    : A → AgdaMaybe A
  | nothing : AgdaMaybe A

instance {A : Type u} : Inhabited (AgdaMaybe A) := ⟨.nothing⟩

def maybeMap {A : Type u} {B : Type v} (f : A → B) : AgdaMaybe A → AgdaMaybe B
  | .just x  => .just (f x)
  | .nothing => .nothing

def maybeBind {A : Type u} {B : Type v} : AgdaMaybe A → (A → AgdaMaybe B) → AgdaMaybe B
  | .just x,  f => f x
  | .nothing, _ => .nothing

def maybePrime {A : Type u} {B : Type v} (f : A → B) (d : B) : AgdaMaybe A → B
  | .just x  => f x
  | .nothing => d

def fromMaybe {A : Type u} (d : A) : AgdaMaybe A → A
  | .just x  => x
  | .nothing => d

def maybeWhen {A : Type u} : Bool → A → AgdaMaybe A
  | true,  x => .just x
  | false, _ => .nothing

def maybeIsJust {A : Type u} : AgdaMaybe A → Bool
  | .just _  => true
  | .nothing => false

def maybeIsNothing {A : Type u} : AgdaMaybe A → Bool
  | .just _  => false
  | .nothing => true

def maybeZipWith {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) :
    AgdaMaybe A → AgdaMaybe B → AgdaMaybe C
  | .just a, .just b => .just (f a b)
  | .nothing, _ => .nothing
  | .just _, .nothing => .nothing

-- §5 Natural Numbers (Agda 1st-argument structural recursion + pointwise-verified native lowering)

-- Reversing the operands gives exactly Agda's defining equations on open
-- terms and lets the kernel's Nat reductions handle closed scalar arithmetic.
def agdaAdd (n m : Nat) : Nat := Nat.add m n

theorem agdaAdd_eq_add (n m : Nat) : agdaAdd n m = Nat.add n m := Nat.add_comm m n

def agdaMul (n m : Nat) : Nat := Nat.mul m n

theorem agdaMul_eq_mul (n m : Nat) : agdaMul n m = n * m := Nat.mul_comm m n

private def nativeSub : Nat → Nat → Nat := Nat.sub

@[implemented_by nativeSub]
def agdaSub : Nat → Nat → Nat
  | n, 0 => n
  | 0, Nat.succ _ => 0
  | Nat.succ n, Nat.succ m => agdaSub n m
termination_by structural _ m => m

theorem agdaSub_eq_sub : ∀ n m : Nat, agdaSub n m = Nat.sub n m
  | 0, 0 => rfl
  | Nat.succ _, 0 => rfl
  | 0, Nat.succ m => (Nat.zero_sub (Nat.succ m)).symm
  | Nat.succ n, Nat.succ m => (agdaSub_eq_sub n m).trans (Nat.succ_sub_succ n m).symm
termination_by structural n _ => n

def agdaNatEq (m n : Nat) : Bool := Nat.beq m n

-- Agda inspects the bound first. Reversing ≤ preserves that order at zero.
def agdaNatLt (m n : Nat) : Bool := !Nat.ble n m

def agdaNatLe : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ m, n => agdaNatLt m n

def agdaMin : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ _, 0 => 0
  | Nat.succ m, Nat.succ n => Nat.succ (agdaMin m n)
termination_by structural m _ => m

def agdaMax : Nat → Nat → Nat
  | 0, n => n
  | Nat.succ m, 0 => Nat.succ m
  | Nat.succ m, Nat.succ n => Nat.succ (agdaMax m n)
termination_by structural m _ => m

def agdaDiv : Nat → Nat → Nat := Nat.div
def agdaModNat : Nat → Nat → Nat := Nat.mod

def agdaPred : Nat → Nat
  | 0 => 0
  | Nat.succ n => n

def agdaNatDecEq : (m n : Nat) → AgdaDec (AgdaId m n)
  | 0, 0 => .yes .refl
  | 0, Nat.succ n => .no (fun h => False.elim ((Nat.add_one_ne_zero n) (agdaIdToEq h).symm))
  | Nat.succ m, 0 => .no (fun h => False.elim ((Nat.add_one_ne_zero m) (agdaIdToEq h)))
  | Nat.succ m, Nat.succ n =>
    match agdaNatDecEq m n with
    | .yes p => .yes (idCong Nat.succ p)
    | .no np => .no (fun h => np (idCong Nat.pred h))
termination_by structural m _ => m

def agdaNatShow (n : Nat) : String := toString n

inductive AgdaNatLeRel : Nat → Nat → Type where
  | zLeN : {n : Nat} → AgdaNatLeRel 0 n
  | sLeS : {m n : Nat} → AgdaNatLeRel m n → AgdaNatLeRel (Nat.succ m) (Nat.succ n)

def AgdaNatLtRel (m n : Nat) : Type := AgdaNatLeRel (Nat.succ m) n

def agdaNatEqbToEq : (m n : Nat) → AgdaT (agdaNatEq m n) → AgdaId m n
  | 0, 0, _ => .refl
  | 0, Nat.succ _, h => nomatch h
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ m, Nat.succ n, h => idCong Nat.succ (agdaNatEqbToEq m n h)
termination_by structural m _ _ => m

def agdaAddIdentityR : (n : Nat) → AgdaId (agdaAdd n 0) n
  | 0 => .refl
  | Nat.succ n => idCong Nat.succ (agdaAddIdentityR n)
termination_by structural n => n

def agdaAddAssoc : (m n o : Nat) → AgdaId (agdaAdd (agdaAdd m n) o) (agdaAdd m (agdaAdd n o))
  | 0, _, _ => .refl
  | Nat.succ m, n, o => idCong Nat.succ (agdaAddAssoc m n o)
termination_by structural m _ _ => m

def agdaMulIdentityL (n : Nat) : AgdaId (agdaMul 1 n) n :=
  agdaAddIdentityR n

def agdaMulIdentityR : (n : Nat) → AgdaId (agdaMul n 1) n
  | 0 => .refl
  | Nat.succ n => idCong Nat.succ (agdaMulIdentityR n)
termination_by structural n => n

def agdaNatLtbToLt : (m n : Nat) → AgdaT (agdaNatLt m n) → AgdaNatLtRel m n
  | 0, 0, h => nomatch h
  | 0, Nat.succ _, _ => .sLeS .zLeN
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ m, Nat.succ n, h => .sLeS (agdaNatLtbToLt m n h)
termination_by structural m _ _ => m

-- Eliminate the successor endpoint explicitly. Lean's generalized
-- offset-pattern matcher otherwise imports propositional extensionality.
private def extendTrans {i j k : Nat} (q : AgdaNatLeRel (j + 1) k)
    (ih : ∀ {n}, AgdaNatLeRel j n → AgdaNatLeRel i n) : AgdaNatLeRel (i + 1) k :=
  AgdaNatLeRel.casesOn (motive := fun m n _ => m = j + 1 → AgdaNatLeRel (i + 1) n) q
    (fun eq => False.elim (Nat.add_one_ne_zero j eq.symm))
    (fun p eq => .sLeS (ih (Nat.succ.inj eq ▸ p))) rfl

def agdaNatLeTrans {i j k : Nat} : AgdaNatLeRel i j → AgdaNatLeRel j k → AgdaNatLeRel i k
  | .zLeN, _ => .zLeN
  | .sLeS p, q => extendTrans q (agdaNatLeTrans p)
termination_by structural p _ => p

private theorem natLeSound {i j : Nat} : AgdaNatLeRel i j → i ≤ j
  | .zLeN => Nat.zero_le _
  | .sLeS p => Nat.succ_le_succ (natLeSound p)

def agdaNatLtIrrefl {i j : Nat} : AgdaId i j → AgdaNatLtRel i j → AgdaBot
  | .refl, p => False.elim (Nat.not_succ_le_self i (natLeSound p))

-- §6 Indexed `Fin` (exact constructor match with `Data.Fin.Base.Fin`)

inductive AgdaFin : Nat → Type where
  | zero : {n : Nat} → AgdaFin (Nat.succ n)
  | suc  : {n : Nat} → AgdaFin n → AgdaFin (Nat.succ n)

def agdaFinToNat : {n : Nat} → AgdaFin n → Nat
  | _, .zero  => 0
  | _, .suc i => Nat.succ (agdaFinToNat i)

def agdaFinOfBounded : (fuel : Nat) → (x : Nat) → {b : Nat} → AgdaFin (Nat.succ b)
  | _, _, 0 => .zero
  | 0, _, Nat.succ _ => .zero
  | _, 0, Nat.succ _ => .zero
  | Nat.succ f, Nat.succ x', Nat.succ b => .suc (agdaFinOfBounded f x' (b := b))
termination_by structural fuel _ _ => fuel

def agdaFinFromNatMod (m : Nat) (k : Nat) : AgdaFin (Nat.succ k) :=
  let v := Nat.mod m (Nat.succ k)
  agdaFinOfBounded (Nat.succ k) v (b := k)

class AgdaNonZero (d : Nat) : Prop where
  ne_zero : d ≠ 0

instance {k : Nat} : AgdaNonZero (Nat.succ k) := ⟨Nat.add_one_ne_zero k⟩
instance {n : Nat} [NeZero n] : AgdaNonZero n := ⟨NeZero.ne n⟩

def agdaNatModFin (m : Nat) : (d : Nat) → [_nz : AgdaNonZero d] → AgdaFin d
  | 0,          nz => absurd rfl nz.ne_zero
  | Nat.succ k, _  => agdaFinFromNatMod m k

-- §7 Lists (`Agda.Builtin.List.List` = Lean `List`, with 1st-arg structural ops)

@[implemented_by List.append]
def agdaAppend {A : Type u} : List A → List A → List A
  | [], ys => ys
  | x :: xs, ys => x :: agdaAppend xs ys
termination_by structural xs _ => xs

theorem agdaAppend_eq {A : Type u} : ∀ (xs ys : List A), agdaAppend xs ys = List.append xs ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (agdaAppend_eq xs ys)

def agdaMap {A : Type u} {B : Type v} (f : A → B) : List A → List B
  | [] => []
  | x :: xs => f x :: agdaMap f xs
termination_by structural xs => xs

def agdaFoldr {A : Type u} {B : Type v} (f : A → B → B) (acc : B) : List A → B
  | [] => acc
  | x :: xs => f x (agdaFoldr f acc xs)
termination_by structural xs => xs

def agdaFoldl {A : Type u} {B : Type v} (f : B → A → B) : B → List A → B
  | acc, [] => acc
  | acc, x :: xs => agdaFoldl f (f acc x) xs
termination_by structural _ xs => xs

def agdaConcatMap {A : Type u} {B : Type v} (f : A → List B) : List A → List B
  | [] => []
  | x :: xs => agdaAppend (f x) (agdaConcatMap f xs)
termination_by structural xs => xs

def agdaLength {A : Type u} : List A → Nat
  | [] => 0
  | _ :: xs => Nat.succ (agdaLength xs)
termination_by structural xs => xs

def agdaReverse {A : Type u} (xs : List A) : List A :=
  agdaFoldl (fun acc x => x :: acc) [] xs

def agdaReplicate {A : Type u} : Nat → A → List A
  | 0, _ => []
  | Nat.succ n, x => x :: agdaReplicate n x
termination_by structural n _ => n

def agdaFilterB {A : Type u} (p : A → Bool) : List A → List A
  | [] => []
  | x :: xs => agdaIte (p x) (x :: agdaFilterB p xs) (agdaFilterB p xs)
termination_by structural xs => xs

def agdaAllB {A : Type u} (p : A → Bool) : List A → Bool
  | [] => true
  | x :: xs => agdaAnd (p x) (agdaAllB p xs)
termination_by structural xs => xs

def agdaAnyB {A : Type u} (p : A → Bool) : List A → Bool
  | [] => false
  | x :: xs => agdaOr (p x) (agdaAnyB p xs)
termination_by structural xs => xs

inductive AgdaAny {A : Type u} (P : A → Type v) : List A → Type (max u v) where
  | here  : {x : A} → {xs : List A} → P x → AgdaAny P (x :: xs)
  | there : {x : A} → {xs : List A} → AgdaAny P xs → AgdaAny P (x :: xs)

inductive AgdaAll {A : Type u} (P : A → Type v) : List A → Type (max u v) where
  | nil  : AgdaAll P []
  | cons : {x : A} → {xs : List A} → P x → AgdaAll P xs → AgdaAll P (x :: xs)

def agdaTake {A : Type u} : Nat → List A → List A
  | 0, _ => []
  | Nat.succ _, [] => []
  | Nat.succ n, x :: xs => x :: agdaTake n xs
termination_by structural n _ => n

def agdaDrop {A : Type u} : Nat → List A → List A
  | 0, xs => xs
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: xs => agdaDrop n xs
termination_by structural n _ => n

def agdaApplyUpTo {A : Type u} (f : Nat → A) : Nat → List A
  | 0 => []
  | Nat.succ n => f 0 :: agdaApplyUpTo (fun k => f (Nat.succ k)) n
termination_by structural n => n

def agdaUpTo (n : Nat) : List Nat :=
  agdaApplyUpTo (fun x => x) n

def agdaZip {A : Type u} {B : Type v} : List A → List B → List (AgdaProd A B)
  | x :: xs, y :: ys => AgdaSigma.mk x y :: agdaZip xs ys
  | [], _ => []
  | _ :: _, [] => []
termination_by structural xs _ => xs

def agdaZipPair {A : Type u} {B : Type v} : List A → List B → List (AgdaPair A B)
  | x :: xs, y :: ys => AgdaPair.mk x y :: agdaZipPair xs ys
  | [], _ => []
  | _ :: _, [] => []
termination_by structural xs _ => xs

def agdaTails {A : Type u} : List A → List (List A)
  | [] => [[]]
  | x :: xs => (x :: xs) :: agdaTails xs
termination_by structural xs => xs

def agdaMapMaybe {A : Type u} {B : Type v} (p : A → AgdaMaybe B) : List A → List B
  | [] => []
  | x :: xs =>
    match p x with
    | .just y  => y :: agdaMapMaybe p xs
    | .nothing => agdaMapMaybe p xs
termination_by structural xs => xs

def agdaLookup {A : Type u} : (xs : List A) → AgdaFin (agdaLength xs) → A
  | [], i =>
    AgdaFin.casesOn (motive := fun n _ => n = 0 → A) i
      (fun eq => False.elim (Nat.add_one_ne_zero _ eq))
      (fun _ eq => False.elim (Nat.add_one_ne_zero _ eq)) rfl
  | x :: xs, i =>
    AgdaFin.casesOn (motive := fun n _ => n = agdaLength xs + 1 → A) i
      (fun _ => x) (fun j eq => agdaLookup xs (Nat.succ.inj eq ▸ j)) rfl
termination_by structural xs _ => xs

def agdaLinesByGo {A : Type u} {P : A → Type v} (dec : (x : A) → AgdaDec (P x)) :
    AgdaMaybe (List A) → List A → List (List A)
  | .nothing,  [] => []
  | .just acc, [] => [agdaReverse acc]
  | acc, c :: cs =>
    match agdaDoes (dec c) with
    | true  => agdaReverse (fromMaybe [] acc) :: agdaLinesByGo dec .nothing cs
    | false => agdaLinesByGo dec (.just (c :: fromMaybe [] acc)) cs
termination_by structural _ xs => xs

def agdaLinesBy {A : Type u} {P : A → Type v} (dec : (x : A) → AgdaDec (P x)) (xs : List A) : List (List A) :=
  agdaLinesByGo dec .nothing xs

def agdaWordsCons {A : Type u} : List A → List (List A) → List (List A)
  | [], ass => ass
  | a :: as_, ass => agdaReverse (a :: as_) :: ass

def agdaWordsByGo {A : Type u} {P : A → Type v} (dec : (x : A) → AgdaDec (P x)) :
    List A → List A → List (List A)
  | acc, [] => agdaWordsCons acc []
  | acc, c :: cs =>
    match agdaDoes (dec c) with
    | true  => agdaWordsCons acc (agdaWordsByGo dec [] cs)
    | false => agdaWordsByGo dec (c :: acc) cs
termination_by structural _ xs => xs

def agdaWordsByList {A : Type u} {P : A → Type v} (dec : (x : A) → AgdaDec (P x)) (xs : List A) : List (List A) :=
  agdaWordsByGo dec [] xs

-- §8 Characters & Strings

def agdaCharEq (c d : Char) : Bool := c == d
def agdaCharToNat (c : Char) : Nat := c.toNat
-- Agda.Utils.Char.integerToChar wraps at the Unicode limit and replaces surrogates.
def agdaCharFromNat (n : Nat) : Char :=
  let cp := n % 0x110000
  if Nat.ble 0xd800 cp && Nat.ble cp 0xdfff then '�' else Char.ofNat cp

def agdaCharToNatInjective (a b : Char) (h : AgdaId (agdaCharToNat a) (agdaCharToNat b)) : AgdaId a b :=
  have eqAB : a = b := by
    have eqNat : a.val.toNat = b.val.toNat := agdaIdToEq h
    cases a with
    | mk va ha =>
      cases b with
      | mk vb hb =>
        cases va with
        | ofBitVec ba =>
          cases vb with
          | ofBitVec bb =>
            cases BitVec.eq_of_toNat_eq eqNat
            rfl
  agdaEqToId eqAB

def agdaAppendAssoc {A : Type u} : (xs ys zs : List A) →
    AgdaId (agdaAppend (agdaAppend xs ys) zs) (agdaAppend xs (agdaAppend ys zs))
  | [], _, _ => .refl
  | x :: xs, ys, zs => idCong (List.cons x) (agdaAppendAssoc xs ys zs)
termination_by structural xs _ _ => xs

def agdaAppendIdentityL {A : Type u} (xs : List A) : AgdaId (agdaAppend [] xs) xs := .refl

def agdaAppendIdentityR {A : Type u} : (xs : List A) → AgdaId (agdaAppend xs []) xs
  | [] => .refl
  | x :: xs => idCong (List.cons x) (agdaAppendIdentityR xs)
termination_by structural xs => xs

def agdaIsSpace := CharClass.space

def agdaIsDigit (c : Char) : Bool :=
  let n := c.toNat
  48 <= n && n <= 57

def agdaIsAlpha := CharClass.alpha

def agdaIsPrint := CharClass.printable

-- Native byte arrays compare with memcmp. For kernel reduction, walk both
-- byte spines once; indexed access in Array.isEqvAux traverses their lists.
@[extern "lean_sarray_dec_eq"]
def beqByteArray (s t : @& ByteArray) : Bool :=
  @List.beq UInt8 ⟨fun a b => Nat.beq a.toNat b.toNat⟩ s.data.toList t.data.toList

-- The native primitive compares the same UTF-8 bytes in place.
@[extern "lean_string_dec_eq"]
def agdaStrEq (s t : @& String) : Bool := beqByteArray s.toByteArray t.toByteArray
def agdaToList (s : String) : List Char := Utf8.decode s.toByteArray.data.toList
-- The Agda primitive consumes every input scalar before it produces a string.
-- Without this traversal byte comparisons could inspect a prefix of an open list.
private def validScalars (cs : List Char) := cs.all fun c => decide c.val.isValidChar

private theorem validScalars_true : ∀ cs, validScalars cs = true
  | [] => rfl
  | c :: cs => by
    change (decide c.val.isValidChar && validScalars cs) = true
    rw [decide_eq_true c.valid, Bool.true_and, validScalars_true cs]

@[implemented_by String.ofList]
def agdaFromList (cs : List Char) : String := if validScalars cs then Utf8.encode cs else ""

private theorem agdaFromListEq (cs : List Char) : agdaFromList cs = String.ofList cs := by
  unfold agdaFromList
  rw [validScalars_true cs]
  exact Utf8.encodeEq cs

@[extern "lean_string_append"]
def agdaStrAppend (s : String) (t : @& String) : String :=
  -- Agda demands both strings before reducing the primitive. Inspect one byte
  -- of each spine so neither unit law becomes reflexivity on an open string.
  match s.toByteArray.data.toList, t.toByteArray.data.toList with
  | [], [] => ""
  | [], _ :: _ => t
  | _ :: _, [] => s
  | _ :: _, _ :: _ =>
    .ofByteArray (s.toByteArray ++ t.toByteArray) (Utf8.validAppend s.isValidUTF8 t.isValidUTF8)

def agdaStrToListInjective (s t : String) (h : AgdaId (agdaToList s) (agdaToList t)) : AgdaId s t :=
  agdaEqToId ((Utf8.encodeOfString s).symm.trans
    ((congrArg String.ofList (agdaIdToEq h)).trans (Utf8.encodeOfString t)))

def agdaStrFromListInjective (xs ys : List Char) (h : AgdaId (agdaFromList xs) (agdaFromList ys)) : AgdaId xs ys :=
  let eq := (agdaFromListEq xs).symm.trans ((agdaIdToEq h).trans (agdaFromListEq ys))
  agdaEqToId ((Utf8.decodeOfList xs).symm.trans ((congrArg agdaToList eq).trans (Utf8.decodeOfList ys)))

def agdaPrimShowNat (n : Nat) : String := toString n

theorem agdaToList_inj (a b : String) (h : agdaToList a = agdaToList b) : a = b :=
  (Utf8.encodeOfString a).symm.trans ((congrArg String.ofList h).trans (Utf8.encodeOfString b))

def agdaDivHelper : Nat → Nat → Nat → Nat → Nat
  | k, _, 0,     _     => k
  | k, m, n + 1, 0     => agdaDivHelper (k + 1) m n m
  | k, m, n + 1, j + 1 => agdaDivHelper k m n j
termination_by structural _ _ n _ => n

def agdaModHelper : Nat → Nat → Nat → Nat → Nat
  | k, _, 0,     _     => k
  | _, m, n + 1, 0     => agdaModHelper 0 m n m
  | k, m, n + 1, j + 1 => agdaModHelper (k + 1) m n j
termination_by structural _ _ n _ => n

def agdaSumElim {A : Type u} {B : Type v} {C : Type w}
    (f : A → C) (g : B → C) : AgdaSum A B → C
  | .inj₁ x => f x
  | .inj₂ y => g y

def agdaIntersperse (sep : String) : List String → String
  | [] => ""
  | s :: [] => s
  | s :: y :: ys => agdaStrAppend s (agdaStrAppend sep (agdaIntersperse sep (y :: ys)))
termination_by structural xs => xs

def agdaUnlines : List String → String
  | [] => ""
  | s :: [] => s
  | s :: y :: ys => agdaStrAppend s (agdaStrAppend "\n" (agdaUnlines (y :: ys)))
termination_by structural xs => xs

def agdaToLower (c : Char) : Char :=
  if 65 ≤ c.toNat && c.toNat ≤ 90 then Char.ofNat (c.toNat + 32) else c

def agdaCharDecEq (c d : Char) : AgdaDec (AgdaId c d) :=
  if h : c = d then .yes (agdaEqToId h)
  else .no (fun p => nomatch (h (agdaIdToEq p)))

def agdaStrDecEq (s t : String) : AgdaDec (AgdaId s t) :=
  if h : s = t then .yes (agdaEqToId h)
  else .no (fun p => nomatch (h (agdaIdToEq p)))

def agdaCharEqDecides (c d : Char) := agdaIsYes (agdaCharDecEq c d)
def agdaStrEqDecides (s t : String) := agdaIsYes (agdaStrDecEq s t)

def agdaStrConcat : List String → String
  | [] => ""
  | s :: ss => agdaStrAppend s (agdaStrConcat ss)
termination_by structural ss => ss

def agdaWordsBy {P : Char → Type u} (dec : (c : Char) → AgdaDec (P c)) (s : String) : List String :=
  agdaMap agdaFromList (agdaWordsByList dec (agdaToList s))

def agdaWords (s : String) : List String :=
  agdaWordsBy (fun c => agdaBoolTDec (agdaIsSpace c)) s

def agdaLinesByStr {P : Char → Type u} (dec : (c : Char) → AgdaDec (P c)) (s : String) : List String :=
  agdaMap agdaFromList (agdaLinesBy dec (agdaToList s))

def agdaLines (s : String) : List String :=
  agdaLinesByStr (agdaCharDecEq '\n') s

-- §9 Function Combinators (`Function.Base`)

def agdaIdFn {A : Type u} (x : A) : A := x
def agdaConst {A : Type u} {B : Type v} (x : A) (_ : B) : A := x
def agdaComp {A : Type u} {B : Type v} {C : Type w} (g : B → C) (f : A → B) (x : A) : C := g (f x)
def agdaApp {A : Type u} {B : Type v} (f : A → B) (x : A) : B := f x

-- §10 Trusted IO Entrypoint Surface (for `build-exe` `Main` modules)

abbrev AgdaIO (A : Type) : Type := IO A

def agdaIOPure {A : Type} (a : A) : AgdaIO A := pure a
def agdaIOBind {A B : Type} (m : AgdaIO A) (k : A → AgdaIO B) : AgdaIO B := m >>= k
def agdaIOSeq {A B : Type} (m : AgdaIO A) (n : AgdaIO B) : AgdaIO B := m *> n
def agdaPutStrLn (s : String) : AgdaIO PolyTop := do
  (← IO.getStdout).putStr (agdaStrAppend s "\n")
  pure PolyTop.tt
def agdaPutStrLn0 (s : String) : AgdaIO AgdaTop := do
  (← IO.getStdout).putStr (agdaStrAppend s "\n")
  pure AgdaTop.tt
def agdaReadFiniteFile (p : String) : AgdaIO String := IO.FS.readFile p
def agdaWriteFile (p : String) (s : String) : AgdaIO AgdaTop := do
  IO.FS.writeFile p s
  pure AgdaTop.tt

initialize _agdaArgsRef : IO.Ref (Option (List String)) ← IO.mkRef none

@[extern "ct_lean_prog_name"]
opaque ctLeanProgName : IO String

@[extern "ct_lean_argc"]
opaque ctLeanArgc : IO Nat

@[extern "ct_lean_arg_at"]
opaque ctLeanArgAt (idx : UInt32) : IO String

@[extern "ct_lean_is_tty"]
opaque ctLeanIsTTY (fd : UInt32) : IO Bool

@[extern "ct_lean_tcp_exchange"]
opaque ctLeanTcpExchange (host : @& String) (port : UInt32) (req : @& ByteArray)
    (halfClose : UInt8) (timeoutMs : UInt32) : IO (Except String ByteArray)

@[extern "ct_lean_tls_exchange"]
opaque ctLeanTlsExchange (host : @& String) (port : UInt32) (sni : @& String)
    (insecure : UInt8) (tunnelReq : @& ByteArray) (req : @& ByteArray)
    (timeoutMs : UInt32) : IO (Except String ByteArray)

private def collectCArgs (n : Nat) : IO (List String) := do
  let mut acc : List String := []
  for i in [0:n] do
    let a ← ctLeanArgAt (UInt32.ofNat i)
    acc := acc ++ [a]
  pure acc

def agdaGetArgs : AgdaIO (List String) := do
  match (← _agdaArgsRef.get) with
  | some xs => pure xs
  | none    => collectCArgs (← ctLeanArgc)

def agdaGetProgName : AgdaIO String :=
  ctLeanProgName

def agdaLookupEnv (k : String) : AgdaIO (AgdaMaybe String) := do
  match (← IO.getEnv k) with
  | some v => pure (.just v)
  | none   => pure .nothing

def agdaLockUTF8Encoding : AgdaIO AgdaTop :=
  pure AgdaTop.tt

def agdaIsTTYStdin : AgdaIO Bool := ctLeanIsTTY 0
def agdaIsTTYStdout : AgdaIO Bool := ctLeanIsTTY 1
def agdaIsTTYStderr : AgdaIO Bool := ctLeanIsTTY 2

private def byteArrayToAgdaBytes (ba : ByteArray) : List (AgdaFin 256) :=
  ba.data.toList.map (fun b => agdaFinFromNatMod b.toNat 255)

private def agdaBytesToByteArray (bs : List (AgdaFin 256)) : ByteArray :=
  ByteArray.mk ((bs.map (fun b => UInt8.ofNat (agdaFinToNat b))).toArray)

def agdaPutStr (s : String) : AgdaIO PolyTop := do
  IO.print s
  (← IO.getStdout).flush
  pure PolyTop.tt

def agdaPutStr0 (s : String) : AgdaIO AgdaTop := do
  IO.print s
  (← IO.getStdout).flush
  pure AgdaTop.tt

def agdaWriteStdout (s : String) : AgdaIO AgdaTop :=
  agdaPutStr0 s

def agdaWriteStdoutLn (s : String) : AgdaIO AgdaTop :=
  agdaPutStrLn0 s

def agdaWriteStdoutBytes (bs : List (AgdaFin 256)) : AgdaIO AgdaTop := do
  let h ← IO.getStdout
  h.write (agdaBytesToByteArray bs)
  h.flush
  pure AgdaTop.tt

def agdaWriteStderr (s : String) : AgdaIO AgdaTop := do
  let h ← IO.getStderr
  h.putStr s
  h.flush
  pure AgdaTop.tt

def agdaWriteStderrLn (s : String) : AgdaIO AgdaTop := do
  IO.eprintln s
  (← IO.getStderr).flush
  pure AgdaTop.tt

def agdaWriteStderrBytes (bs : List (AgdaFin 256)) : AgdaIO AgdaTop := do
  let h ← IO.getStderr
  h.write (agdaBytesToByteArray bs)
  h.flush
  pure AgdaTop.tt

private partial def readStreamAll (h : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← h.read 65536
  if chunk.isEmpty then pure acc else readStreamAll h (acc ++ chunk)

def agdaReadStdin : AgdaIO String := do
  let h ← IO.getStdin
  let bs ← readStreamAll h ByteArray.empty
  pure (String.fromUTF8! bs)

def agdaReadStdinBytes : AgdaIO (List (AgdaFin 256)) := do
  let h ← IO.getStdin
  let bs ← readStreamAll h ByteArray.empty
  pure (byteArrayToAgdaBytes bs)

def agdaReadStdinEither : AgdaIO (AgdaSum String String) := do
  try
    let h ← IO.getStdin
    let bs ← readStreamAll h ByteArray.empty
    match String.fromUTF8? bs with
    | some s => pure (.inj₂ s)
    | none   => pure (.inj₁ "invalid UTF-8 on stdin")
  catch e =>
    pure (.inj₁ (toString e))

def agdaReadFileEither (p : String) : AgdaIO (AgdaSum String String) := do
  try
    let bs ← IO.FS.readBinFile p
    match String.fromUTF8? bs with
    | some s => pure (.inj₂ s)
    | none   => pure (.inj₁ "invalid UTF-8 in file")
  catch e =>
    pure (.inj₁ (toString e))

def agdaReadFileBytesEither (p : String) : AgdaIO (AgdaSum String (List (AgdaFin 256))) := do
  try
    let bs ← IO.FS.readBinFile p
    pure (.inj₂ (byteArrayToAgdaBytes bs))
  catch e =>
    pure (.inj₁ (toString e))

def agdaWriteFileEither (p : String) (s : String) : AgdaIO (AgdaSum String AgdaTop) := do
  try
    IO.FS.writeFile p s
    pure (.inj₂ AgdaTop.tt)
  catch e =>
    pure (.inj₁ (toString e))

def agdaWriteFileBytesEither (p : String) (bs : List (AgdaFin 256)) : AgdaIO (AgdaSum String AgdaTop) := do
  try
    IO.FS.writeBinFile p (agdaBytesToByteArray bs)
    pure (.inj₂ AgdaTop.tt)
  catch e =>
    pure (.inj₁ (toString e))

def agdaTcpExchange (host : String) (port : Nat) (req : List (AgdaFin 256))
    (halfClose : Bool) (timeoutMs : Nat) :
    AgdaIO (AgdaSum String (List (AgdaFin 256))) := do
  let r ← ctLeanTcpExchange
    host
    (UInt32.ofNat (port % 65536))
    (agdaBytesToByteArray req)
    (if halfClose then 1 else 0)
    (UInt32.ofNat (if timeoutMs > 3600000 then 3600000 else timeoutMs))
  match r with
  | .error msg => pure (.inj₁ msg)
  | .ok ba     => pure (.inj₂ (byteArrayToAgdaBytes ba))

def agdaTlsExchange (host : String) (port : Nat) (sni : String) (insecure : Bool)
    (tunnelReq : List (AgdaFin 256)) (req : List (AgdaFin 256)) (timeoutMs : Nat) :
    AgdaIO (AgdaSum String (List (AgdaFin 256))) := do
  let r ← ctLeanTlsExchange
    host
    (UInt32.ofNat (port % 65536))
    sni
    (if insecure then 1 else 0)
    (agdaBytesToByteArray tunnelReq)
    (agdaBytesToByteArray req)
    (UInt32.ofNat (if timeoutMs > 3600000 then 3600000 else timeoutMs))
  match r with
  | .error msg => pure (.inj₁ msg)
  | .ok ba     => pure (.inj₂ (byteArrayToAgdaBytes ba))

def agdaExitWithCode (n : Nat) : AgdaIO AgdaTop := do
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit (UInt8.ofNat (n % 256))

def agdaExitFailure0 : AgdaIO AgdaTop := do
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit 1

def agdaRunPrismCatSelfChecks : AgdaIO AgdaTop := do
  let some binDir := (← IO.appPath).parent | throw <| IO.userError "missing harness executable directory"
  let checked ← IO.Process.output {cmd := (binDir / "agda2lean").toString, args := #["cat-self-check"]}
  unless checked.exitCode == 0 do throw <| IO.userError (checked.stdout ++ checked.stderr)
  pure AgdaTop.tt

def agdaEnableLineBuffering : AgdaIO AgdaTop :=
  pure AgdaTop.tt

-- §9 Inductive Natural & Integer Ordering and `Data.Integer.Base` Arithmetic

-- Invert the ordering through its two-index recursor. A dependent match on
-- Nat.succ endpoints would bring the offset matcher's propext into the kernel.
private def lowerLe {m n : Nat} (h : AgdaNatLeRel (m+1) (n+1)) : AgdaNatLeRel m n :=
  AgdaNatLeRel.casesOn (motive := fun a b _ => AgdaNatLeRel a.pred b.pred) h
    .zLeN (fun p => p)

def agdaNatLeDec : (m n : Nat) → AgdaDec (AgdaNatLeRel m n)
  | 0,          _          => .yes .zLeN
  | Nat.succ m, 0          => .no (fun h => False.elim (Nat.not_succ_le_zero m (natLeSound h)))
  | Nat.succ m, Nat.succ n =>
      match agdaNatLeDec m n with
      | .yes p => .yes (.sLeS p)
      | .no np => .no (fun h => np (lowerLe h))
termination_by structural m _ => m

private def agdaNatLeRefl : (x : Nat) → AgdaNatLeRel x x
  | 0          => .zLeN
  | Nat.succ x => .sLeS (agdaNatLeRefl x)

private def agdaNatLeStepR {m k : Nat} : AgdaNatLeRel m k → AgdaNatLeRel m (Nat.succ k)
  | .zLeN => .zLeN
  | .sLeS h => .sLeS (agdaNatLeStepR h)
termination_by structural h => h

def agdaNatMLeNM (m : Nat) : (n : Nat) → AgdaNatLeRel m (agdaAdd n m)
  | 0          => agdaNatLeRefl m
  | Nat.succ n => agdaNatLeStepR (agdaNatMLeNM m n)

def agdaIntZero : Int := Int.ofNat 0
def agdaIntNegOne : Int := Int.negSucc 0
def agdaIntOne : Int := Int.ofNat 1

def agdaIntAbs : Int → Nat
  | Int.ofNat n   => n
  | Int.negSucc n => Nat.succ n

inductive AgdaIntLeRel : Int → Int → Type where
  | negLeNeg : {m n : Nat} → AgdaNatLeRel n m → AgdaIntLeRel (Int.negSucc m) (Int.negSucc n)
  | negLePos : {m n : Nat} → AgdaIntLeRel (Int.negSucc m) (Int.ofNat n)
  | posLePos : {m n : Nat} → AgdaNatLeRel m n → AgdaIntLeRel (Int.ofNat m) (Int.ofNat n)

def agdaIntLeB : Int → Int → Bool
  | Int.negSucc m, Int.negSucc n => agdaNatLe n m
  | Int.ofNat _,   Int.negSucc _ => false
  | Int.negSucc _, Int.ofNat _   => true
  | Int.ofNat m,   Int.ofNat n   => agdaNatLe m n

def agdaIntLeDec : (a b : Int) → AgdaDec (AgdaIntLeRel a b)
  | Int.negSucc m, Int.negSucc n =>
      match agdaNatLeDec n m with
      | .yes p => .yes (.negLeNeg p)
      | .no np => .no (fun h => match h with | .negLeNeg p => np p)
  | Int.negSucc _, Int.ofNat _ => .yes .negLePos
  | Int.ofNat _,   Int.negSucc _ => .no (fun h => nomatch h)
  | Int.ofNat m,   Int.ofNat n =>
      match agdaNatLeDec m n with
      | .yes p => .yes (.posLePos p)
      | .no np => .no (fun h => match h with | .posLePos p => np p)

def agdaIntNeg : Int → Int
  | Int.negSucc n          => Int.ofNat (Nat.succ n)
  | Int.ofNat 0            => Int.ofNat 0
  | Int.ofNat (Nat.succ n) => Int.negSucc n

def agdaNatSubInt (m n : Nat) : Int :=
  match agdaNatLt m n with
  | true  => agdaIntNeg (Int.ofNat (agdaSub n m))
  | false => Int.ofNat (agdaSub m n)

def agdaIntAdd : Int → Int → Int
  | Int.negSucc m, Int.negSucc n => Int.negSucc (Nat.succ (agdaAdd m n))
  | Int.negSucc m, Int.ofNat n   => agdaNatSubInt n (Nat.succ m)
  | Int.ofNat m,   Int.negSucc n => agdaNatSubInt m (Nat.succ n)
  | Int.ofNat m,   Int.ofNat n   => Int.ofNat (agdaAdd m n)

def agdaIntSub (i j : Int) : Int :=
  agdaIntAdd i (agdaIntNeg j)

def agdaIntSuc (i : Int) : Int :=
  agdaIntAdd agdaIntOne i

def agdaIntPred (i : Int) : Int :=
  agdaIntAdd agdaIntNegOne i

def agdaSignApply : Bool → Nat → Int
  | _,     0          => Int.ofNat 0
  | false, n          => Int.ofNat n
  | true,  Nat.succ n => Int.negSucc n

def agdaIntIsNeg : Int → Bool
  | Int.ofNat _   => false
  | Int.negSucc _ => true

def agdaIntMul (i j : Int) : Int :=
  let neg := agdaXor (agdaIntIsNeg i) (agdaIntIsNeg j)
  agdaSignApply neg (agdaMul (agdaIntAbs i) (agdaIntAbs j))

def agdaIntMax : Int → Int → Int
  | Int.negSucc m, Int.negSucc n => Int.negSucc (agdaMin m n)
  | Int.negSucc _, Int.ofNat n   => Int.ofNat n
  | Int.ofNat m,   Int.negSucc _ => Int.ofNat m
  | Int.ofNat m,   Int.ofNat n   => Int.ofNat (agdaMax m n)

def agdaIntMin : Int → Int → Int
  | Int.negSucc m, Int.negSucc n => Int.negSucc (agdaMax m n)
  | Int.negSucc m, Int.ofNat _   => Int.negSucc m
  | Int.ofNat _,   Int.negSucc n => Int.negSucc n
  | Int.ofNat m,   Int.ofNat n   => Int.ofNat (agdaMin m n)

def agdaIntDecEq : (a b : Int) → AgdaDec (AgdaId a b)
  | Int.ofNat m, Int.ofNat n =>
      match agdaNatDecEq m n with
      | .yes p => .yes (idCong Int.ofNat p)
      | .no np => .no (fun h => match h with | .refl => np .refl)
  | Int.negSucc m, Int.negSucc n =>
      match agdaNatDecEq m n with
      | .yes p => .yes (idCong Int.negSucc p)
      | .no np => .no (fun h => match h with | .refl => np .refl)
  | Int.ofNat _, Int.negSucc _ => .no (fun h => nomatch h)
  | Int.negSucc _, Int.ofNat _ => .no (fun h => nomatch h)

end AgdaMirror
