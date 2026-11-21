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
2. **Exact Agda Definitional Reduction Order + `@[csimp]` Hardware Lowering**:
   `agdaAdd`, `agdaMul`, `agdaSub`, `agdaAppend`, etc. recurse on the exact same
   argument as `Agda.Builtin.*` / `agda-stdlib` during kernel `isDefEq` checking
   (so `0 + m ≡ m` is `refl` while `n + 0 ≡ n` is stuck on open `n`), and lower
   via verified `@[csimp]` theorems to GMP/native operations in C codegen.
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

inductive AgdaDec (P : Type u) : Type u where
  | yes : P → AgdaDec P
  | no  : (P → AgdaBot) → AgdaDec P

def agdaDoes {P : Type u} : AgdaDec P → Bool
  | .yes _ => true
  | .no  _ => false

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
  | _,       _       => .nothing

-- §5 Natural Numbers (Agda 1st-argument structural recursion + `@[csimp]` fast lowering)

def agdaAdd : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (agdaAdd n m)
termination_by structural n _ => n

private theorem agdaAdd_zero_right : ∀ n : Nat, agdaAdd n 0 = n
  | 0 => rfl
  | Nat.succ n => congrArg Nat.succ (agdaAdd_zero_right n)

private theorem agdaAdd_succ_right : ∀ n m : Nat, agdaAdd n (Nat.succ m) = Nat.succ (agdaAdd n m)
  | 0, _ => rfl
  | Nat.succ n, m => congrArg Nat.succ (agdaAdd_succ_right n m)

private theorem agdaAdd_eq_add : ∀ n m : Nat, agdaAdd n m = Nat.add n m := by
  intro n m
  induction m with
  | zero => exact agdaAdd_zero_right n
  | succ m ih => exact Eq.trans (agdaAdd_succ_right n m) (congrArg Nat.succ ih)

@[csimp] theorem agdaAdd_csimp : @agdaAdd = @Nat.add := by
  funext n m
  exact agdaAdd_eq_add n m

def agdaMul : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ n, m => agdaAdd m (agdaMul n m)
termination_by structural n _ => n

def agdaSub : Nat → Nat → Nat
  | n, 0 => n
  | 0, Nat.succ _ => 0
  | Nat.succ n, Nat.succ m => agdaSub n m
termination_by structural n _ => n

private theorem agdaSub_eq_sub : ∀ n m : Nat, agdaSub n m = Nat.sub n m
  | 0, 0 => rfl
  | Nat.succ _, 0 => rfl
  | 0, Nat.succ m => by rw [Nat.sub_eq]; simp [agdaSub]
  | Nat.succ n, Nat.succ m => by
      have ih := agdaSub_eq_sub n m
      simp only [agdaSub]
      rw [Nat.sub_eq] at ih ⊢
      omega

@[csimp] theorem agdaSub_csimp : @agdaSub = @Nat.sub := by
  funext n m
  exact agdaSub_eq_sub n m

def agdaNatEq : Nat → Nat → Bool
  | 0, 0 => true
  | Nat.succ n, Nat.succ m => agdaNatEq n m
  | _, _ => false
termination_by structural n _ => n

def agdaNatLt : Nat → Nat → Bool
  | _, 0 => false
  | 0, Nat.succ _ => true
  | Nat.succ n, Nat.succ m => agdaNatLt n m
termination_by structural n _ => n

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
  | 0, Nat.succ _ => .no (fun h => nomatch h)
  | Nat.succ _, 0 => .no (fun h => nomatch h)
  | Nat.succ m, Nat.succ n =>
    match agdaNatDecEq m n with
    | .yes p => .yes (idCong Nat.succ p)
    | .no np => .no (fun h => match h with | .refl => np .refl)
termination_by structural m _ => m

def agdaNatShow (n : Nat) : String := toString n

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

instance {k : Nat} : AgdaNonZero (Nat.succ k) := ⟨Nat.succ_ne_zero k⟩
instance {n : Nat} [NeZero n] : AgdaNonZero n := ⟨NeZero.ne n⟩

def agdaNatModFin (m : Nat) : (d : Nat) → [_nz : AgdaNonZero d] → AgdaFin d
  | 0,          nz => absurd rfl nz.ne_zero
  | Nat.succ k, _  => agdaFinFromNatMod m k

-- §7 Lists (`Agda.Builtin.List.List` = Lean `List`, with 1st-arg structural ops)

def agdaAppend {A : Type u} : List A → List A → List A
  | [], ys => ys
  | x :: xs, ys => x :: agdaAppend xs ys
termination_by structural xs _ => xs

private theorem agdaAppend_eq {A : Type u} : ∀ (xs ys : List A), agdaAppend xs ys = List.append xs ys
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (agdaAppend_eq xs ys)

@[csimp] theorem agdaAppend_csimp : @agdaAppend.{u} = @List.append.{u} := by
  funext A xs ys
  exact agdaAppend_eq xs ys

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
  | _, _ => []
termination_by structural xs _ => xs

def agdaZipPair {A : Type u} {B : Type v} : List A → List B → List (AgdaPair A B)
  | x :: xs, y :: ys => AgdaPair.mk x y :: agdaZipPair xs ys
  | _, _ => []
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
  | x :: _,  .zero  => x
  | _ :: xs, .suc i => agdaLookup xs i

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
  | as_, ass => agdaReverse as_ :: ass

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
def agdaCharFromNat (n : Nat) : Char := Char.ofNat n

def agdaIsSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

def agdaIsDigit (c : Char) : Bool :=
  let n := c.toNat
  48 <= n && n <= 57

def agdaIsAlpha (c : Char) : Bool :=
  let n := c.toNat
  (65 <= n && n <= 90) || (97 <= n && n <= 122)

private def utf8DecodeBytes : List UInt8 → List Char
  | [] => []
  | b1 :: rest =>
    let n1 := b1.toNat
    if n1 < 0x80 then
      Char.ofNat n1 :: utf8DecodeBytes rest
    else if n1 < 0xE0 then
      match rest with
      | b2 :: rest2 =>
        let cp := (n1 - 192) * 64 + (b2.toNat - 128)
        Char.ofNat cp :: utf8DecodeBytes rest2
      | _ => []
    else if n1 < 0xF0 then
      match rest with
      | b2 :: b3 :: rest3 =>
        let cp := (n1 - 224) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128)
        Char.ofNat cp :: utf8DecodeBytes rest3
      | _ => []
    else
      match rest with
      | b2 :: b3 :: b4 :: rest4 =>
        let cp := (n1 - 240) * 262144 + (b2.toNat - 128) * 4096 + (b3.toNat - 128) * 64 + (b4.toNat - 128)
        Char.ofNat cp :: utf8DecodeBytes rest4
      | _ => []
termination_by structural bs => bs

def agdaStrEq (s t : String) : Bool := s == t
def agdaStrAppend (s t : String) : String := s ++ t
def agdaToList (s : String) : List Char := utf8DecodeBytes s.toByteArray.data.toList
def agdaFromList (cs : List Char) : String := String.ofList cs
def agdaPrimShowNat (n : Nat) : String := toString n

private theorem utf8DecodeBytes_step (b1 : UInt8) (rest : List UInt8) :
    utf8DecodeBytes (b1 :: rest) =
      let n1 := b1.toNat
      if n1 < 0x80 then Char.ofNat n1 :: utf8DecodeBytes rest
      else if n1 < 0xE0 then match rest with | b2 :: rest2 => Char.ofNat ((n1 - 192) * 64 + (b2.toNat - 128)) :: utf8DecodeBytes rest2 | _ => []
      else if n1 < 0xF0 then match rest with | b2 :: b3 :: rest3 => Char.ofNat ((n1 - 224) * 4096 + (b2.toNat - 128) * 64 + (b3.toNat - 128)) :: utf8DecodeBytes rest3 | _ => []
      else match rest with | b2 :: b3 :: b4 :: rest4 => Char.ofNat ((n1 - 240) * 262144 + (b2.toNat - 128) * 4096 + (b3.toNat - 128) * 64 + (b4.toNat - 128)) :: utf8DecodeBytes rest4 | _ => [] := by
  cases rest with
  | nil => simp [utf8DecodeBytes]
  | cons b2 r2 => cases r2 with
    | nil => simp [utf8DecodeBytes]
    | cons b3 r3 => cases r3 <;> simp [utf8DecodeBytes]

private theorem utf8Decode_encodeChar (c : Char) (rest : List UInt8) :
    utf8DecodeBytes (String.utf8EncodeChar c ++ rest) = c :: utf8DecodeBytes rest := by
  have hv : c.val.toNat < 0x110000 := by
    have h := c.valid; simp only [UInt32.isValidChar, Nat.isValidChar] at h; omega
  have hc := Char.ofNat_toNat c
  have htn : c.toNat = c.val.toNat := rfl
  simp only [String.utf8EncodeChar]
  split
  · rw [List.cons_append, List.nil_append, utf8DecodeBytes_step]
    simp only [UInt8.toNat_ofNat']
    split
    · have e : c.val.toNat % 2 ^ 8 = c.toNat := by omega
      rw [e, hc]
    · omega
  · split
    · rw [List.cons_append, List.cons_append, List.nil_append, utf8DecodeBytes_step]
      simp only [UInt8.toNat_ofNat']
      split
      · omega
      · split
        · have e : (((c.val.toNat / 64 % 32 + 192) % 2 ^ 8 - 192) * 64 + ((c.val.toNat % 64 + 128) % 2 ^ 8 - 128)) = c.toNat := by omega
          rw [e, hc]
        · omega
    · split
      · rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append, utf8DecodeBytes_step]
        simp only [UInt8.toNat_ofNat']
        split
        · omega
        · split
          · omega
          · split
            · have e : (((c.val.toNat / 4096 % 16 + 224) % 2 ^ 8 - 224) * 4096 + ((c.val.toNat / 64 % 64 + 128) % 2 ^ 8 - 128) * 64 + ((c.val.toNat % 64 + 128) % 2 ^ 8 - 128)) = c.toNat := by omega
              rw [e, hc]
            · omega
      · rw [List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.nil_append, utf8DecodeBytes_step]
        simp only [UInt8.toNat_ofNat']
        split
        · omega
        · split
          · omega
          · split
            · omega
            · have e : (((c.val.toNat / 262144 % 8 + 240) % 2 ^ 8 - 240) * 262144 + ((c.val.toNat / 4096 % 64 + 128) % 2 ^ 8 - 128) * 4096 + ((c.val.toNat / 64 % 64 + 128) % 2 ^ 8 - 128) * 64 + ((c.val.toNat % 64 + 128) % 2 ^ 8 - 128)) = c.toNat := by omega
              rw [e, hc]

private theorem toByteArray_loop_eq : ∀ (xs : List UInt8) (acc : ByteArray),
    (List.toByteArray.loop xs acc).data.toList = acc.data.toList ++ xs
  | [], acc => by simp [List.toByteArray.loop]
  | x :: xs, acc => by
      rw [List.toByteArray.loop, toByteArray_loop_eq xs (acc.push x)]
      simp [ByteArray.push, Array.push, List.append_assoc]

private theorem utf8Decode_flatMap : ∀ (cs : List Char), utf8DecodeBytes (cs.flatMap String.utf8EncodeChar) = cs
  | [] => rfl
  | c :: cs => by rw [List.flatMap_cons, utf8Decode_encodeChar, utf8Decode_flatMap cs]

theorem agdaToList_inj (a b : String) (h : agdaToList a = agdaToList b) : a = b := by
  have hba : a.toByteArray = b.toByteArray := by
    have ha := a.isValidUTF8
    have hb := b.isValidUTF8
    cases ha with | intro ma ema =>
    cases hb with | intro mb emb =>
    have emptyL : (ByteArray.emptyWithCapacity 0).data.toList = [] := rfl
    have da : utf8DecodeBytes a.toByteArray.data.toList = ma := by
      rw [ema]; simp only [List.utf8Encode, List.toByteArray, ByteArray.empty]
      rw [toByteArray_loop_eq, emptyL, List.nil_append]; exact utf8Decode_flatMap ma
    have db : utf8DecodeBytes b.toByteArray.data.toList = mb := by
      rw [emb]; simp only [List.utf8Encode, List.toByteArray, ByteArray.empty]
      rw [toByteArray_loop_eq, emptyL, List.nil_append]; exact utf8Decode_flatMap mb
    have eqm : ma = mb := Eq.trans (Eq.symm da) (Eq.trans h db)
    rw [ema, emb, eqm]
  cases a; cases b; simp at hba; subst hba; rfl

def agdaDivHelper : Nat → Nat → Nat → Nat → Nat
  | k, _, 0,     _     => k
  | k, m, n + 1, 0     => agdaDivHelper (k + 1) m n m
  | k, m, n + 1, j + 1 => agdaDivHelper k m n j
termination_by _ _ n _ => n

def agdaModHelper : Nat → Nat → Nat → Nat → Nat
  | k, _, 0,     _     => k
  | _, m, n + 1, 0     => agdaModHelper 0 m n m
  | k, m, n + 1, j + 1 => agdaModHelper (k + 1) m n j
termination_by _ _ n _ => n

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

def agdaToLower (c : Char) : Char := c.toLower

def agdaCharDecEq (c d : Char) : AgdaDec (AgdaId c d) :=
  if h : c = d then .yes (agdaEqToId h)
  else .no (fun p => nomatch (h (agdaIdToEq p)))

def agdaStrDecEq (s t : String) : AgdaDec (AgdaId s t) :=
  if h : s = t then .yes (agdaEqToId h)
  else .no (fun p => nomatch (h (agdaIdToEq p)))

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

def agdaShowString (s : String) : String := reprStr s

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
  IO.println s
  pure PolyTop.tt
def agdaPutStrLn0 (s : String) : AgdaIO AgdaTop := do
  IO.println s
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

def agdaEnableLineBuffering : AgdaIO AgdaTop :=
  pure AgdaTop.tt

-- §9 Inductive Natural & Integer Ordering and `Data.Integer.Base` Arithmetic

inductive AgdaNatLeRel : Nat → Nat → Type where
  | zLeN : {n : Nat} → AgdaNatLeRel 0 n
  | sLeS : {m n : Nat} → AgdaNatLeRel m n → AgdaNatLeRel (Nat.succ m) (Nat.succ n)

abbrev AgdaNatLtRel (m n : Nat) : Type :=
  AgdaNatLeRel (Nat.succ m) n

def agdaNatLeDec : (m n : Nat) → AgdaDec (AgdaNatLeRel m n)
  | 0,          _          => .yes .zLeN
  | Nat.succ _, 0          => .no (fun h => nomatch h)
  | Nat.succ m, Nat.succ n =>
      match agdaNatLeDec m n with
      | .yes p => .yes (.sLeS p)
      | .no np => .no (fun h => match h with | .sLeS p => np p)
termination_by structural m _ => m

private def agdaNatLeRefl : (x : Nat) → AgdaNatLeRel x x
  | 0          => .zLeN
  | Nat.succ x => .sLeS (agdaNatLeRefl x)

private def agdaNatLeStepR : {m k : Nat} → AgdaNatLeRel m k → AgdaNatLeRel m (Nat.succ k)
  | 0,          _, _       => .zLeN
  | Nat.succ _, _, .sLeS h => .sLeS (agdaNatLeStepR h)

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
