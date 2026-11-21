{-# OPTIONS --safe #-}
module Context.TranscodeCategory where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
import Data.Nat.Properties as Nat
import Data.List.Properties as Lists
open import Data.List.Base using (List; []; _∷_; [_]; _++_; map; length; filter)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-filter⁺; ∈-filter⁻)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ; ∃; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Binary.Definitions using (Decidable)

data BasePt : Set where ⋆ : BasePt

data BasePolyOp : List BasePt → BasePt → Set where
  idOp splitOp projectShellOp stepOp : BasePolyOp [ ⋆ ] ⋆
  gluePushoutOp : BasePolyOp (⋆ ∷ ⋆ ∷ ⋆ ∷ []) ⋆
  consOp : BasePolyOp (⋆ ∷ ⋆ ∷ []) ⋆
  compOp : ∀ {xs ys zs} → BasePolyOp xs ⋆ → BasePolyOp (ys ++ ⋆ ∷ zs) ⋆ →
           BasePolyOp (ys ++ xs ++ zs) ⋆

data DeclSort : Set where
  baseTypeDecl pureSigHelperDecl sweetBodyDecl exoBodyDecl boundaryHoleDecl : DeclSort

data SliceColor : Set where SharedBase SweetMod ExoMod MixMod : SliceColor

private variable S A B : Set

-- A hole carries only its type. Its empty body dependency list is definitional.
Body : Set → DeclSort → Set
Body S boundaryHoleDecl = ⊤
Body S baseTypeDecl = List S
Body S pureSigHelperDecl = List S
Body S sweetBodyDecl = List S
Body S exoBodyDecl = List S

record DeclEntry (Sym : Set) : Set where
  constructor entry
  field
    entrySym : Sym
    entrySort : DeclSort
    sigDeps : List Sym
    contents : Body Sym entrySort
open DeclEntry public

decl : S → DeclSort → List S → List S → DeclEntry S
decl s baseTypeDecl a b = entry s baseTypeDecl a b
decl s pureSigHelperDecl a b = entry s pureSigHelperDecl a b
decl s sweetBodyDecl a b = entry s sweetBodyDecl a b
decl s exoBodyDecl a b = entry s exoBodyDecl a b
decl s boundaryHoleDecl a b = entry s boundaryHoleDecl a tt

bodyDeps : DeclEntry S → List S
bodyDeps (entry _ baseTypeDecl _ b) = b
bodyDeps (entry _ pureSigHelperDecl _ b) = b
bodyDeps (entry _ sweetBodyDecl _ b) = b
bodyDeps (entry _ exoBodyDecl _ b) = b
bodyDeps (entry _ boundaryHoleDecl _ _) = []

deps : DeclEntry S → List S
deps d = sigDeps d ++ bodyDeps d

dom : List (DeclEntry S) → List S
dom = map entrySym

infix 4 _⊆_
_⊆_ : List A → List A → Set
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

DownClosed : List (DeclEntry S) → Set
DownClosed ds = ∀ {d} → d ∈ ds → deps d ⊆ dom ds

data NoDupSyms {S : Set} : List (DeclEntry S) → Set where
  empty : NoDupSyms []
  fresh : ∀ {d ds} → ¬ (entrySym d ∈ dom ds) → NoDupSyms ds → NoDupSyms (d ∷ ds)

record CodePoint (Sym : Set) : Set where
  constructor point
  field
    entries : List (DeclEntry Sym)
    unique : NoDupSyms entries
    closed : DownClosed entries
open CodePoint public

shared : DeclSort → Bool
shared baseTypeDecl = true
shared pureSigHelperDecl = true
shared _ = false

Allowed : SliceColor → DeclSort → Set
Allowed SharedBase k = T (shared k)
Allowed SweetMod k = k ≢ exoBodyDecl
Allowed ExoMod k = k ≢ sweetBodyDecl
Allowed MixMod k = ⊤

HasSliceColor : SliceColor → CodePoint S → Set
HasSliceColor c m = DownClosed (entries m) ×
  (∀ {d} → d ∈ entries m → Allowed c (entrySort d))

-- The single base point has a fiber of code values, refined by slice color.
El : Set → BasePt → Set
El S ⋆ = CodePoint S

Colored : Set → SliceColor → Set
Colored S c = Σ (El S ⋆) (HasSliceColor c)

singleton-dangling : ¬ DownClosed [ decl true sweetBodyDecl [ false ] [] ]
singleton-dangling dc with dc (here refl) (here refl)
... | there ()

private
  key-unique : ∀ {ds : List (DeclEntry S)} {d e} → NoDupSyms ds →
    d ∈ ds → e ∈ ds → entrySym d ≡ entrySym e → d ≡ e
  key-unique (fresh n u) (here refl) (here refl) eq = refl
  key-unique (fresh n u) (here refl) (there q) eq = ⊥-elim (n (subst (_∈ _) (sym eq) (∈-map⁺ entrySym q)))
  key-unique (fresh n u) (there p) (here refl) eq = ⊥-elim (n (subst (_∈ _) eq (∈-map⁺ entrySym p)))
  key-unique (fresh n u) (there p) (there q) eq = key-unique u p q eq

  filter-unique : ∀ {P : DeclEntry S → Set} (P? : ∀ d → Dec (P d)) {ds} →
    NoDupSyms ds → NoDupSyms (filter P? ds)
  filter-unique P? empty = empty
  filter-unique P? (fresh {d} {ds} n u) with P? d
  ... | no _ = filter-unique P? u
  ... | yes _ = fresh apart (filter-unique P? u)
    where
    apart : ¬ (entrySym d ∈ dom (filter P? ds))
    apart p with ∈-map⁻ entrySym p
    ... | e , e∈ , refl = n (∈-map⁺ entrySym (proj₁ (∈-filter⁻ P? e∈)))

  select : ∀ {P : DeclEntry S → Set} (P? : ∀ d → Dec (P d)) (m : CodePoint S) →
    (∀ {d e} → d ∈ entries m → P d → e ∈ entries m → entrySym e ∈ deps d → P e) → CodePoint S
  select P? (point ds u dc) hered = point (filter P? ds) (filter-unique P? u) proof
    where
    proof : DownClosed (filter P? ds)
    proof {d} d∈ {s} s∈ with ∈-filter⁻ P? d∈
    ... | original , ok with ∈-map⁻ entrySym (dc original s∈)
    ... | e , e∈ , refl = ∈-map⁺ entrySym (∈-filter⁺ P? e∈ (hered original ok e∈ s∈))

  decideAll : ∀ {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) →
    Dec (∀ {x} → x ∈ xs → P x)
  decideAll test [] = yes λ ()
  decideAll test (x ∷ xs) with test x | decideAll test xs
  ... | no n | _ = no λ f → n (f (here refl))
  ... | yes _ | no n = no λ f → n (λ p → f (there p))
  ... | yes h | yes t = yes λ { (here refl) → h ; (there p) → t p }

  -- Removing an enabled worklist entry supplies both a structural bound and a
  -- partition witness, including in cyclic graphs and for duplicate requests.
  record Pick (P : A → Set) (xs : List A) : Set where
    constructor picked
    field
      item : A
      enabled : P item
      member : item ∈ xs
      rest : List A
      smaller : length xs ≡ suc (length rest)
      embed : rest ⊆ xs
      cases : ∀ {x} → x ∈ xs → x ≡ item ⊎ x ∈ rest

  pick : ∀ {P : A → Set} (test : ∀ x → Dec (P x)) (xs : List A) →
    (∀ {x} → x ∈ xs → ¬ P x) ⊎ Pick P xs
  pick test [] = inj₁ λ ()
  pick test (x ∷ xs) with test x
  ... | yes px = inj₂ (picked x px (here refl) xs refl there
      λ { (here refl) → inj₁ refl ; (there p) → inj₂ p })
  ... | no nx with pick test xs
  ...   | inj₁ none = inj₁ λ { (here refl) → nx ; (there q) → none q }
  ...   | inj₂ (picked y py mem ys sz emb parts) =
    inj₂ (picked y py (there mem) (x ∷ ys) (cong suc sz)
      (λ { (here refl) → here refl ; (there p) → there (emb p) })
      λ { (here refl) → inj₂ (here refl) ; (there p) → liftCase (parts p) })
    where
    liftCase : ∀ {z} → z ≡ y ⊎ z ∈ ys → z ≡ y ⊎ z ∈ (x ∷ ys)
    liftCase (inj₁ eq) = inj₁ eq
    liftCase (inj₂ q) = inj₂ (there q)

module Over {Sym : Set} (_≟_ : Decidable (_≡_ {A = Sym})) where
  private
    D = DeclEntry Sym

  member? : (s : Sym) (xs : List Sym) → Dec (s ∈ xs)
  member? s = any? (s ≟_)

  noDup? : (ds : List D) → Dec (NoDupSyms ds)
  noDup? [] = yes empty
  noDup? (d ∷ ds) with member? (entrySym d) (dom ds) | noDup? ds
  ... | yes p | _ = no λ { (fresh n u) → n p }
  ... | no _ | no n = no λ { (fresh _ u) → n u }
  ... | no n | yes u = yes (fresh n u)

  checkPoint : List D → Maybe (CodePoint Sym)
  checkPoint ds with noDup? ds | decideAll (λ d → decideAll (λ s → member? s (dom ds)) (deps d)) ds
  ... | yes u | yes dc = just (point ds u dc)
  ... | _ | _ = nothing

  Stable : List D → List Sym → Set
  Stable ds names = ∀ {d} → d ∈ ds → entrySym d ∈ names → deps d ⊆ names

  record Closure (ds : List D) (seeds : List Sym) : Set where
    constructor closure
    field
      names : List Sym
      contains : seeds ⊆ names
      follows : Stable ds names
      least : ∀ zs → seeds ⊆ zs → Stable ds zs → names ⊆ zs
  open Closure public

  private
    visit : (fuel : ℕ) (ds : List D) → length ds ≤ fuel → (ss : List Sym) → Closure ds ss
    visit fuel [] bound ss = closure ss (λ p → p) (λ ()) (λ _ sub _ → sub)
    visit (suc fuel) ds@(d ∷ tail) (s≤s bound) ss with pick (λ e → member? (entrySym e) ss) ds
    ... | inj₁ none = closure ss (λ p → p) (λ q p → ⊥-elim (none q p)) (λ _ sub _ → sub)
    ... | inj₂ (picked e enabled mem rest sz emb cases) = closure result roots stable minimal
      where
      predEq : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
      predEq refl = refl
      child = visit fuel rest (subst (_≤ fuel) (predEq sz) bound) (deps e ++ ss)
      result = names child
      roots : ss ⊆ result
      roots q = contains child (∈-++⁺ʳ (deps e) q)
      stable : Stable ds result
      stable q p r with cases q
      ... | inj₁ refl = contains child (∈-++⁺ˡ r)
      ... | inj₂ t = follows child t p r
      minimal : ∀ zs → ss ⊆ zs → Stable ds zs → result ⊆ zs
      minimal zs sub step = least child zs start (λ t → step (emb t))
        where
        start : deps e ++ ss ⊆ zs
        start p with ∈-++⁻ (deps e) p
        ... | inj₁ q = step mem (sub enabled) q
        ... | inj₂ q = sub q

  reachable : (ds : List D) (seeds : List Sym) → Closure ds seeds
  reachable ds = visit (length ds) ds ≤-refl

  private
    trim : CodePoint Sym → List Sym → CodePoint Sym
    trim m ss = select (λ d → member? (entrySym d) (names r)) m (λ d∈ p _ → follows r d∈ p)
      where r = reachable (entries m) ss

    trim-in : ∀ m ss {d} → d ∈ entries (trim m ss) →
      d ∈ entries m × entrySym d ∈ names (reachable (entries m) ss)
    trim-in m ss = ∈-filter⁻ _

    trim-keep : ∀ m ss {d} → d ∈ entries m → entrySym d ∈ ss →
      d ∈ entries (trim m ss)
    trim-keep m ss p q = ∈-filter⁺ _ p (contains (reachable (entries m) ss) q)

    T? : (b : Bool) → Dec (T b)
    T? true = yes tt
    T? false = no λ ()

    Reached : CodePoint Sym → D → List Sym
    Reached m d = names (reachable (entries m) [ entrySym d ])

    Clean : CodePoint Sym → D → Set
    Clean m d = ∀ {e} → e ∈ entries m → entrySym e ∈ Reached m d → T (shared (entrySort e))

    clean? : ∀ m d → Dec (Clean m d)
    clean? m d = decideAll test (entries m)
      where
      test : ∀ e → Dec (entrySym e ∈ Reached m d → T (shared (entrySort e)))
      test e with member? (entrySym e) (Reached m d) | T? (shared (entrySort e))
      ... | no n | _ = yes (λ p → ⊥-elim (n p))
      ... | yes _ | yes s = yes (λ _ → s)
      ... | yes p | no n = no λ f → n (f p)

    inherits : ∀ m {d e} → d ∈ entries m → Clean m d → e ∈ entries m →
      entrySym e ∈ deps d → Clean m e
    inherits m {d} {e} d∈ ok e∈ dep y∈ yName = ok y∈ (least fromE (names fromD) start (follows fromD) yName)
      where
      fromD = reachable (entries m) [ entrySym d ]
      fromE = reachable (entries m) [ entrySym e ]
      start : [ entrySym e ] ⊆ names fromD
      start (here refl) = follows fromD d∈ (contains fromD (here refl)) dep
      start (there ())

  -- Greatest dependency-closed subtable of shared kinds. If a purported shared
  -- declaration refers to an exotic body, it cannot inhabit the SharedBase fiber.
  computeSharedBase : CodePoint Sym → CodePoint Sym
  computeSharedBase m = select (clean? m) m (inherits m)

  shared-color : ∀ m → HasSliceColor SharedBase (computeSharedBase m)
  shared-color m = closed (computeSharedBase m) , proof
    where
    proof : ∀ {d} → d ∈ entries (computeSharedBase m) → T (shared (entrySort d))
    proof {d} q with ∈-filter⁻ (clean? m) q
    ... | p , ok = ok p (contains (reachable (entries m) [ entrySym d ]) (here refl))

  -- Any already-closed shared submodule embeds unchanged in the computed base.
  shared-greatest : ∀ m b → entries b ⊆ entries m → HasSliceColor SharedBase b →
    entries b ⊆ entries (computeSharedBase m)
  shared-greatest m b sub (_ , color) {d} p = ∈-filter⁺ (clean? m) (sub p) clean
    where
    stable : Stable (entries m) (dom (entries b))
    stable {x} x∈ key dep with ∈-map⁻ entrySym key
    ... | y , y∈ , eq with key-unique (unique m) x∈ (sub y∈) eq
    ... | refl = closed b y∈ dep
    start : [ entrySym d ] ⊆ dom (entries b)
    start (here refl) = ∈-map⁺ entrySym p
    start (there ())
    clean : Clean m d
    clean {e} e∈ reached with ∈-map⁻ entrySym
      (least (reachable (entries m) [ entrySym d ]) (dom (entries b)) start stable reached)
    ... | x , x∈ , eq with key-unique (unique m) e∈ (sub x∈) eq
    ... | refl = color x∈

  BaseStable : CodePoint Sym → Set
  BaseStable m = ∀ {d e} → d ∈ entries m → T (shared (entrySort d)) →
    e ∈ entries m → entrySym e ∈ deps d → T (shared (entrySort e))

  all-shared-in-base : ∀ m → BaseStable m → ∀ {d} → d ∈ entries m →
    T (shared (entrySort d)) → d ∈ entries (computeSharedBase m)
  all-shared-in-base m hereditary p ok =
    shared-greatest m b (λ q → proj₁ (∈-filter⁻ test {xs = entries m} q))
      (closed b , (λ q → proj₂ (∈-filter⁻ test {xs = entries m} q))) (∈-filter⁺ test p ok)
    where
    test = λ d → T? (shared (entrySort d))
    b = select test m hereditary

  private
    hole : D → D
    hole d = decl (entrySym d) boundaryHoleDecl (sigDeps d) []

    redact : (DeclSort → Bool) → D → D
    redact mask d with mask (entrySort d)
    ... | true = hole d
    ... | false = d

    key-preserved : ∀ mask d → entrySym (redact mask d) ≡ entrySym d
    key-preserved mask d with mask (entrySort d)
    ... | true = refl
    ... | false = refl

    smaller-deps : ∀ mask d → deps (redact mask d) ⊆ deps d
    smaller-deps mask d p with mask (entrySort d)
    ... | false = p
    ... | true with ∈-++⁻ (sigDeps d) p
    ...   | inj₁ q = ∈-++⁺ˡ q
    ...   | inj₂ ()

    dom-redact : ∀ mask ds → dom (map (redact mask) ds) ≡ dom ds
    dom-redact mask [] = refl
    dom-redact mask (d ∷ ds) rewrite key-preserved mask d | dom-redact mask ds = refl

    redact-unique : ∀ mask {ds} → NoDupSyms ds → NoDupSyms (map (redact mask) ds)
    redact-unique mask empty = empty
    redact-unique mask (fresh {d} {ds} n u) = fresh apart (redact-unique mask u)
      where
      apart : ¬ (entrySym (redact mask d) ∈ dom (map (redact mask) ds))
      apart rewrite key-preserved mask d | dom-redact mask ds = n

    redact-point : (DeclSort → Bool) → CodePoint Sym → CodePoint Sym
    redact-point mask (point ds u dc) = point (map (redact mask) ds) (redact-unique mask u) proof
      where
      proof : DownClosed (map (redact mask) ds)
      proof {d} p q with ∈-map⁻ (redact mask) p
      ... | e , e∈ , refl = subst (_ ∈_) (sym (dom-redact mask ds)) (dc e∈ (smaller-deps mask e q))

    isSweet isExo isBody : DeclSort → Bool
    isSweet sweetBodyDecl = true
    isSweet _ = false
    isExo exoBodyDecl = true
    isExo _ = false
    isBody sweetBodyDecl = true
    isBody exoBodyDecl = true
    isBody _ = false

    root? : (d : D) → Dec (entrySort d ≢ sweetBodyDecl)
    root? (entry _ sweetBodyDecl _ _) = no λ n → n refl
    root? (entry _ baseTypeDecl _ _) = yes λ ()
    root? (entry _ pureSigHelperDecl _ _) = yes λ ()
    root? (entry _ exoBodyDecl _ _) = yes λ ()
    root? (entry _ boundaryHoleDecl _ _) = yes λ ()

    agdaRoots : CodePoint Sym → List Sym
    agdaRoots m = dom (filter root? (entries m))

    agdaFull : CodePoint Sym → CodePoint Sym
    agdaFull = redact-point isSweet

  leanLane agdaLane : CodePoint Sym → CodePoint Sym
  leanLane = redact-point isExo
  agdaLane m = trim (agdaFull m) (agdaRoots m)

  pushoutSplit : CodePoint Sym → CodePoint Sym × CodePoint Sym × CodePoint Sym
  pushoutSplit m = computeSharedBase m , leanLane m , agdaLane m

  -- Reachability is computed after erasing proof bodies, so no body-only
  -- dependency can pull extra declarations into an upstream signature shell.
  projectUpstreamShell : CodePoint Sym → List Sym → CodePoint Sym
  projectUpstreamShell m = trim (redact-point isBody m)

  shell-closed : ∀ m seeds → DownClosed (entries (projectUpstreamShell m seeds))
  shell-closed m seeds = closed (projectUpstreamShell m seeds)

  private
    lean-kind : ∀ d → entrySort (redact isExo d) ≢ exoBodyDecl
    lean-kind (entry _ baseTypeDecl _ _) ()
    lean-kind (entry _ pureSigHelperDecl _ _) ()
    lean-kind (entry _ sweetBodyDecl _ _) ()
    lean-kind (entry _ exoBodyDecl _ _) ()
    lean-kind (entry _ boundaryHoleDecl _ _) ()

    agda-kind : ∀ d → entrySort (redact isSweet d) ≢ sweetBodyDecl
    agda-kind (entry _ baseTypeDecl _ _) ()
    agda-kind (entry _ pureSigHelperDecl _ _) ()
    agda-kind (entry _ sweetBodyDecl _ _) ()
    agda-kind (entry _ exoBodyDecl _ _) ()
    agda-kind (entry _ boundaryHoleDecl _ _) ()

    shell-kind : ∀ d → entrySort (redact isBody d) ≢ sweetBodyDecl
    shell-kind (entry _ baseTypeDecl _ _) ()
    shell-kind (entry _ pureSigHelperDecl _ _) ()
    shell-kind (entry _ sweetBodyDecl _ _) ()
    shell-kind (entry _ exoBodyDecl _ _) ()
    shell-kind (entry _ boundaryHoleDecl _ _) ()

  lean-color : ∀ m → HasSliceColor SweetMod (leanLane m)
  lean-color m = closed (leanLane m) , proof
    where
    proof : ∀ {d} → d ∈ entries (leanLane m) → entrySort d ≢ exoBodyDecl
    proof p with ∈-map⁻ (redact isExo) p
    ... | e , _ , refl = lean-kind e

  agda-color : ∀ m → HasSliceColor ExoMod (agdaLane m)
  agda-color m = closed (agdaLane m) , proof
    where
    proof : ∀ {d} → d ∈ entries (agdaLane m) → entrySort d ≢ sweetBodyDecl
    proof p with ∈-map⁻ (redact isSweet) (proj₁ (trim-in (agdaFull m) (agdaRoots m) p))
    ... | e , _ , refl = agda-kind e

  shell-no-fast-bodies : ∀ m ss {d} → d ∈ entries (projectUpstreamShell m ss) → entrySort d ≢ sweetBodyDecl
  shell-no-fast-bodies m ss p with ∈-map⁻ (redact isBody) (proj₁ (trim-in (redact-point isBody m) ss p))
  ... | e , _ , refl = shell-kind e

  shell-exact : ∀ m ss {d} → d ∈ entries (projectUpstreamShell m ss) →
    d ∈ entries (redact-point isBody m) × entrySym d ∈ names (reachable (entries (redact-point isBody m)) ss)
  shell-exact m ss = trim-in (redact-point isBody m) ss

  private
    agda-keep : ∀ m {d} → d ∈ entries m → entrySort d ≢ sweetBodyDecl →
      redact isSweet d ∈ entries (agdaLane m)
    agda-keep m {d} p ok = trim-keep (agdaFull m) (agdaRoots m) (∈-map⁺ (redact isSweet) p)
      (subst (_∈ agdaRoots m) (sym (key-preserved isSweet d)) (∈-map⁺ entrySym (∈-filter⁺ root? p ok)))

  shared-helper-unchanged : ∀ m {d} → d ∈ entries m → entrySort d ≡ pureSigHelperDecl →
    d ∈ entries (leanLane m) × d ∈ entries (agdaLane m)
  shared-helper-unchanged m {entry s pureSigHelperDecl a b} p refl =
    ∈-map⁺ (redact isExo) p , agda-keep m p (λ ())

  private
    dom-sub : ∀ {xs ys : List D} → xs ⊆ ys → dom xs ⊆ dom ys
    dom-sub sub p with ∈-map⁻ entrySym p
    ... | d , m , refl = ∈-map⁺ entrySym (sub m)

    ++-closed : ∀ {xs ys : List D} → DownClosed xs → DownClosed ys → DownClosed (xs ++ ys)
    ++-closed {xs} {ys} a b p q with ∈-++⁻ xs p
    ... | inj₁ m = dom-sub {xs} {xs ++ ys} ∈-++⁺ˡ (a m q)
    ... | inj₂ m = dom-sub {ys} {xs ++ ys} (∈-++⁺ʳ xs) (b m q)

    record Registry (xs : List D) : Set where
      constructor registry
      field
        rows : List D
        distinct : NoDupSyms rows
        origin : rows ⊆ xs
        covers : dom xs ⊆ dom rows
    open Registry

    -- Canonical keys choose one representative. Input order breaks ties
    -- between conflicting concrete declarations in an arbitrary pair of tables.
    register : (xs : List D) → Registry xs
    register [] = registry [] empty (λ ()) (λ ())
    register (d ∷ ds) with register ds
    ... | registry rs u sub cover with member? (entrySym d) (dom rs)
    ...   | yes seen = registry rs u (λ q → there (sub q))
      (λ { (here refl) → seen ; (there q) → cover q })
    ...   | no n = registry (d ∷ rs) (fresh n u)
      (λ { (here refl) → here refl ; (there p) → there (sub p) })
      (λ { (here refl) → here refl ; (there q) → there (cover q) })

    Concrete : D → Set
    Concrete d = entrySort d ≢ boundaryHoleDecl

    concrete? : (d : D) → Dec (Concrete d)
    concrete? (entry _ baseTypeDecl _ _) = yes λ ()
    concrete? (entry _ pureSigHelperDecl _ _) = yes λ ()
    concrete? (entry _ exoBodyDecl _ _) = yes λ ()
    concrete? (entry _ sweetBodyDecl _ _) = yes λ ()
    concrete? (entry _ boundaryHoleDecl _ _) = no λ n → n refl

    Eligible : List D → D → Set
    Eligible xs d = Concrete d ⊎ ¬ (entrySym d ∈ dom (filter concrete? xs))

    eligible? : ∀ xs d → Dec (Eligible xs d)
    eligible? xs d with concrete? d | member? (entrySym d) (dom (filter concrete? xs))
    ... | yes c | _ = yes (inj₁ c)
    ... | no _ | no n = yes (inj₂ n)
    ... | no n | yes p = no λ { (inj₁ c) → n c ; (inj₂ k) → k p }

    gluedRows : (xs : List D) → Registry (filter (eligible? xs) xs)
    gluedRows xs = register (filter (eligible? xs) xs)

    representatives : ∀ xs → dom xs ⊆ dom (rows (gluedRows xs))
    representatives xs key with ∈-map⁻ entrySym key
    ... | d , d∈ , refl with member? (entrySym d) (dom (filter concrete? xs))
    ...   | no n = covers (gluedRows xs) (∈-map⁺ entrySym (∈-filter⁺ (eligible? xs) d∈ (inj₂ n)))
    ...   | yes seen with ∈-map⁻ entrySym seen
    ...     | e , e∈ , eq with ∈-filter⁻ concrete? {xs = xs} e∈
    ...       | org , c = covers (gluedRows xs) (subst (_∈ _) (sym eq)
        (∈-map⁺ entrySym (∈-filter⁺ (eligible? xs) org (inj₁ c))))

    chosen : ∀ xs {d} → d ∈ rows (gluedRows xs) → d ∈ xs × Eligible xs d
    chosen xs p = ∈-filter⁻ (eligible? xs) (origin (gluedRows xs) p)

    candidates : CodePoint Sym → CodePoint Sym → CodePoint Sym → List D
    candidates b l r = entries b ++ entries l ++ entries r

  pushoutGlue : CodePoint Sym → CodePoint Sym → CodePoint Sym → CodePoint Sym
  pushoutGlue b l r = point (rows reg) (distinct reg) proof
    where
    xs = candidates b l r
    reg = gluedRows xs
    dc : DownClosed xs
    dc = ++-closed {entries b} {entries l ++ entries r} (closed b)
      (++-closed {entries l} {entries r} (closed l) (closed r))
    proof : DownClosed (rows reg)
    proof p q = representatives xs (dc (proj₁ (chosen xs p)) q)

  recombine : CodePoint Sym → CodePoint Sym
  recombine m = pushoutGlue (computeSharedBase m) (leanLane m) (agdaLane m)

  private
    both : (m : CodePoint Sym) → List D
    both m = candidates (computeSharedBase m) (leanLane m) (agdaLane m)

    from-lean : ∀ m → entries (leanLane m) ⊆ both m
    from-lean m p = ∈-++⁺ʳ (entries (computeSharedBase m)) (∈-++⁺ˡ p)

    from-agda : ∀ m → entries (agdaLane m) ⊆ both m
    from-agda m p = ∈-++⁺ʳ (entries (computeSharedBase m)) (∈-++⁺ʳ (entries (leanLane m)) p)

    supplied : ∀ m → entries m ⊆ both m
    supplied m {entry s baseTypeDecl a b} p = from-lean m (∈-map⁺ (redact isExo) p)
    supplied m {entry s pureSigHelperDecl a b} p = from-lean m (∈-map⁺ (redact isExo) p)
    supplied m {entry s sweetBodyDecl a b} p = from-lean m (∈-map⁺ (redact isExo) p)
    supplied m {entry s boundaryHoleDecl a b} p = from-lean m (∈-map⁺ (redact isExo) p)
    supplied m {entry s exoBodyDecl a b} p = from-agda m (agda-keep m p (λ ()))

    Source : CodePoint Sym → D → Set
    Source m d = ∃ λ e → e ∈ entries m × (d ≡ e ⊎ d ≡ hole e)

    same-or-hole : ∀ mask d → redact mask d ≡ d ⊎ redact mask d ≡ hole d
    same-or-hole mask d with mask (entrySort d)
    ... | true = inj₂ refl
    ... | false = inj₁ refl

    source : ∀ m {d} → d ∈ both m → Source m d
    source m {d} p with ∈-++⁻ (entries (computeSharedBase m)) p
    ... | inj₁ base = d , proj₁ (∈-filter⁻ (clean? m) base) , inj₁ refl
    ... | inj₂ lanes with ∈-++⁻ (entries (leanLane m)) lanes
    ...   | inj₁ lean with ∈-map⁻ (redact isExo) lean
    ...     | e , e∈ , refl = e , e∈ , same-or-hole isExo e
    source m p | inj₂ lanes | inj₂ agda with ∈-map⁻ (redact isSweet)
      (proj₁ (trim-in (agdaFull m) (agdaRoots m) agda))
    ...   | e , e∈ , refl = e , e∈ , same-or-hole isSweet e

    original-key : ∀ {d e} → (d ≡ e ⊎ d ≡ hole e) → entrySym d ≡ entrySym e
    original-key (inj₁ refl) = refl
    original-key (inj₂ refl) = refl

    winning : ∀ m {d e} → d ∈ entries m → e ∈ entries (recombine m) → entrySym d ≡ entrySym e →
      d ≡ e
    winning m {d} {e} d∈ e∈ eq with chosen (both m) e∈
    ... | src , allowed with source m src
    ...   | x , x∈ , form with key-unique (unique m) d∈ x∈ (trans eq (original-key form))
    ...     | refl with form
    ...       | inj₁ refl = refl
    ...       | inj₂ refl = resolved d d∈ allowed
      where
      resolved : ∀ x → x ∈ entries m → Eligible (both m) (hole x) → x ≡ hole x
      resolved x x∈ (inj₁ c) = ⊥-elim (c refl)
      resolved x x∈ (inj₂ n) with concrete? x
      ... | yes c = ⊥-elim (n (∈-map⁺ entrySym (∈-filter⁺ concrete? (supplied m x∈) c)))
      resolved (entry _ baseTypeDecl _ _) _ (inj₂ n) | no impossible = ⊥-elim (impossible λ ())
      resolved (entry _ pureSigHelperDecl _ _) _ (inj₂ n) | no impossible = ⊥-elim (impossible λ ())
      resolved (entry _ sweetBodyDecl _ _) _ (inj₂ n) | no impossible = ⊥-elim (impossible λ ())
      resolved (entry _ exoBodyDecl _ _) _ (inj₂ n) | no impossible = ⊥-elim (impossible λ ())
      resolved (entry _ boundaryHoleDecl _ _) _ (inj₂ n) | no _ = refl

  split-glue-recovers : ∀ m → entries m ⊆ entries (recombine m)
  split-glue-recovers m {d} p with ∈-map⁻ entrySym (representatives (both m) (∈-map⁺ entrySym (supplied m p)))
  ... | e , e∈ , eq = subst (_∈ _) (sym (winning m p e∈ eq)) e∈

  split-glue-reflects : ∀ m → entries (recombine m) ⊆ entries m
  split-glue-reflects m p with source m (proj₁ (chosen (both m) p))
  ... | d , d∈ , form = subst (_∈ _) (winning m d∈ p (sym (original-key form))) d∈

  split-glue-no-holes : ∀ m → (∀ {d} → d ∈ entries m → Concrete d) →
    ∀ {d} → d ∈ entries (recombine m) → Concrete d
  split-glue-no-holes m total p = total (split-glue-reflects m p)

  split-glue-unique : ∀ m → NoDupSyms (entries (recombine m))
  split-glue-unique m = unique (recombine m)

  toBoundary : D → D
  toBoundary = hole

  lean-origin : ∀ m {d} → d ∈ entries (leanLane m) →
    ∃ λ e → e ∈ entries m × (d ≡ e ⊎ d ≡ toBoundary e)
  lean-origin m p = source m (from-lean m p)

  agda-origin : ∀ m {d} → d ∈ entries (agdaLane m) →
    ∃ λ e → e ∈ entries m × (d ≡ e ⊎ d ≡ toBoundary e)
  agda-origin m p = source m (from-agda m p)

  lanes-cover : ∀ m {d} → d ∈ entries m → d ∈ entries (leanLane m) ⊎ d ∈ entries (agdaLane m)
  lanes-cover m {entry s baseTypeDecl a b} p = inj₁ (∈-map⁺ (redact isExo) p)
  lanes-cover m {entry s pureSigHelperDecl a b} p = inj₁ (∈-map⁺ (redact isExo) p)
  lanes-cover m {entry s sweetBodyDecl a b} p = inj₁ (∈-map⁺ (redact isExo) p)
  lanes-cover m {entry s boundaryHoleDecl a b} p = inj₁ (∈-map⁺ (redact isExo) p)
  lanes-cover m {entry s exoBodyDecl a b} p = inj₂ (agda-keep m p (λ ()))

  diagonal : ∀ m {d} → d ∈ entries (computeSharedBase m) →
    d ∈ entries (leanLane m) × d ∈ entries (agdaLane m)
  diagonal m {d} p = keep d (proj₁ (∈-filter⁻ (clean? m) p)) (proj₂ (shared-color m) p)
    where
    keep : ∀ x → x ∈ entries m → T (shared (entrySort x)) →
      x ∈ entries (leanLane m) × x ∈ entries (agdaLane m)
    keep (entry _ baseTypeDecl _ _) q tt = ∈-map⁺ (redact isExo) q , agda-keep m q (λ ())
    keep (entry _ pureSigHelperDecl _ _) q tt = shared-helper-unchanged m q refl

  signatureTable : CodePoint Sym → CodePoint Sym
  signatureTable = redact-point isBody

  -- Among signature tables containing the roots, the projection is the
  -- least closed submodule (order by unchanged declaration inclusion).
  shell-least : ∀ m ss b → ss ⊆ dom (entries b) → entries b ⊆ entries (signatureTable m) →
    entries (projectUpstreamShell m ss) ⊆ entries b
  shell-least m ss b start sub {d} p = retain (shell-exact m ss p)
    where
    full = signatureTable m
    stable : Stable (entries full) (dom (entries b))
    stable {e} e∈ key dep with ∈-map⁻ entrySym key
    ... | f , f∈ , eq with key-unique (unique full) e∈ (sub f∈) eq
    ... | refl = closed b f∈ dep
    retain : d ∈ entries full × entrySym d ∈ names (reachable (entries full) ss) → d ∈ entries b
    retain (d∈ , seen) with ∈-map⁻ entrySym (least (reachable (entries full) ss) (dom (entries b)) start stable seen)
    ... | e , e∈ , eq = subst (_∈ entries b) (sym (key-unique (unique full) d∈ (sub e∈) eq)) e∈

  shell-covers-seeds : ∀ m ss → ss ⊆ dom (entries m) → ss ⊆ dom (entries (projectUpstreamShell m ss))
  shell-covers-seeds m ss sub {s} p with ∈-map⁻ entrySym
    (subst (s ∈_) (sym (dom-redact isBody (entries m))) (sub p))
  ... | d , d∈ , refl = ∈-map⁺ entrySym (trim-keep (signatureTable m) ss d∈ p)

  -- A refinement preserves the key and signature dependency list. The IR
  -- bridge retains the original type expression when it abstracts a body.
  infix 4 _≼_ _⊑_
  _≼_ : D → D → Set
  d ≼ e = d ≡ e ⊎ d ≡ toBoundary e

  ≼-trans : ∀ {d e f} → d ≼ e → e ≼ f → d ≼ f
  ≼-trans (inj₁ refl) q = q
  ≼-trans (inj₂ refl) (inj₁ refl) = inj₂ refl
  ≼-trans (inj₂ refl) (inj₂ refl) = inj₂ refl

  _⊑_ : CodePoint Sym → CodePoint Sym → Set
  m ⊑ n = ∀ {d} → d ∈ entries m → ∃ λ e → e ∈ entries n × d ≼ e

  -- The refinement category is thin. Proof irrelevance here expresses that
  -- two arrows with the same endpoints are equal, even for interface entries
  -- for which both presentations of a reflexive refinement are possible.
  record Hom (m n : CodePoint Sym) : Set where
    constructor arrow
    field .witness : m ⊑ n

  hom-unique : ∀ {m n} (f g : Hom m n) → f ≡ g
  hom-unique f g = refl

  hom-id : ∀ {m} → Hom m m
  hom-id = arrow (λ p → _ , p , inj₁ refl)

  compose-refinement : ∀ {m n o} → n ⊑ o → m ⊑ n → m ⊑ o
  compose-refinement g f p with f p
  ... | e , e∈ , r with g e∈
  ... | x , x∈ , q = x , x∈ , ≼-trans r q

  _after_ : ∀ {m n o} → Hom n o → Hom m n → Hom m o
  _after_ {m} {n} {o} (arrow g) (arrow f) = arrow (compose-refinement {m} {n} {o} g f)

  inclusion : ∀ {m n} → entries m ⊆ entries n → Hom m n
  inclusion sub = arrow λ p → _ , sub p , inj₁ refl

  record IsPushout (b l r g : CodePoint Sym) : Set where
    field
      base-left : Hom b l
      base-right : Hom b r
      in-left : Hom l g
      in-right : Hom r g
      mediate : ∀ t → Hom l t → Hom r t → Hom g t

    commutes : (in-left after base-left) ≡ (in-right after base-right)
    commutes = hom-unique _ _

    factor-left : ∀ t (f : Hom l t) (h : Hom r t) → (mediate t f h after in-left) ≡ f
    factor-left t f h = hom-unique _ _

    factor-right : ∀ t (f : Hom l t) (h : Hom r t) → (mediate t f h after in-right) ≡ h
    factor-right t f h = hom-unique _ _

    unique-mediator : ∀ t (f : Hom l t) (h : Hom r t) (k : Hom g t) →
      k ≡ mediate t f h
    unique-mediator t f h k = hom-unique _ _

  split-is-pushout : ∀ m → IsPushout (computeSharedBase m) (leanLane m) (agdaLane m) (recombine m)
  split-is-pushout m = record
    { base-left = inclusion (λ p → proj₁ (diagonal m p))
    ; base-right = inclusion (λ p → proj₂ (diagonal m p))
    ; in-left = arrow (λ p → leg (lean-origin m p))
    ; in-right = arrow (λ p → leg (agda-origin m p))
    ; mediate = universal
    }
    where
    leg : ∀ {d} → Source m d → ∃ λ e → e ∈ entries (recombine m) × d ≼ e
    leg (e , e∈ , r) = e , split-glue-recovers m e∈ , r
    bound : ∀ t → leanLane m ⊑ t → agdaLane m ⊑ t → recombine m ⊑ t
    bound t f h p with lanes-cover m (split-glue-reflects m p)
    ... | inj₁ q = f q
    ... | inj₂ q = h q
    universal : ∀ t → Hom (leanLane m) t → Hom (agdaLane m) t → Hom (recombine m) t
    universal t (arrow f) (arrow h) = arrow (bound t f h)

  private
    sortCode : DeclSort → ℕ
    sortCode baseTypeDecl = 0
    sortCode pureSigHelperDecl = 1
    sortCode sweetBodyDecl = 2
    sortCode exoBodyDecl = 3
    sortCode boundaryHoleDecl = 4

    sortAt : ℕ → DeclSort
    sortAt 0 = baseTypeDecl
    sortAt 1 = pureSigHelperDecl
    sortAt 2 = sweetBodyDecl
    sortAt 3 = exoBodyDecl
    sortAt _ = boundaryHoleDecl

    sort-roundtrip : ∀ k → sortAt (sortCode k) ≡ k
    sort-roundtrip baseTypeDecl = refl
    sort-roundtrip pureSigHelperDecl = refl
    sort-roundtrip sweetBodyDecl = refl
    sort-roundtrip exoBodyDecl = refl
    sort-roundtrip boundaryHoleDecl = refl

    sortEq : Decidable (_≡_ {A = DeclSort})
    sortEq k j with sortCode k Nat.≟ sortCode j
    ... | yes eq = yes (trans (sym (sort-roundtrip k)) (trans (cong sortAt eq) (sort-roundtrip j)))
    ... | no n = no λ eq → n (cong sortCode eq)

    entry-ext : ∀ {d e : D} → entrySym d ≡ entrySym e → entrySort d ≡ entrySort e →
      sigDeps d ≡ sigDeps e → bodyDeps d ≡ bodyDeps e → d ≡ e
    entry-ext {entry _ baseTypeDecl _ _} {entry _ _ _ _} refl refl refl refl = refl
    entry-ext {entry _ pureSigHelperDecl _ _} {entry _ _ _ _} refl refl refl refl = refl
    entry-ext {entry _ sweetBodyDecl _ _} {entry _ _ _ _} refl refl refl refl = refl
    entry-ext {entry _ exoBodyDecl _ _} {entry _ _ _ _} refl refl refl refl = refl
    entry-ext {entry _ boundaryHoleDecl _ _} {entry _ _ _ _} refl refl refl refl = refl

    entryEq : Decidable (_≡_ {A = D})
    entryEq d e with entrySym d ≟ entrySym e | sortEq (entrySort d) (entrySort e)
                  | Lists.≡-dec _≟_ (sigDeps d) (sigDeps e) | Lists.≡-dec _≟_ (bodyDeps d) (bodyDeps e)
    ... | no n | _ | _ | _ = no λ p → n (cong entrySym p)
    ... | yes _ | no n | _ | _ = no λ p → n (cong entrySort p)
    ... | yes _ | yes _ | no n | _ = no λ p → n (cong sigDeps p)
    ... | yes _ | yes _ | yes _ | no n = no λ p → n (cong bodyDeps p)
    ... | yes k | yes j | yes a | yes b = yes (entry-ext k j a b)

    refinement? : ∀ d e → Dec (d ≼ e)
    refinement? d e with entryEq d e | entryEq d (hole e)
    ... | yes eq | _ = yes (inj₁ eq)
    ... | no _ | yes eq = yes (inj₂ eq)
    ... | no n | no k = no λ { (inj₁ p) → n p ; (inj₂ p) → k p }

    Comparable : D → D → Set
    Comparable d e = entrySym d ≡ entrySym e → (d ≼ e) ⊎ (e ≼ d)

    compatible? : ∀ d e → Dec (Comparable d e)
    compatible? d e with entrySym d ≟ entrySym e | refinement? d e | refinement? e d
    ... | no n | _ | _ = yes λ p → ⊥-elim (n p)
    ... | yes _ | yes p | _ = yes λ _ → inj₁ p
    ... | yes _ | no _ | yes p = yes λ _ → inj₂ p
    ... | yes eq | no n | no k = no λ f → reject (f eq)
      where
      reject : _ → ⊥
      reject (inj₁ p) = n p
      reject (inj₂ p) = k p

    base-in? : ∀ b l → Dec (entries b ⊆ entries l)
    base-in? b l = decideAll (λ x → any? (entryEq x) (entries l)) (entries b)

    PairwiseCompatible : List D → Set
    PairwiseCompatible xs = ∀ {d} → d ∈ xs → ∀ {e} → e ∈ xs → Comparable d e

    pairs? : ∀ xs → Dec (PairwiseCompatible xs)
    pairs? xs = decideAll (λ x → decideAll (compatible? x) xs) xs

    closed-hole : ∀ d → ¬ Concrete d → d ≡ toBoundary d
    closed-hole (entry _ baseTypeDecl _ _) n = ⊥-elim (n λ ())
    closed-hole (entry _ pureSigHelperDecl _ _) n = ⊥-elim (n λ ())
    closed-hole (entry _ sweetBodyDecl _ _) n = ⊥-elim (n λ ())
    closed-hole (entry _ exoBodyDecl _ _) n = ⊥-elim (n λ ())
    closed-hole (entry _ boundaryHoleDecl _ _) n = refl

    choose-leg : ∀ xs {d e} → d ∈ xs → Eligible xs e → (d ≼ e) ⊎ (e ≼ d) → d ≼ e
    choose-leg xs p ok (inj₁ r) = r
    choose-leg xs p ok (inj₂ (inj₁ refl)) = inj₁ refl
    choose-leg xs p (inj₁ c) (inj₂ (inj₂ refl)) = ⊥-elim (c refl)
    choose-leg xs {d} p (inj₂ n) (inj₂ (inj₂ refl)) with concrete? d
    ... | no h = inj₁ (closed-hole d h)
    ... | yes c = ⊥-elim (n (∈-map⁺ entrySym (∈-filter⁺ concrete? p c)))

  compatible-pushout : ∀ b l r → entries b ⊆ entries l → entries b ⊆ entries r →
    PairwiseCompatible (candidates b l r) → IsPushout b l r (pushoutGlue b l r)
  compatible-pushout b l r left right agree = record
    { base-left = inclusion left
    ; base-right = inclusion right
    ; in-left = arrow λ p → leg (∈-++⁺ʳ (entries b) (∈-++⁺ˡ p))
    ; in-right = arrow λ p → leg (∈-++⁺ʳ (entries b) (∈-++⁺ʳ (entries l) p))
    ; mediate = universal
    }
    where
    xs = candidates b l r
    g = pushoutGlue b l r
    leg : ∀ {d} → d ∈ xs → ∃ λ e → e ∈ entries g × d ≼ e
    leg {d} p with ∈-map⁻ entrySym (representatives xs (∈-map⁺ entrySym p))
    ... | e , e∈ , eq with chosen xs e∈
    ... | from , ok = e , e∈ , choose-leg xs p ok (agree p from eq)
    bound : ∀ t → l ⊑ t → r ⊑ t → g ⊑ t
    bound t f h p with ∈-++⁻ (entries b) (proj₁ (chosen xs p))
    ... | inj₁ q = f (left q)
    ... | inj₂ q with ∈-++⁻ (entries l) q
    ...   | inj₁ v = f v
    ...   | inj₂ v = h v
    universal : ∀ t → Hom l t → Hom r t → Hom g t
    universal t (arrow f) (arrow h) = arrow (bound t f h)

  -- Validate externally supplied spans before treating their merge as a
  -- categorical pushout. Same-name concrete disagreements and differently
  -- typed holes fail the comparison, even when the output would be closed.
  checkedPushoutGlue : ∀ b l r → Maybe (Σ (CodePoint Sym) (IsPushout b l r))
  checkedPushoutGlue b l r with base-in? b l | base-in? b r | pairs? (candidates b l r)
  ... | yes left | yes right | yes agree = just (pushoutGlue b l r , compatible-pushout b l r left right agree)
  ... | _ | _ | _ = nothing

-- Concrete canonical names may be character strings or lists of name segments.
import Data.Char.Properties as Char
import Data.String.Properties as String
module CharSymbols = Over (Lists.≡-dec Char._≟_)
module QNameSymbols = Over (Lists.≡-dec String._≟_)

-- Port semantics and the categorical laws are independent of symbol representation.
module PortSemantics where
  open import Data.Bool.Base using (Bool; true; false; if_then_else_)
  open import Data.Empty using (⊥)
  open import Data.List.Base using (List; []; _∷_; _++_; concatMap)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s)
  open import Data.Nat.Properties using (≤-refl; ≤-step; +-mono-≤; *-suc)
  open import Data.Product using (_×_; _,_)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Unit.Base using (⊤)
  open import Relation.Binary using (Decidable)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Nullary using (yes; no)
  import Data.List.Membership.DecPropositional as Membership

  data ForbiddenAx : Set where
    propextAx choiceAx quotSoundAx sorryAx trustMeAx unsafePrimAx : ForbiddenAx

  data AxiomTag (Sym : Set) : Set where
    approvedBoundary : Sym → AxiomTag Sym
    forbiddenKernelAxiom : ForbiddenAx → AxiomTag Sym

  CleanFootprint : ∀ {Sym} → List (AxiomTag Sym) → Set
  CleanFootprint xs = ∀ bad → forbiddenKernelAxiom bad ∉ xs

  module Guard {Sym : Set} (_≟_ : Decidable (_≡_ {A = Sym})) where
    open Membership _≟_ using (_∈?_)

    guardAxiomsAssuming : List Sym → List (AxiomTag Sym) → Bool
    guardAxiomsAssuming allowed [] = true
    guardAxiomsAssuming allowed (forbiddenKernelAxiom _ ∷ _) = false
    guardAxiomsAssuming allowed (approvedBoundary s ∷ xs) with s ∈? allowed
    ... | yes _ = guardAxiomsAssuming allowed xs
    ... | no _ = false

    Admitted : List Sym → AxiomTag Sym → Set
    Admitted allowed (approvedBoundary s) = s ∈ allowed
    Admitted allowed (forbiddenKernelAxiom _) = ⊥

    accepted-member : ∀ {allowed xs tag} → guardAxiomsAssuming allowed xs ≡ true →
      tag ∈ xs → Admitted allowed tag
    accepted-member {xs = []} ok ()
    accepted-member {xs = forbiddenKernelAxiom _ ∷ xs} () m
    accepted-member {allowed} {approvedBoundary s ∷ xs} ok m with s ∈? allowed
    ... | no _ with ok
    ...   | ()
    accepted-member {allowed} {approvedBoundary s ∷ xs} ok m | yes a with m
    ... | here refl = a
    ... | there rest = accepted-member {allowed} {xs} ok rest

    guard-clean : ∀ {allowed xs} → guardAxiomsAssuming allowed xs ≡ true → CleanFootprint xs
    guard-clean {allowed} {xs} ok bad = accepted-member {allowed} {xs} ok

    clean-append : ∀ {xs ys} → CleanFootprint {Sym} xs → CleanFootprint ys →
      CleanFootprint (xs ++ ys)
    clean-append {xs} left right bad mem with ∈-++⁻ xs mem
    ... | inj₁ m = left bad m
    ... | inj₂ m = right bad m

    -- The resolver supplies the actual footprint for each checked boundary.
    -- Preserve all these footprints in the union, including transitive axioms.
    clean-resolutions : (allowed : List Sym) (footprint : Sym → List (AxiomTag Sym)) →
      (∀ s → s ∈ allowed → CleanFootprint (footprint s)) →
      CleanFootprint (concatMap footprint allowed)
    clean-resolutions [] footprint checked bad ()
    clean-resolutions (s ∷ ss) footprint checked =
      clean-append (checked s (here refl))
        (clean-resolutions ss footprint (λ t member → checked t (there member)))

    guard-glue-sound : ∀ allowed lean footprint →
      guardAxiomsAssuming allowed lean ≡ true →
      (∀ s → s ∈ allowed → CleanFootprint (footprint s)) →
      CleanFootprint (lean ++ concatMap footprint allowed)
    guard-glue-sound allowed lean footprint ok checked =
      clean-append (guard-clean {allowed} {lean} ok) (clean-resolutions allowed footprint checked)

    legacyGuard : Bool → List (AxiomTag Sym) → Bool
    legacyGuard true _ = true
    legacyGuard false xs = guardAxiomsAssuming [] xs

    legacyUncheckedHybridUnsound :
      let dirty = forbiddenKernelAxiom choiceAx ∷ [] in
      (legacyGuard true dirty ≡ true) × (guardAxiomsAssuming [] dirty ≡ false)
    legacyUncheckedHybridUnsound = refl , refl

  data EvalColor : Set where
    Ghost Thunked StrictVal : EvalColor

  -- The bit selects a render alternative. Leaves have an observable payload so
  -- equality of the two evaluators includes the choice of branch.
  data ChoiceTree : Set where
    leaf : ℕ → ChoiceTree
    branch : Bool → ChoiceTree → ChoiceTree → ChoiceTree

  evalStrictVal : ChoiceTree → ℕ
  evalStrictVal (leaf v) = v
  evalStrictVal (branch b l r) = if b then evalStrictVal l else evalStrictVal r

  evalThunkedVal : ChoiceTree → ℕ
  evalThunkedVal (leaf v) = v
  evalThunkedVal (branch true l r) = evalThunkedVal l
  evalThunkedVal (branch false l r) = evalThunkedVal r

  thunked-preserves-value : ∀ t → evalThunkedVal t ≡ evalStrictVal t
  thunked-preserves-value (leaf v) = refl
  thunked-preserves-value (branch true l r) = thunked-preserves-value l
  thunked-preserves-value (branch false l r) = thunked-preserves-value r

  -- Strict execution pays for both operands before selection. A thunked branch
  -- pays for dispatch and forcing its chosen child. A leaf costs one in either model.
  evalStrictCost : ChoiceTree → ℕ
  evalStrictCost (leaf _) = 1
  evalStrictCost (branch _ l r) = suc (evalStrictCost l + evalStrictCost r)

  evalThunkedCost : ChoiceTree → ℕ
  evalThunkedCost (leaf _) = 1
  evalThunkedCost (branch true l r) = suc (suc (evalThunkedCost l))
  evalThunkedCost (branch false l r) = suc (suc (evalThunkedCost r))

  spineChain : ℕ → ChoiceTree
  spineChain zero = leaf 0
  spineChain (suc n) = let tail = spineChain n in branch true tail tail

  exp2 : ℕ → ℕ
  exp2 zero = 1
  exp2 (suc n) = exp2 n + exp2 n

  thunked-spine-linear : ∀ n → evalThunkedCost (spineChain n) ≤ suc (2 * n)
  thunked-spine-linear zero = ≤-refl
  thunked-spine-linear (suc n) rewrite *-suc 2 n = s≤s (s≤s (thunked-spine-linear n))

  strict-spine-exponential : ∀ n → exp2 n ≤ evalStrictCost (spineChain n)
  strict-spine-exponential zero = ≤-refl
  strict-spine-exponential (suc n) =
    let ih = strict-spine-exponential n in ≤-step (+-mono-≤ ih ih)

  -- Parenthesized contexts make exchange and reassociation explicit. A cut
  -- joins one output to one input and carries all the other ports through.
  module Poly {Color : Set} (Fiber : Color → Set) where
    infixr 5 _⊗_
    data Ports : Set where
      empty : Ports
      port : Color → Ports
      _⊗_ : Ports → Ports → Ports

    Values : Ports → Set
    Values empty = ⊤
    Values (port c) = Fiber c
    Values (xs ⊗ ys) = Values xs × Values ys

    Arrow : Ports → Ports → Set
    Arrow xs ys = Values xs → Values ys

    identity : ∀ {P} → Arrow P P
    identity x = x

    infixl 2 _then_
    _then_ : ∀ {P Q R} → Arrow P Q → Arrow Q R → Arrow P R
    (f then g) x = g (f x)

    tensor : ∀ {P Q R S} → Arrow P Q → Arrow R S → Arrow (P ⊗ R) (Q ⊗ S)
    tensor f g (x , y) = f x , g y

    exchange : ∀ {P Q} → Arrow (P ⊗ Q) (Q ⊗ P)
    exchange (x , y) = y , x

    associate : ∀ {P Q R} → Arrow ((P ⊗ Q) ⊗ R) (P ⊗ (Q ⊗ R))
    associate ((x , y) , z) = x , (y , z)

    unassociate : ∀ {P Q R} → Arrow (P ⊗ (Q ⊗ R)) ((P ⊗ Q) ⊗ R)
    unassociate (x , (y , z)) = (x , y) , z

    diagonal : ∀ {P} → Arrow P (P ⊗ P)
    diagonal x = x , x

    cut : ∀ {P Q R S c} → Arrow P (Q ⊗ port c) → Arrow (port c ⊗ R) S →
      Arrow (P ⊗ R) (Q ⊗ S)
    cut f g (x , r) with f x
    ... | q , v = q , g (v , r)

    -- Laws are extensional (on port values), so no function extensionality
    -- axiom or equality of transported declaration-table certificates is needed.
    id-left : ∀ {P Q} (f : Arrow P Q) x → _then_ {P} {P} {Q} (identity {P}) f x ≡ f x
    id-left f x = refl

    id-right : ∀ {P Q} (f : Arrow P Q) x → _then_ {P} {Q} {Q} f (identity {Q}) x ≡ f x
    id-right f x = refl

    compose-assoc : ∀ {P Q R S} (f : Arrow P Q) (g : Arrow Q R) (h : Arrow R S) x →
      _then_ {P} {R} {S} (_then_ {P} {Q} {R} f g) h x
      ≡ _then_ {P} {Q} {S} f (_then_ {Q} {R} {S} g h) x
    compose-assoc f g h x = refl

    exchange-involutive : ∀ {P Q} (x : Values (P ⊗ Q)) →
      exchange {Q} {P} (exchange {P} {Q} x) ≡ x
    exchange-involutive (x , y) = refl

    tensor-interchange : ∀ {P Q R S T U} (f : Arrow P Q) (g : Arrow Q R)
      (h : Arrow S T) (k : Arrow T U) (x : Values (P ⊗ S)) →
      tensor {Q} {R} {T} {U} g k (tensor {P} {Q} {S} {T} f h x)
      ≡ tensor {P} {R} {S} {U} (_then_ {P} {Q} {R} f g) (_then_ {S} {T} {U} h k) x
    tensor-interchange f g h k (x , y) = refl

    -- The two orders of cutting c and d give the same outputs, modulo the
    -- written associators on the input and output contexts.
    cut-assoc : ∀ {P Q R S T U c d}
      (f : Arrow P (Q ⊗ port c)) (g : Arrow (port c ⊗ R) (S ⊗ port d))
      (h : Arrow (port d ⊗ T) U) (x : Values ((P ⊗ R) ⊗ T)) →
      associate {Q} {S} {U}
        (cut {P ⊗ R} {Q ⊗ S} {T} {U} {d}
          (λ xr → unassociate {Q} {S} {port d} (cut {P} {Q} {R} {S ⊗ port d} {c} f g xr)) h x)
      ≡ cut {P} {Q} {R ⊗ T} {S ⊗ U} {c} f
          (λ crt → cut {port c ⊗ R} {S} {T} {U} {d} g h
            (unassociate {port c} {R} {T} crt)) (associate {P} {R} {T} x)
    cut-assoc f g h ((x , r) , t) = refl

open PortSemantics public

-- Every typed operation acts on code values over ⋆. Its source ports determine
-- the arity of its T0 operation. The tensor groups simultaneous result ports.
module T1 {Sym : Set} (_≟_ : Decidable (_≡_ {A = Sym})) where
  module P = Over _≟_
  open Poly (Colored Sym) public
  open Guard _≟_ public

  bases : Ports → List BasePt
  bases empty = []
  bases (port _) = [ ⋆ ]
  bases (xs ⊗ ys) = bases xs ++ bases ys

  record Lifted (xs ys : Ports) (op : BasePolyOp (bases xs) ⋆) : Set where
    constructor liftOp
    field apply : Arrow xs ys

  split : Lifted (port MixMod) (port SharedBase ⊗ port SweetMod ⊗ port ExoMod) splitOp
  split = liftOp λ { (m , _) →
    (P.computeSharedBase m , P.shared-color m) ,
    (P.leanLane m , P.lean-color m) , (P.agdaLane m , P.agda-color m) }

  glue : Lifted (port SharedBase ⊗ port SweetMod ⊗ port ExoMod) (port MixMod) gluePushoutOp
  glue = liftOp λ { ((b , _) , (l , _) , (r , _)) →
    let m = P.pushoutGlue b l r in m , closed m , (λ _ → tt) }

  project : List Sym → Lifted (port MixMod) (port ExoMod) projectShellOp
  project seeds = liftOp λ { (m , _) → P.projectUpstreamShell m seeds ,
    P.shell-closed m seeds , P.shell-no-fast-bodies m seeds }

  -- A checker supplies evidence for the very slice and transitive footprint
  -- being discharged. The theorem is parametric in that external judgment.
  record ExoDischarge (SafeCheck : CodePoint Sym → List (AxiomTag Sym) → Set)
                      (s : Sym) (footprint : List (AxiomTag Sym)) : Set where
    field
      residual : CodePoint Sym
      color : HasSliceColor ExoMod residual
      resolves : ∃ λ d → d ∈ entries residual × entrySym d ≡ s × entrySort d ≡ exoBodyDecl
      safelyChecked : SafeCheck residual footprint
      footprintClean : CleanFootprint footprint

  hybrid-gluing-sound : ∀ {SafeCheck} allowed lean footprint →
    guardAxiomsAssuming allowed lean ≡ true →
    (∀ s → s ∈ allowed → ExoDischarge SafeCheck s (footprint s)) →
    CleanFootprint (lean ++ Data.List.Base.concatMap footprint allowed)
  hybrid-gluing-sound allowed lean footprint ok discharges =
    guard-glue-sound allowed lean footprint ok
      (λ s member → ExoDischarge.footprintClean (discharges s member))

-- Expressions remain available in the source fiber even on erased ports.
-- The concrete IR supplies the family of annotated expression/parameter values.
data T1Color : Set where
  moduleColor : SliceColor → T1Color
  portColor : EvalColor → T1Color

module TotalPorts (Sym : Set) (PortIR : EvalColor → Set) where
  Fiber : T1Color → Set
  Fiber (moduleColor c) = Colored Sym c
  Fiber (portColor c) = PortIR c
  open Poly Fiber public
