{-# OPTIONS --guardedness #-}
module Code.Tree where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; trans; inspect; [_])
open import Ownership hiding (Home)
open import Code using (Code; Decl)
open import Code.Transport using (Memory)
open import Code.Shape public

Interface : Set
Interface = List Decl

Leaves : Ctx
Leaves = ("code" , File Code) ∷ ("memory" , File Memory) ∷ ("spec" , File Interface) ∷ []

Home : Ctx → Ctx
Home kids = kids ++ Leaves

HomeSt : HomeShape → St
HomeCtx : HomeShape → Ctx
KidsCtx : List (Name × HomeShape) → Ctx
HomeSt sh = Dir (Home (HomeCtx sh))
HomeCtx (node ks) = KidsCtx ks
KidsCtx [] = []
KidsCtx ((n , sh) ∷ ks) = (n , HomeSt sh) ∷ KidsCtx ks

homeDroppable : (sh : HomeShape) → Droppable (HomeSt sh)
kidsDroppable : (ks : List (Name × HomeShape)) → DroppableAll (KidsCtx ks ++ Leaves)
homeDroppable (node ks) = kidsDroppable ks
kidsDroppable [] = tt , tt , tt , tt
kidsDroppable ((n , sh) ∷ ks) = homeDroppable sh , kidsDroppable ks

-- A zipper prefix makes traversal of a changing suffix definitionally stable.
data Prefix : Set₁ where
  root : Prefix
  push : (Name × St) → Prefix → Prefix

plug : Prefix → Ctx → Ctx
plug root Γ = Γ
plug (push e p) Γ = plug p (e ∷ Γ)

at : ∀ {n Γ} (p : Prefix) → n ↦ Γ → n ↦ plug p Γ
at root x = x
at (push e p) x = at p (there x)

at-state : ∀ {n Γ} (p : Prefix) (x : n ↦ Γ) → stateOf (at p x) ≡ stateOf x
at-state root x = refl
at-state (push e p) x = at-state p (there x)

at-set : ∀ {n Γ} (p : Prefix) (x : n ↦ Γ) (s : St) → set (at p x) s ≡ plug p (set x s)
at-set root x s = refl
at-set (push e p) x s = at-set p (there x) s

at-remove : ∀ {n Γ} (p : Prefix) (x : n ↦ Γ) → remove (at p x) ≡ plug p (remove x)
at-remove root x = refl
at-remove (push e p) x = at-remove p (there x)

castP : ∀ {Ψ Γ Δ S} → Γ ≡ Δ → Proc Ψ Γ S → Proc Ψ Δ S
castP refl p = p

stopHead : ∀ {Ψ Q R I F n Γ S} (p : Prefix)
         → ((i : I) → Proc Ψ (plug p ((n , F i) ∷ Γ)) S)
         → Proc Ψ (plug p ((n , Chan (SrvI Q R I F)) ∷ Γ)) S
stopHead p k = stopP (at p (here refl)) (at-state p (here refl)) λ i →
  castP (sym (at-set p (here refl) _)) (k i)

dropHead : ∀ {Ψ n s Γ S} (p : Prefix) → Droppable s → Proc Ψ (plug p Γ) S
         → Proc Ψ (plug p ((n , s) ∷ Γ)) S
dropHead p d k = run (dropAs (at p (here refl)) _ (at-state p (here refl)) d) λ _ →
  castP (sym (at-remove p (here refl))) k

readHead : ∀ {Ψ n A Γ} (p : Prefix)
         → Prog Ψ (Dir (plug p ((n , File A) ∷ Γ))) (Dir (plug p ((n , File A) ∷ Γ))) A
readHead {Ψ} {n} {A} {Γ} p = focus (at p (here refl))
  (subst (λ s → Prog Ψ s (File A) A) (sym (at-state p (here refl))) read)
  λ a → subst (λ Δ → Prog Ψ (Dir Δ) (Dir (plug p ((n , File A) ∷ Γ))) A)
    (sym (at-set p (here refl) (File A))) (done a)

import Data.List.Relation.Binary.Permutation.Propositional as Perm

front : (p : Prefix) (e : Name × St) (Γ : Ctx) → (e ∷ plug p Γ) Perm.↭ plug p (e ∷ Γ)
front root e Γ = Perm.refl
front (push x p) e Γ = Perm.trans (front p e (x ∷ Γ)) (under p (Perm.swap e x Perm.refl))
  where
    under : ∀ {Γ Δ} (p : Prefix) → Γ Perm.↭ Δ → plug p Γ Perm.↭ plug p Δ
    under root q = q
    under (push x p) q = under p (Perm.prep x q)

replaceHead : ∀ {Ψ n A Γ} (p : Prefix) → A
            → Prog Ψ (Dir (plug p ((n , File A) ∷ Γ))) (Dir (plug p ((n , File A) ∷ Γ))) Bool
replaceHead {Ψ} {n} {A} {Γ} p a with member n (plug p Γ) | inspect (member n) (plug p Γ)
... | true | [ eq ] = done false
... | false | [ eq ] =
  step (castCmd refl (cong Dir (at-remove p (here refl)))
    (Raw.unlink (at p (here refl)) (subst IsFile (sym (at-state p (here refl))) tt))) λ _ →
  step (Raw.create n (¬member n (plug p Γ) (subst (λ b → T (not b)) (sym eq) tt)) a) λ _ →
  step (Raw.reorder (front p (n , File A) Γ)) λ _ → done true

set-same : ∀ {n Γ} (x : n ↦ Γ) → set x (stateOf x) ≡ Γ
set-same (here _) = refl
set-same (there x) = cong (_ ∷_) (set-same x)

callAt : ∀ {Ψ n Γ Q R I F} (x : n ↦ Γ) → stateOf x ≡ Chan (SrvI Q R I F) → Q
       → Prog Ψ (Dir Γ) (Dir Γ) R
callAt x e q = step (castCmd refl (cong Dir (trans (cong (set x) (sym e)) (set-same x))) (Raw.call x e q)) done

focusSame : ∀ {Ψ n Γ A} (x : n ↦ Γ) → Prog Ψ (stateOf x) (stateOf x) A
          → Prog Ψ (Dir Γ) (Dir Γ) A
focusSame {Ψ} {Γ = Γ} {A = A} x p = focus x p λ a →
  subst (λ Δ → Prog Ψ (Dir Δ) (Dir Γ) A) (sym (set-same x)) (done a)

snapshotHome : ∀ {Ψ} (sh : HomeShape) → Prog Ψ (HomeSt sh) (HomeSt sh) (Model (HomeSt sh))
snapshotKids : ∀ {Ψ} (p : Prefix) (ks : List (Name × HomeShape))
             → Prog Ψ (Dir (plug p (KidsCtx ks ++ Leaves))) (Dir (plug p (KidsCtx ks ++ Leaves))) (Models (KidsCtx ks ++ Leaves))
snapshotHome (node ks) = snapshotKids root ks
snapshotKids p [] = do
  c ← readHead p
  m ← readHead (push ("code" , File Code) p)
  i ← readHead (push ("memory" , File Memory) (push ("code" , File Code) p))
  done (c , m , i , tt)
snapshotKids {Ψ} p ((n , sh) ∷ ks) = do
  h ← focusSame (at p (here refl))
    (subst (λ s → Prog Ψ s s (Model (HomeSt sh))) (sym (at-state p (here refl))) (snapshotHome sh))
  hs ← snapshotKids (push (n , HomeSt sh) p) ks
  done (h , hs)

leavesOf : (ks : List (Name × HomeShape)) → Models (KidsCtx ks ++ Leaves) → Models Leaves
leavesOf [] m = m
leavesOf ((n , sh) ∷ ks) (_ , ms) = leavesOf ks ms

codeOf : (sh : HomeShape) → Model (HomeSt sh) → Code
codeOf (node ks) m = Data.Product.proj₁ (leavesOf ks m)

memoryOf : (sh : HomeShape) → Model (HomeSt sh) → Memory
memoryOf (node ks) m = Data.Product.proj₁ (Data.Product.proj₂ (leavesOf ks m))

codesOf : (sh : HomeShape) → Model (HomeSt sh) → List Code
forestCodes : (ks : List (Name × HomeShape)) → Models (KidsCtx ks ++ Leaves) → List Code
codesOf sh m = codeOf sh m ∷ forestCodes′ sh m
  where
    forestCodes′ : (sh : HomeShape) → Model (HomeSt sh) → List Code
    forestCodes′ (node ks) m = forestCodes ks m
forestCodes [] m = []
forestCodes ((n , sh) ∷ ks) (h , hs) = codesOf sh h ++ forestCodes ks hs

openHead : ∀ {Ψ n Γ m} (p : Prefix) (h : m ↦ₛ Ψ) (i : idxOf h)
         → Prog Ψ (Dir (plug p ((n , Dir (ctxAt h i)) ∷ Γ)))
                  (Dir (plug p ((n , Chan (sessionAt h i)) ∷ Γ))) ⊤
openHead {Ψ} {n} {Γ} p h i =
  exec x (subst IsDir (sym e) tt) h i (sym (cong children e))
    (subst (λ Δ → Prog Ψ (Dir Δ) (Dir (plug p ((n , Chan (sessionAt h i)) ∷ Γ))) ⊤)
      (sym (at-set p (here refl) _)) (done tt))
  where
    x = at p (here refl)
    e : stateOf x ≡ Dir (ctxAt h i)
    e = at-state p (here refl)

sendHead : ∀ {Ψ n Γ A S} (p : Prefix) → A
         → Prog Ψ (Dir (plug p ((n , Chan (Dat A ⊸ S)) ∷ Γ))) (Dir (plug p ((n , Chan S) ∷ Γ))) ⊤
sendHead p a = step (castCmd refl (cong Dir (at-set p (here refl) _))
  (Raw.sendD (at p (here refl)) (at-state p (here refl)) a)) done

insertDir : ∀ {Ψ Γ S} (p : Prefix) (n : Name)
          → Proc Ψ (plug p ((n , Dir []) ∷ Γ)) S
          → Proc Ψ (plug p Γ) S
          → Proc Ψ (plug p Γ) S
insertDir {Ψ} {Γ} p n yes no with member n (plug p Γ) | inspect (member n) (plug p Γ)
... | true | [ eq ] = no
... | false | [ eq ] = run (step (Raw.mkdir n (¬member n (plug p Γ) (subst (λ b → T (not b)) (sym eq) tt))) λ _ →
                   step (Raw.reorder (front p (n , Dir []) Γ)) done) λ _ → yes

plantLeaf : ∀ {Ψ} → Code → Memory → Interface → Prog Ψ (Dir []) (HomeSt (node [])) ⊤
plantLeaf c m i = do
  create "spec" i
  create "memory" m
  create "code" c

plantAt : ∀ {Ψ n Γ} (p : Prefix) → Code → Memory → Interface
        → Prog Ψ (Dir (plug p ((n , Dir []) ∷ Γ))) (Dir (plug p ((n , HomeSt (node [])) ∷ Γ))) ⊤
plantAt {Ψ} {n} {Γ} p c m i = focus (at p (here refl))
  (subst (λ s → Prog Ψ s (HomeSt (node [])) ⊤) (sym (at-state p (here refl))) (plantLeaf c m i)) λ _ →
  subst (λ Δ → Prog Ψ (Dir Δ) (Dir (plug p ((n , HomeSt (node [])) ∷ Γ))) ⊤)
    (sym (at-set p (here refl) _)) (done tt)

-- A certificate for rebuilding a plain-data snapshot using only create/mkdir.
-- Freshness is checked when a home enters the scheduler, never assumed.
Clean : HomeShape → Set
CleanKids : List (Name × HomeShape) → Set
Clean (node ks) = CleanKids ks
CleanKids [] = ⊤
CleanKids ((n , sh) ∷ ks) = T (not (member n (KidsCtx ks ++ Leaves))) × Clean sh × CleanKids ks

open import Data.Maybe using (Maybe; just; nothing)

certify : (sh : HomeShape) → Maybe (Clean sh)
certifyKids : (ks : List (Name × HomeShape)) → Maybe (CleanKids ks)
certify (node ks) = certifyKids ks
certifyKids [] = just tt
certifyKids ((n , sh) ∷ ks) with member n (KidsCtx ks ++ Leaves)
... | true = nothing
... | false with certify sh | certifyKids ks
... | just a | just b = just (tt , a , b)
... | _ | _ = nothing

plantHome : ∀ {Ψ} (sh : HomeShape) → Clean sh → Model (HomeSt sh) → Prog Ψ (Dir []) (HomeSt sh) ⊤
plantKids : ∀ {Ψ} (ks : List (Name × HomeShape)) → CleanKids ks → Models (KidsCtx ks ++ Leaves)
          → Prog Ψ (Dir []) (Dir (KidsCtx ks ++ Leaves)) ⊤
plantHome (node ks) = plantKids ks
plantKids [] _ (c , m , i , _) = plantLeaf c m i
plantKids {Ψ} ((n , sh) ∷ ks) (fresh , a , b) (h , hs) =
  plantKids ks b hs >> step (Raw.mkdir n (¬member n (KidsCtx ks ++ Leaves) fresh)) λ _ →
  focus (here refl) (plantHome sh a h) done
