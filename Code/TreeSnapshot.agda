{-# OPTIONS --guardedness #-}
module Code.TreeSnapshot where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Ownership using (Name; Model; Models)
open import Code.Tree
open import Code.NodeTransport using (Frozen; frozen)

freezeHome : (sh : HomeShape) → Model (HomeSt sh) → Frozen
freezeHome (node ks) m with leavesOf ks m
... | c , mem , ds , _ = frozen c mem ds (forest ks m)
  where
    forest : (ks : List (Name × HomeShape)) → Models (KidsCtx ks ++ Leaves) → List (Name × Frozen)
    forest [] m = []
    forest ((n , sh) ∷ ks) (h , rest) = (n , freezeHome sh h) ∷ forest ks rest

thawHome : Frozen → Σ HomeShape (λ sh → Model (HomeSt sh))
thawHome (frozen c mem ds ks) = assemble ks
  where
    assemble : List (Name × Frozen) → Σ HomeShape (λ sh → Model (HomeSt sh))
    assemble [] = node [] , c , mem , ds , tt
    assemble ((n , h) ∷ rest) with thawHome h | assemble rest
    ... | sh , child | node js , m = node ((n , sh) ∷ js) , child , m

open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; subst)
open import Ownership using (Prog; Dir; focus; done)

plantFrozenAt : ∀ {Ψ n Γ} (p : Prefix) (sh : HomeShape) → Clean sh → Model (HomeSt sh) →
                Prog Ψ (Dir (plug p ((n , Dir []) ∷ Γ))) (Dir (plug p ((n , HomeSt sh) ∷ Γ))) Data.Unit.⊤
plantFrozenAt {Ψ} {n} {Γ} p sh clean m = focus (at p (here refl))
  (subst (λ s → Prog Ψ s (HomeSt sh) Data.Unit.⊤) (sym (at-state p (here refl))) (plantHome sh clean m)) λ _ →
  subst (λ Δ → Prog Ψ (Dir Δ) (Dir (plug p ((n , HomeSt sh) ∷ Γ))) Data.Unit.⊤)
    (sym (at-set p (here refl) _)) (done Data.Unit.tt)
