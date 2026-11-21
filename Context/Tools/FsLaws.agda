{-# OPTIONS --safe #-}
module Context.Tools.FsLaws where

import Data.Char.Properties as CP
open import Agda.Builtin.String.Properties using (primStringToListInjective)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (toℕ to octet)
import Data.Fin.Properties as FP
open import Data.List using (List; []; _∷_; _++_; reverse)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Context.Terminal using (Byte; Bytes)
open import Context.Tools.FsSandbox
open import Context.World using
  ( FsError; fsNotFound; fsIsDirectory
  ; hasDotSlashPrefix; normalizeRelPath; readVirtualFile; writeVirtualFile )

------------------------------------------------------------------------
-- §1 Reflective Equality Laws for `ℕ`, `Byte`, `Bytes`, `Char`, `String`
------------------------------------------------------------------------

≡ᵇ-refl : ∀ (n : ℕ) → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≡ᵇ⇒≡ : ∀ (m n : ℕ) → (m ≡ᵇ n) ≡ true → m ≡ n
≡ᵇ⇒≡ zero    zero    _  = refl
≡ᵇ⇒≡ (suc m) (suc n) eq = cong suc (≡ᵇ⇒≡ m n eq)

≢⇒≡ᵇ≡false : ∀ (m n : ℕ) → (m ≡ n → ⊥) → (m ≡ᵇ n) ≡ false
≢⇒≡ᵇ≡false m n neq with m ≡ᵇ n in eq
... | false = refl
... | true  = ⊥-elim (neq (≡ᵇ⇒≡ m n eq))

eqBytes-refl : ∀ (bs : Bytes) → eqBytes bs bs ≡ true
eqBytes-refl []       = refl
eqBytes-refl (b ∷ bs) rewrite ≡ᵇ-refl (octet b) = eqBytes-refl bs

eqBytes⇒≡ : ∀ (xs ys : Bytes) → eqBytes xs ys ≡ true → xs ≡ ys
eqBytes⇒≡ []       []       _  = refl
eqBytes⇒≡ (x ∷ xs) (y ∷ ys) eq with octet x ≡ᵇ octet y in eqHead
... | true = cong₂ _∷_ (FP.toℕ-injective (≡ᵇ⇒≡ (octet x) (octet y) eqHead)) (eqBytes⇒≡ xs ys eq)

eqChars-refl : ∀ (cs : List Char) → eqChars cs cs ≡ true
eqChars-refl []       = refl
eqChars-refl (c ∷ cs) rewrite ≡ᵇ-refl (toℕ c) = eqChars-refl cs

eqChars⇒≡ : ∀ (xs ys : List Char) → eqChars xs ys ≡ true → xs ≡ ys
eqChars⇒≡ []       []       _  = refl
eqChars⇒≡ (x ∷ xs) (y ∷ ys) eq with toℕ x ≡ᵇ toℕ y in eqHead
... | true = cong₂ _∷_ (CP.toℕ-injective x y (≡ᵇ⇒≡ (toℕ x) (toℕ y) eqHead)) (eqChars⇒≡ xs ys eq)

eqStr-refl : ∀ (s : String) → eqStr s s ≡ true
eqStr-refl s = eqChars-refl (toList s)

eqStr⇒≡ : ∀ (a b : String) → eqStr a b ≡ true → a ≡ b
eqStr⇒≡ a b eq = primStringToListInjective a b (eqChars⇒≡ (toList a) (toList b) eq)

≢Str⇒eqStr≡false : ∀ (a b : String) → (a ≡ b → ⊥) → eqStr a b ≡ false
≢Str⇒eqStr≡false a b neq with eqStr a b in eq
... | false = refl
... | true  = ⊥-elim (neq (eqStr⇒≡ a b eq))

≢⇒eqStr≡false : ∀ (a b : String) → (a ≡ b → ⊥) → eqStr a b ≡ false
≢⇒eqStr≡false = ≢Str⇒eqStr≡false

eqStr-sym : ∀ (a b : String) → eqStr a b ≡ eqStr b a
eqStr-sym a b with eqStr a b in eqAB | eqStr b a in eqBA
... | true  | true  = refl
... | false | false = refl
... | true  | false = ⊥-elim (false≢true (trans (sym eqBA) (trans (cong (λ x → eqStr b x) (eqStr⇒≡ a b eqAB)) (eqStr-refl b))))
  where false≢true : false ≡ true → ⊥ ; false≢true ()
... | false | true  = ⊥-elim (false≢true (trans (sym eqAB) (trans (cong (λ x → eqStr a x) (eqStr⇒≡ b a eqBA)) (eqStr-refl a))))
  where false≢true : false ≡ true → ⊥ ; false≢true ()

------------------------------------------------------------------------
-- §2 Universal Entry-Map Lens Laws (`GetPut`, `PutPut`, `Frame`)
------------------------------------------------------------------------

lookup-insert-same : ∀ (e : FsEntryObs) (es : List FsEntryObs) →
  lookupEntry (entryPath e) (insertEntry e es) ≡ just e
lookup-insert-same e [] rewrite eqStr-refl (entryPath e) = refl
lookup-insert-same e (x ∷ xs) with eqStr (entryPath e) (entryPath x) in eqP
... | true  rewrite eqStr-refl (entryPath e) = refl
... | false with ltBytes (Context.Terminal.bytes (entryPath e)) (Context.Terminal.bytes (entryPath x))
...   | true  rewrite eqStr-refl (entryPath e) = refl
...   | false rewrite eqP = lookup-insert-same e xs

lookup-insert-other : ∀ (q : String) (e : FsEntryObs) (es : List FsEntryObs) →
  (q ≡ entryPath e → ⊥) →
  lookupEntry q (insertEntry e es) ≡ lookupEntry q es
lookup-insert-other q e [] neq with eqStr q (entryPath e) in eqQE
... | false = refl
... | true  = ⊥-elim (neq (eqStr⇒≡ q (entryPath e) eqQE))
lookup-insert-other q e (x ∷ xs) neq with eqStr (entryPath e) (entryPath x) in eqEX
... | true with eqStr q (entryPath e) in eqQE | eqStr q (entryPath x) in eqQX
...   | true  | _     = ⊥-elim (neq (eqStr⇒≡ q (entryPath e) eqQE))
...   | false | true  = ⊥-elim (neq (trans (eqStr⇒≡ q (entryPath x) eqQX) (sym (eqStr⇒≡ (entryPath e) (entryPath x) eqEX))))
...   | false | false = refl
lookup-insert-other q e (x ∷ xs) neq | false with ltBytes (Context.Terminal.bytes (entryPath e)) (Context.Terminal.bytes (entryPath x))
... | true with eqStr q (entryPath e) in eqQE
...   | true  = ⊥-elim (neq (eqStr⇒≡ q (entryPath e) eqQE))
...   | false = refl
lookup-insert-other q e (x ∷ xs) neq | false | false with eqStr q (entryPath x)
... | true  = refl
... | false = lookup-insert-other q e xs neq

insert-insert-same : ∀ (e₁ e₂ : FsEntryObs) (es : List FsEntryObs) →
  entryPath e₁ ≡ entryPath e₂ →
  insertEntry e₂ (insertEntry e₁ es) ≡ insertEntry e₂ es
insert-insert-same e₁ e₂ [] pEq rewrite sym pEq | eqStr-refl (entryPath e₁) = refl
insert-insert-same e₁ e₂ (x ∷ xs) pEq with eqStr (entryPath e₁) (entryPath x) in eq1X
... | true  rewrite sym pEq | eq1X | eqStr-refl (entryPath e₁) = refl
... | false with ltBytes (Context.Terminal.bytes (entryPath e₁)) (Context.Terminal.bytes (entryPath x)) in lt1X
...   | true  rewrite sym pEq | eq1X | lt1X | eqStr-refl (entryPath e₁) = refl
...   | false rewrite sym pEq | eq1X | lt1X = cong (x ∷_) (insert-insert-same e₁ e₂ xs pEq)

------------------------------------------------------------------------
-- §3 High-Level `VirtualFs` File Read/Write Lens & Frame Laws (`∀ p q bs v`)
------------------------------------------------------------------------

noSlashOrNull : List Char → Bool
noSlashOrNull []       = true
noSlashOrNull (c ∷ cs) = not (toℕ c ≡ᵇ 47) ∧ not (toℕ c ≡ᵇ 0) ∧ noSlashOrNull cs

ValidFlatFile : String → Bool
ValidFlatFile p = validSegChars (toList p) ∧ noSlashOrNull (toList p)

isWritableEntry : Maybe FsEntryObs → Bool
isWritableEntry nothing  = true
isWritableEntry (just e) = eqKind (entryKind e) regularNode

CanWriteReg : String → VirtualFs → Bool
CanWriteReg p v = isWritableEntry (lookupEntry p (fsEntries v))

isNotSymlinkEntry : Maybe FsEntryObs → Bool
isNotSymlinkEntry nothing  = true
isNotSymlinkEntry (just e) = not (eqKind (entryKind e) symlinkNode)

NotSymlink : String → VirtualFs → Bool
NotSymlink p v = isNotSymlinkEntry (lookupEntry p (fsEntries v))

private
  and-left : ∀ (a b : Bool) → (a ∧ b) ≡ true → a ≡ true
  and-left true  _ _  = refl
  and-left false _ ()

  and-right : ∀ (a b : Bool) → (a ∧ b) ≡ true → b ≡ true
  and-right true  _ h  = h
  and-right false _ ()

  not-dot : ∀ (cs : List Char) → validSegChars cs ≡ true → eqChars cs ('.' ∷ []) ≡ false
  not-dot cs h with eqChars cs [] | eqChars cs ('.' ∷ [])
  ... | true  | _    = ⊥-elim (false≢true h) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | true = ⊥-elim (false≢true h) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | false = refl

  noSlash-split : ∀ (acc cs : List Char) → noSlashOrNull cs ≡ true →
    splitSegmentChars acc cs ≡ (reverse acc ++ cs) ∷ []
  noSlash-split acc [] _ rewrite LP.++-identityʳ (reverse acc) = refl
  noSlash-split acc (c ∷ cs) ok with toℕ c ≡ᵇ 47 | toℕ c ≡ᵇ 0
  ... | true  | _     = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | false = trans (noSlash-split (c ∷ acc) cs ok) (cong (_∷ []) (rev-step acc c cs))
    where
      rev-step : ∀ (a : List Char) (x : Char) (ys : List Char) →
        (reverse (x ∷ a) ++ ys) ≡ (reverse a ++ (x ∷ ys))
      rev-step a x ys rewrite LP.unfold-reverse x a | LP.++-assoc (reverse a) (x ∷ []) ys = refl

  noSlash-noNull : ∀ (cs : List Char) → noSlashOrNull cs ≡ true →
    all (λ c → not (toℕ c ≡ᵇ 0)) cs ≡ true
  noSlash-noNull [] _ = refl
  noSlash-noNull (c ∷ cs) ok with toℕ c ≡ᵇ 47 | toℕ c ≡ᵇ 0
  ... | true  | _     = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | false = noSlash-noNull cs ok

  noSlash-noDotSlash : ∀ (cs : List Char) → noSlashOrNull cs ≡ true → hasDotSlashPrefix cs ≡ false
  noSlash-noDotSlash []             _  = refl
  noSlash-noDotSlash (_ ∷ [])       _  = refl
  noSlash-noDotSlash (c₁ ∷ c₂ ∷ _) ok with toℕ c₁ ≡ᵇ 47 | toℕ c₁ ≡ᵇ 0 | toℕ c₂ ≡ᵇ 47
  ... | true  | _     | _     = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | true  | _     = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | false | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | false | false with toℕ c₁ ≡ᵇ 46
  ...   | false = refl
  ...   | true  = refl

  flat-segOk : ∀ (p : String) → ValidFlatFile p ≡ true → validSegChars (toList p) ≡ true
  flat-segOk p = and-left (validSegChars (toList p)) (noSlashOrNull (toList p))

  flat-nsOk : ∀ (p : String) → ValidFlatFile p ≡ true → noSlashOrNull (toList p) ≡ true
  flat-nsOk p = and-right (validSegChars (toList p)) (noSlashOrNull (toList p))

  flat-normalize : ∀ (p : String) → ValidFlatFile p ≡ true → normalizeRelPath p ≡ p
  flat-normalize p ok rewrite noSlash-noDotSlash (toList p) (flat-nsOk p ok) = refl

  flat-validRelPath : ∀ (p : String) → ValidFlatFile p ≡ true → validRelPath p ≡ true
  flat-validRelPath p ok
    rewrite noSlash-split [] (toList p) (flat-nsOk p ok)
          | noSlash-noNull (toList p) (flat-nsOk p ok)
    with validSegChars (toList p) | flat-segOk p ok
  ... | true  | _  = refl
  ... | false | ()

  flat-parentPaths : ∀ (p : String) → ValidFlatFile p ≡ true → parentPaths p ≡ []
  flat-parentPaths p ok rewrite noSlash-split [] (toList p) (flat-nsOk p ok) = refl

-- Law 1 (`PutGet` / Read-After-Write): Writing `bs` to `p` and reading `p` returns `inj₂ bs`!
read-after-write-same : ∀ (p : String) (bs : Bytes) (v : VirtualFs) →
  ValidFlatFile p ≡ true →
  CanWriteReg p v ≡ true →
  readVirtualFile p (proj₂ (writeVirtualFile p bs v)) ≡ inj₂ bs
read-after-write-same p bs v flatOk canOk
  rewrite flat-normalize p flatOk
        | not-dot (toList p) (flat-segOk p flatOk)
        | flat-validRelPath p flatOk
        | flat-parentPaths p flatOk with lookupEntry p (fsEntries v)
... | nothing rewrite flat-normalize p flatOk
                    | not-dot (toList p) (flat-segOk p flatOk)
                    | flat-validRelPath p flatOk
                    | lookup-insert-same (fsEntry p regularNode 420 bs) (fsEntries v) = refl
... | just e with entryKind e
...   | regularNode rewrite flat-normalize p flatOk
                          | not-dot (toList p) (flat-segOk p flatOk)
                          | flat-validRelPath p flatOk
                          | lookup-insert-same (fsEntry p regularNode (entryMode e) bs) (fsEntries v) = refl
...   | dirNode     = ⊥-elim (false≢true canOk) where false≢true : false ≡ true → ⊥ ; false≢true ()
...   | symlinkNode = ⊥-elim (false≢true canOk) where false≢true : false ≡ true → ⊥ ; false≢true ()

-- Law 2 (`Frame` / Distinct-Path Non-Interference): Writing `p` leaves reading `q ≢ p` unchanged!
read-after-write-other : ∀ (p q : String) (bs : Bytes) (v : VirtualFs) →
  ValidFlatFile p ≡ true →
  ValidFlatFile q ≡ true →
  (q ≡ p → ⊥) →
  CanWriteReg p v ≡ true →
  NotSymlink q v ≡ true →
  readVirtualFile q (proj₂ (writeVirtualFile p bs v)) ≡ readVirtualFile q v
read-after-write-other p q bs v flatP flatQ q≢p canP noSymQ
  rewrite flat-normalize p flatP
        | not-dot (toList p) (flat-segOk p flatP)
        | flat-validRelPath p flatP
        | flat-parentPaths p flatP with lookupEntry p (fsEntries v)
... | nothing rewrite flat-normalize q flatQ
                    | not-dot (toList q) (flat-segOk q flatQ)
                    | flat-validRelPath q flatQ
                    | lookup-insert-other q (fsEntry p regularNode 420 bs) (fsEntries v) q≢p
    with lookupEntry q (fsEntries v)
...   | nothing = refl
...   | just eqE with entryKind eqE
...     | regularNode = refl
...     | dirNode     = refl
...     | symlinkNode = ⊥-elim (false≢true noSymQ) where false≢true : false ≡ true → ⊥ ; false≢true ()
read-after-write-other p q bs v flatP flatQ q≢p canP noSymQ | just ep with entryKind ep
... | regularNode rewrite flat-normalize q flatQ
                        | not-dot (toList q) (flat-segOk q flatQ)
                        | flat-validRelPath q flatQ
                        | lookup-insert-other q (fsEntry p regularNode (entryMode ep) bs) (fsEntries v) q≢p
    with lookupEntry q (fsEntries v)
...   | nothing = refl
...   | just eqE with entryKind eqE
...     | regularNode = refl
...     | dirNode     = refl
...     | symlinkNode = ⊥-elim (false≢true noSymQ) where false≢true : false ≡ true → ⊥ ; false≢true ()
read-after-write-other p q bs v flatP flatQ q≢p canP noSymQ | just ep | dirNode =
  ⊥-elim (false≢true canP) where false≢true : false ≡ true → ⊥ ; false≢true ()
read-after-write-other p q bs v flatP flatQ q≢p canP noSymQ | just ep | symlinkNode =
  ⊥-elim (false≢true canP) where false≢true : false ≡ true → ⊥ ; false≢true ()
