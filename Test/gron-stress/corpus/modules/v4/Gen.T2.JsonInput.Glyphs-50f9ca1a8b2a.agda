module Gen.T2.JsonInput.Glyphs where

open import Agda.Builtin.Char using (primCharEquality; primNatToChar)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; [_]; any; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; fromList) renaming (_++_ to _++ˢ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

private
  choose : {A : Set} → Bool → A → A → A
  choose true x y = x
  choose false x y = y

  andLeft : (x y : Bool) → (x ∧ y) ≡ true → x ≡ true
  andLeft true y p = refl
  andLeft false y ()

  andRight : (x y : Bool) → (x ∧ y) ≡ true → y ≡ true
  andRight true y p = p
  andRight false y ()

  orTrue : {A : Set} → (x y : Bool) → (x ∨ y) ≡ true → (x ≡ true → A) → (y ≡ true → A) → A
  orTrue true y p left right = left refl
  orTrue false y p left right = right p

  orLeftFalse : (x y : Bool) → (x ∨ y) ≡ false → x ≡ false
  orLeftFalse true y ()
  orLeftFalse false y p = refl

  orRightFalse : (x y : Bool) → (x ∨ y) ≡ false → y ≡ false
  orRightFalse true y ()
  orRightFalse false y p = p

  lessTrans : (a b c : ℕ) → (a <ᵇ b) ≡ true → (b <ᵇ c) ≡ true → (a <ᵇ c) ≡ true
  lessTrans zero zero c () q
  lessTrans (suc a) zero c () q
  lessTrans zero (suc b) zero p ()
  lessTrans (suc a) (suc b) zero p ()
  lessTrans zero (suc b) (suc c) p q = refl
  lessTrans (suc a) (suc b) (suc c) p q = lessTrans a b c p q

  complementary : (b n : ℕ) → (n <ᵇ suc b) ≡ not (b <ᵇ n)
  complementary zero zero = refl
  complementary zero (suc zero) = refl
  complementary zero (suc (suc n)) = refl
  complementary (suc b) zero = refl
  complementary (suc b) (suc n) = complementary b n

  doubleNot : (x : Bool) → x ≡ not (not x)
  doubleNot true = refl
  doubleNot false = refl

  belowToAboveFalse : (b n : ℕ) → (n <ᵇ suc b) ≡ true → (b <ᵇ n) ≡ false
  belowToAboveFalse b n p =
    trans (doubleNot (b <ᵇ n)) (cong not (trans (sym (complementary b n)) p))

  aboveToBelowFalse : (b n : ℕ) → (b <ᵇ n) ≡ true → (n <ᵇ suc b) ≡ false
  aboveToBelowFalse b n p = trans (complementary b n) (cong not p)

  natEqual : (m n : ℕ) → (m ≡ᵇ n) ≡ true → m ≡ n
  natEqual zero zero p = refl
  natEqual zero (suc n) ()
  natEqual (suc m) zero ()
  natEqual (suc m) (suc n) p = cong suc (natEqual m n p)

  escaped : Char → List (Char × String) → String → String
  escaped c [] fallback = fallback
  escaped c ((key , value) ∷ rest) fallback =
    choose (primCharEquality c key) value (escaped c rest fallback)

  escapedMiss : (c : Char) → (entries : List (Char × String)) → (fallback : String) →
    any (primCharEquality c) (map proj₁ entries) ≡ false →
    escaped c entries fallback ≡ fallback
  escapedMiss c [] fallback p = refl
  escapedMiss c ((key , value) ∷ rest) fallback p =
    trans
      (cong (λ matched → choose matched value (escaped c rest fallback))
        (orLeftFalse (primCharEquality c key) (any (primCharEquality c) (map proj₁ rest)) p))
      (escapedMiss c rest fallback
        (orRightFalse (primCharEquality c key) (any (primCharEquality c) (map proj₁ rest)) p))

  printableEscapes : List (Char × String)
  printableEscapes = ('\'' , "\\'") ∷ ('\\' , "\\\\") ∷ []

  controlEscapes : List (Char × String)
  controlEscapes = (primNatToChar 7 , "\\a") ∷ (primNatToChar 8 , "\\b") ∷ ('	' , "\\t") ∷
    ('\n' , "\\n") ∷ (primNatToChar 11 , "\\v") ∷ (primNatToChar 12 , "\\f") ∷ ('\r' , "\\r") ∷ []

  printableRange : ℕ → Bool
  printableRange n = (31 <ᵇ n) ∧ (n <ᵇ 127)

  controlRange : ℕ → Bool
  controlRange n = (n <ᵇ 32) ∨ (n ≡ᵇ 127)

  controlBounds : (n : ℕ) → controlRange n ≡ true → ((127 <ᵇ n) ≡ false) × (printableRange n ≡ false)
  controlBounds n p = orTrue (n <ᵇ 32) (n ≡ᵇ 127) p
    (λ low → belowToAboveFalse 127 n (lessTrans n 32 128 low refl) ,
      cong (λ b → b ∧ (n <ᵇ 127)) (belowToAboveFalse 31 n low))
    (λ del → cong (λ m → 127 <ᵇ m) (natEqual n 127 del) ,
      cong printableRange (natEqual n 127 del))

  nibbleGlyph : ℕ → Bool → Char
  nibbleGlyph n decimal = choose decimal (primNatToChar (48 + n)) (primNatToChar (87 + n))

diagnosticNibble : ℕ → Char
diagnosticNibble n = nibbleGlyph n (n <ᵇ 10)

private
  hexGlyph : ℕ → String
  hexGlyph n = "\\x" ++ˢ fromList (diagnosticNibble (n / 16) ∷ (diagnosticNibble (n % 16) ∷ []))

  byteGlyph : ℕ → ℕ → String
  byteGlyph base payload = fromList ([ primNatToChar (base + payload) ])

  longerGlyph : ℕ → Bool → String
  longerGlyph n fourBytes =
    choose fourBytes (byteGlyph 240 (n / 262144)) (byteGlyph 224 (n / 4096))

  unicodeGlyph : ℕ → Bool → String
  unicodeGlyph n moreThanTwo =
    choose moreThanTwo (longerGlyph n (65535 <ᵇ n)) (byteGlyph 192 (n / 64))

  asciiGlyph : Char → Bool → String
  asciiGlyph c printable = choose printable
    (escaped c printableEscapes (fromList ([ c ])))
    (escaped c controlEscapes (hexGlyph (toℕ c)))

  selectGlyph : Char → Bool → String
  selectGlyph c unicode = choose unicode
    (unicodeGlyph (toℕ c) (2047 <ᵇ toℕ c))
    (asciiGlyph c (printableRange (toℕ c)))

diagnosticGlyph : Char → String
diagnosticGlyph c = selectGlyph c (127 <ᵇ toℕ c)

printableAscii : (c : _) → (((31 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 127)) ≡ true) → (primCharEquality c '\'' ≡ false) → (primCharEquality c '\\' ≡ false) → diagnosticGlyph c ≡ fromList ([ c ])
printableAscii c p a b =
  trans
    (cong (selectGlyph c)
      (belowToAboveFalse 127 (toℕ c)
        (lessTrans (toℕ c) 127 128 (andRight (31 <ᵇ toℕ c) (toℕ c <ᵇ 127) p) refl)))
    (trans (cong (asciiGlyph c) p)
      (escapedMiss c printableEscapes (fromList ([ c ]))
        (trans (cong (λ match → match ∨ (primCharEquality c '\\' ∨ false)) a)
          (cong (λ match → match ∨ false) b))))

apostropheGlyph : diagnosticGlyph '\'' ≡ "\\'"
apostropheGlyph = refl

backslashGlyph : diagnosticGlyph '\\' ≡ "\\\\"
backslashGlyph = refl

bellGlyph : diagnosticGlyph (primNatToChar 7) ≡ "\\a"
bellGlyph = refl

verticalTabGlyph : diagnosticGlyph (primNatToChar 11) ≡ "\\v"
verticalTabGlyph = refl

backspaceGlyph : diagnosticGlyph (primNatToChar 8) ≡ "\\b"
backspaceGlyph = refl

tabGlyph : diagnosticGlyph '	' ≡ "\\t"
tabGlyph = refl

newlineGlyph : diagnosticGlyph '\n' ≡ "\\n"
newlineGlyph = refl

formfeedGlyph : diagnosticGlyph (primNatToChar 12) ≡ "\\f"
formfeedGlyph = refl

returnGlyph : diagnosticGlyph '\r' ≡ "\\r"
returnGlyph = refl

decimalNibble : (n : _) → ((n <ᵇ 10) ≡ true) → diagnosticNibble n ≡ primNatToChar (48 + n)
decimalNibble n p = cong (nibbleGlyph n) p

alphabeticNibble : (n : _) → (((9 <ᵇ n) ∧ (n <ᵇ 16)) ≡ true) → diagnosticNibble n ≡ primNatToChar (87 + n)
alphabeticNibble n p = cong (nibbleGlyph n)
  (aboveToBelowFalse 9 n (andLeft (9 <ᵇ n) (n <ᵇ 16) p))

hexControlGlyph : (c : _) → (((toℕ c <ᵇ 32) ∨ (toℕ c ≡ᵇ 127)) ≡ true) → (any (primCharEquality c) (primNatToChar 7 ∷ (primNatToChar 8 ∷ ('	' ∷ ('\n' ∷ (primNatToChar 11 ∷ (primNatToChar 12 ∷ ('\r' ∷ []))))))) ≡ false) → diagnosticGlyph c ≡ ("\\x" ++ˢ fromList (diagnosticNibble (toℕ c / 16) ∷ (diagnosticNibble (toℕ c % 16) ∷ [])))
hexControlGlyph c p outside =
  trans (cong (selectGlyph c) (proj₁ (controlBounds (toℕ c) p)))
    (trans (cong (asciiGlyph c) (proj₂ (controlBounds (toℕ c) p)))
      (escapedMiss c controlEscapes (hexGlyph (toℕ c)) outside))

glyphTwoBytes : (c : _) → (((127 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 2048)) ≡ true) → diagnosticGlyph c ≡ fromList ([ primNatToChar (192 + (toℕ c / 64)) ])
glyphTwoBytes c p =
  trans (cong (selectGlyph c) (andLeft (127 <ᵇ toℕ c) (toℕ c <ᵇ 2048) p))
    (cong (unicodeGlyph (toℕ c))
      (belowToAboveFalse 2047 (toℕ c) (andRight (127 <ᵇ toℕ c) (toℕ c <ᵇ 2048) p)))

glyphThreeBytes : (c : _) → (((2047 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 65536)) ≡ true) → diagnosticGlyph c ≡ fromList ([ primNatToChar (224 + (toℕ c / 4096)) ])
glyphThreeBytes c p =
  trans
    (cong (selectGlyph c)
      (lessTrans 127 2047 (toℕ c) refl (andLeft (2047 <ᵇ toℕ c) (toℕ c <ᵇ 65536) p)))
    (trans (cong (unicodeGlyph (toℕ c)) (andLeft (2047 <ᵇ toℕ c) (toℕ c <ᵇ 65536) p))
      (cong (longerGlyph (toℕ c))
        (belowToAboveFalse 65535 (toℕ c) (andRight (2047 <ᵇ toℕ c) (toℕ c <ᵇ 65536) p))))

glyphFourBytes : (c : _) → ((65535 <ᵇ toℕ c) ≡ true) → diagnosticGlyph c ≡ fromList ([ primNatToChar (240 + (toℕ c / 262144)) ])
glyphFourBytes c p =
  trans (cong (selectGlyph c) (lessTrans 127 65535 (toℕ c) refl p))
    (trans (cong (unicodeGlyph (toℕ c)) (lessTrans 2047 65535 (toℕ c) refl p))
      (cong (longerGlyph (toℕ c)) p))
