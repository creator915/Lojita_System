module Gen.T1.Gron.Codec where

  open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
  open import Data.Char using (Char; toℕ; fromℕ)
  import Data.Char as Ch
  open import Data.List using (List; []; _∷_; _++_; all; map; foldr)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_; _≡ᵇ_)
  import Data.Nat.Show as Nat
  open import Data.Nat.DivMod using (_/_; _%_)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.String using (String; toList; fromList; _≟_) renaming (_++_ to _++ˢ_)
  open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
  open import Relation.Nullary using (Dec; yes; no)
  open import Data.Empty using (⊥)
  open import Data.Nat using (ℕ; _<ᵇ_; _≡ᵇ_)
  open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  data Notation : Set where
    assignments : Notation
    pairs : Notation
  data Ordering : Set where
    before : Ordering
    equal : Ordering
    after : Ordering
  data Shade : Set where
    name : Shade
    container : Shade
    numeral : Shade
    quoted : Shade
    constant : Shade
  data Listed (word : List Char) : List (List Char) → Set where
    first : {words : _} → Listed word (word ∷ words)
    later : {other : _} → {words : _} → Listed word words → Listed word (other ∷ words)
  record Parsed (A : Set) : Set where
    constructor parsed
    field
      value : A
      rest : List Char
  data Atom : Set where
    null : Atom
    boolean : Bool → Atom
    number : String → Atom
    text : String → Atom
  data Value : Set where
    scalar : Atom → Value
    array : List Value → Value
    object : List (String × Value) → Value
  data Segment : Set where
    property : String → Segment
    index : ℕ → Segment
  data Payload : Set where
    atom : Atom → Payload
    arrayMark : Payload
    objectMark : Payload
  record Statement : Set where
    constructor assignment
    field
      path : List Segment
      rhs : Payload
  private
    decision : {A : Set} → Dec A → Bool
    decision (yes _) = true
    decision (no _) = false
  private
    decisionYes : {A : Set} → (d : Dec A) → A → decision d ≡ true
    decisionYes (yes _) present = refl
    decisionYes (no absent) present = ⊥-elim (absent present)
  private
    decisionNo : {A : Set} → (d : Dec A) → (A → ⊥) → decision d ≡ false
    decisionNo (yes present) absent = ⊥-elim (absent present)
    decisionNo (no _) absent = refl
  hasKey : {V : Set} → String → List (String × V) → Bool
  hasKey k [] = false
  hasKey k ((j , v) ∷ xs) = decision (k ≟ j) ∨ hasKey k xs
  private
    keepHead : {V : Set} → String → V → List (String × V) → List (String × V)
    keepHead k v ys = if hasKey k ys then ys else ((k , v) ∷ ys)
  keepLatest : {V : Set} → List (String × V) → List (String × V)
  keepLatest [] = []
  keepLatest ((k , v) ∷ xs) = keepHead k v (keepLatest xs)
  hasKeyEmpty : {V : Set} → (k : _) → hasKey {V} k [] ≡ false
  hasKeyEmpty k = refl
  hasKeySame : {V : Set} → (k : _) → (v : _) → (xs : _) → hasKey {V} k ((k , v) ∷ xs) ≡ true
  hasKeySame k v xs = cong (λ b → b ∨ hasKey k xs) (decisionYes (k ≟ k) refl)
  hasKeyOther : {V : Set} → (k : _) → (j : _) → (v : _) → (xs : _) → (k ≢ j) → hasKey {V} k ((j , v) ∷ xs) ≡ hasKey k xs
  hasKeyOther k j v xs different = cong (λ b → b ∨ hasKey k xs) (decisionNo (k ≟ j) different)
  keepLatestEmpty : {V : Set} → keepLatest {V} [] ≡ []
  keepLatestEmpty = refl
  keepLatestNext : {V : Set} → (k : _) → (v : _) → (xs : _) → keepLatest {V} ((k , v) ∷ xs) ≡ (if hasKey k (keepLatest xs) then keepLatest xs else ((k , v) ∷ keepLatest xs))
  keepLatestNext k v xs = refl
  private
    hasKeyMap : {A D : Set} → (f : A → D) → (k : String) → (xs : List (String × A)) → hasKey k (map (λ kv → proj₁ kv , f (proj₂ kv)) xs) ≡ hasKey k xs
    hasKeyMap f k [] = refl
    hasKeyMap f k ((j , v) ∷ xs) = cong (λ b → decision (k ≟ j) ∨ b) (hasKeyMap f k xs)
  private
    mapChoice : {A D : Set} → (f : A → D) → (k : String) → (v : A) → (ys : List (String × A)) → (b : Bool) → map (λ kv → proj₁ kv , f (proj₂ kv)) (if b then ys else ((k , v) ∷ ys)) ≡ (if b then map (λ kv → proj₁ kv , f (proj₂ kv)) ys else ((k , f v) ∷ map (λ kv → proj₁ kv , f (proj₂ kv)) ys))
    mapChoice f k v ys true = refl
    mapChoice f k v ys false = refl
  keepLatestMap : {A D : Set} → (f : A → D) → (xs : List (String × A)) → map (λ kv → proj₁ kv , f (proj₂ kv)) (keepLatest xs) ≡ keepLatest (map (λ kv → proj₁ kv , f (proj₂ kv)) xs)
  keepLatestMap f [] = refl
  keepLatestMap f ((k , v) ∷ xs) = trans (mapChoice f k v (keepLatest xs) (hasKey k (keepLatest xs))) (trans (cong (λ b → if b then map (λ kv → proj₁ kv , f (proj₂ kv)) (keepLatest xs) else ((k , f v) ∷ map (λ kv → proj₁ kv , f (proj₂ kv)) (keepLatest xs))) (sym (hasKeyMap f k (keepLatest xs)))) (cong (keepHead k (f v)) (keepLatestMap f xs)))
  private
    Result : Set → Set
    Result A = String ⊎ Parsed A
  private
    mapParsed : {A B : Set} → (A → B) → Result A → Result B
    mapParsed f (inj₁ e) = inj₁ e
    mapParsed f (inj₂ (parsed a xs)) = inj₂ (parsed (f a) xs)
  private
    emit : List Char → Result (List Char) → Result (List Char)
    emit cs = mapParsed (λ tail → cs ++ tail)
  private
    incomplete : {A : Set} → Result A
    incomplete = inj₁ "unexpected EOF"
  private
    digitCode : ℕ → Bool
    digitCode n = (47 <ᵇ n) ∧ (n <ᵇ 58)
  private
    numberStart : Char → Bool
    numberStart c = (toℕ c ≡ᵇ 45) ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))
  private
    lowerHex : ℕ → Char
    lowerHex n = fromℕ (if (n <ᵇ 10) then (48 + n) else (87 + n))
  private
    firstByte : ℕ → ℕ
    firstByte n = if (n <ᵇ 128) then n else (if (n <ᵇ 2048) then (192 + (n / 64)) else (if (n <ᵇ 65536) then (224 + (n / 4096)) else (240 + (n / 262144))))
  private
    diagnosticBody : Char → List Char
    diagnosticBody '\'' = '\\' ∷ ('\'' ∷ [])
    diagnosticBody '\\' = '\\' ∷ ('\\' ∷ [])
    diagnosticBody '	' = '\\' ∷ ('t' ∷ [])
    diagnosticBody '\n' = '\\' ∷ ('n' ∷ [])
    diagnosticBody '\r' = '\\' ∷ ('r' ∷ [])
    diagnosticBody c = let n = toℕ c in if (n ≡ᵇ 7) then ('\\' ∷ ('a' ∷ [])) else (if (n ≡ᵇ 8) then ('\\' ∷ ('b' ∷ [])) else (if (n ≡ᵇ 11) then ('\\' ∷ ('v' ∷ [])) else (if (n ≡ᵇ 12) then ('\\' ∷ ('f' ∷ [])) else (if ((n <ᵇ 32) ∨ (n ≡ᵇ 127)) then ('\\' ∷ ('x' ∷ (lowerHex (n / 16) ∷ (lowerHex (n % 16) ∷ [])))) else (c ∷ [])))))
  private
    diagnostic : Char → String
    diagnostic c = "'" ++ˢ (fromList (diagnosticBody (fromℕ (firstByte (toℕ c)))) ++ˢ "'")
  private
    badCharacter : {A : Set} → Char → String → Result A
    badCharacter c context = inj₁ ("invalid character " ++ˢ (diagnostic c ++ˢ (" " ++ˢ context)))
  private
    data NumberState : Set where
      firstDigit : NumberState
      integerDigits : NumberState
      afterZero : NumberState
      firstFraction : NumberState
      fractionDigits : NumberState
      exponentSign : NumberState
      firstExponent : NumberState
      exponentDigits : NumberState
  private
    data NumberStep : Set where
      advance : NumberState → NumberStep
      finishToken : NumberStep
      reject : String → NumberStep
  private
    requireDigit : NumberState → String → Char → NumberStep
    requireDigit state message c = if digitCode (toℕ c) then advance state else reject message
  private
    exponentOrEnd : Char → NumberStep
    exponentOrEnd 'e' = advance exponentSign
    exponentOrEnd 'E' = advance exponentSign
    exponentOrEnd _ = finishToken
  private
    fractionOrEnd : Char → NumberStep
    fractionOrEnd '.' = advance firstFraction
    fractionOrEnd c = exponentOrEnd c
  private
    digitOr : NumberState → NumberStep → Char → NumberStep
    digitOr state next c = if digitCode (toℕ c) then advance state else next
  private
    numberStep : NumberState → Char → NumberStep
    numberStep firstDigit '0' = advance afterZero
    numberStep firstDigit c = requireDigit integerDigits "in numeric literal" c
    numberStep integerDigits c = digitOr integerDigits (fractionOrEnd c) c
    numberStep afterZero c = fractionOrEnd c
    numberStep firstFraction c = requireDigit fractionDigits "after decimal point in numeric literal" c
    numberStep fractionDigits c = digitOr fractionDigits (exponentOrEnd c) c
    numberStep exponentSign '+' = advance firstExponent
    numberStep exponentSign '-' = advance firstExponent
    numberStep exponentSign c = requireDigit exponentDigits "in exponent of numeric literal" c
    numberStep firstExponent c = requireDigit exponentDigits "in exponent of numeric literal" c
    numberStep exponentDigits c = digitOr exponentDigits finishToken c
  private
    numberEnd : NumberState → Result (List Char)
    numberEnd integerDigits = inj₂ (parsed [] [])
    numberEnd afterZero = inj₂ (parsed [] [])
    numberEnd fractionDigits = inj₂ (parsed [] [])
    numberEnd exponentDigits = inj₂ (parsed [] [])
    numberEnd _ = incomplete
  private
    numberMore : Char → List Char → (NumberState → Result (List Char)) → NumberStep → Result (List Char)
    numberMore c cs next (advance state) = emit (c ∷ []) (next state)
    numberMore c cs next finishToken = inj₂ (parsed [] (c ∷ cs))
    numberMore c cs next (reject message) = badCharacter c message
  private
    numberChars : NumberState → List Char → Result (List Char)
    numberChars state [] = numberEnd state
    numberChars state (c ∷ cs) = numberMore c cs (λ next → numberChars next cs) (numberStep state c)
  decodeNumber : List Char → String ⊎ Parsed String
  decodeNumber ('-' ∷ xs) = mapParsed fromList (emit ('-' ∷ []) (numberChars firstDigit xs))
  decodeNumber xs = mapParsed fromList (numberChars firstDigit xs)
  private
    hexValue : Char → Maybe ℕ
    hexValue c = let n = toℕ c in if digitCode n then just (n ∸ 48) else (if ((64 <ᵇ n) ∧ (n <ᵇ 71)) then just (n ∸ 55) else (if ((96 <ᵇ n) ∧ (n <ᵇ 103)) then just (n ∸ 87) else nothing))
  private
    simpleEscape : Char → Maybe Char
    simpleEscape '\"' = just '\"'
    simpleEscape '\\' = just '\\'
    simpleEscape '/' = just '/'
    simpleEscape 'b' = just (fromℕ 8)
    simpleEscape 'f' = just (fromℕ 12)
    simpleEscape 'n' = just '\n'
    simpleEscape 'r' = just '\r'
    simpleEscape 't' = just '	'
    simpleEscape _ = nothing
  private
    data Surrogate : Set where
      noHigh : Surrogate
      pendingHigh : ℕ → Surrogate
  private
    replacement : Char
    replacement = fromℕ 65533
  private
    flushHigh : Surrogate → List Char → List Char
    flushHigh noHigh cs = cs
    flushHigh (pendingHigh _) cs = replacement ∷ cs
  private
    joinLow : Surrogate → ℕ → Char
    joinLow noHigh low = replacement
    joinLow (pendingHigh high) low = fromℕ ((65536 + ((high ∸ 55296) * 1024)) + (low ∸ 56320))
  private
    unicodeStep : Surrogate → ℕ → List Char × Surrogate
    unicodeStep pending n = if ((55295 <ᵇ n) ∧ (n <ᵇ 56320)) then (flushHigh pending [] , pendingHigh n) else (if ((56319 <ᵇ n) ∧ (n <ᵇ 57344)) then ((joinLow pending n ∷ []) , noHigh) else (flushHigh pending (fromℕ n ∷ []) , noHigh))
  private
    data QuoteState : Set where
      ordinary : QuoteState
      escaped : QuoteState
      hexadecimal : ℕ → ℕ → QuoteState
  private
    emitEscape : Surrogate → Char → Result (List Char) → Maybe Char → Result (List Char)
    emitEscape pending c next nothing = badCharacter c "in string escape code"
    emitEscape pending c next (just d) = emit (flushHigh pending (d ∷ [])) next
  private
    readHex : Char → (ℕ → Result (List Char)) → Maybe ℕ → Result (List Char)
    readHex c next nothing = badCharacter c "in \\u hexadecimal character escape"
    readHex c next (just d) = next d
  private
    quotedChars : Surrogate → QuoteState → List Char → Result (List Char)
    quotedChars pending state [] = incomplete
    quotedChars pending ordinary ('\"' ∷ xs) = inj₂ (parsed (flushHigh pending []) xs)
    quotedChars pending ordinary ('\\' ∷ xs) = quotedChars pending escaped xs
    quotedChars pending ordinary (c ∷ xs) = if (toℕ c <ᵇ 32) then badCharacter c "in string literal" else emit (flushHigh pending (c ∷ [])) (quotedChars noHigh ordinary xs)
    quotedChars pending escaped ('u' ∷ xs) = quotedChars pending (hexadecimal 3 0) xs
    quotedChars pending escaped (c ∷ xs) = emitEscape pending c (quotedChars noHigh ordinary xs) (simpleEscape c)
    quotedChars pending (hexadecimal zero n) (c ∷ xs) = readHex c (λ d → let step = unicodeStep pending ((n * 16) + d) in emit (proj₁ step) (quotedChars (proj₂ step) ordinary xs)) (hexValue c)
    quotedChars pending (hexadecimal (suc left) n) (c ∷ xs) = readHex c (λ d → quotedChars pending (hexadecimal left ((n * 16) + d)) xs) (hexValue c)
  decodeQuoted : List Char → String ⊎ Parsed String
  decodeQuoted xs = mapParsed fromList (quotedChars noHigh ordinary xs)
  private
    whitespace : List Char → List Char
    whitespace (' ' ∷ xs) = whitespace xs
    whitespace ('	' ∷ xs) = whitespace xs
    whitespace ('\r' ∷ xs) = whitespace xs
    whitespace ('\n' ∷ xs) = whitespace xs
    whitespace xs = xs
  private
    expectLiteral : String → Value → List Char → List Char → Result Value
    expectLiteral word v [] xs = inj₂ (parsed v xs)
    expectLiteral word v (c ∷ cs) [] = incomplete
    expectLiteral word v (c ∷ cs) (d ∷ ds) = if (toℕ d ≡ᵇ toℕ c) then expectLiteral word v cs ds else badCharacter d ("in literal " ++ˢ (word ++ˢ (" (expecting " ++ˢ (diagnostic c ++ˢ ")"))))
  private
    decodeHead : Bool → Char → List Char → Result Value → (List Char → Result (List Value)) → (List Char → Result (List (String × Value))) → Result Value
    decodeHead true c xs skipped elements members = mapParsed (λ n → scalar (number n)) (decodeNumber (c ∷ xs))
    decodeHead false ' ' xs skipped elements members = skipped
    decodeHead false '	' xs skipped elements members = skipped
    decodeHead false '\r' xs skipped elements members = skipped
    decodeHead false '\n' xs skipped elements members = skipped
    decodeHead false 't' xs skipped elements members = expectLiteral "true" (scalar (boolean true)) ('r' ∷ ('u' ∷ ('e' ∷ []))) xs
    decodeHead false 'f' xs skipped elements members = expectLiteral "false" (scalar (boolean false)) ('a' ∷ ('l' ∷ ('s' ∷ ('e' ∷ [])))) xs
    decodeHead false 'n' xs skipped elements members = expectLiteral "null" (scalar null) ('u' ∷ ('l' ∷ ('l' ∷ []))) xs
    decodeHead false '\"' xs skipped elements members = mapParsed (λ s → scalar (text s)) (decodeQuoted xs)
    decodeHead false '[' xs skipped elements members = mapParsed array (elements xs)
    decodeHead false '{' xs skipped elements members = mapParsed (λ kvs → object (keepLatest kvs)) (members xs)
    decodeHead false c xs skipped elements members = badCharacter c "looking for beginning of value"
  private
    data Inner : Set where
      inside : (List Char → Result Value) → (List Char → Result (List Value)) → (List Char → Result (List (String × Value))) → Inner
  private
    valueAt : Inner → List Char → Result Value
    valueAt (inside value element member) = value
  private
    elementAt : Inner → List Char → Result (List Value)
    elementAt (inside value element member) = element
  private
    memberAt : Inner → List Char → Result (List (String × Value))
    memberAt (inside value element member) = member
  private
    startElements : Inner → List Char → Result (List Value)
    startElements p [] = incomplete
    startElements p (']' ∷ xs) = inj₂ (parsed [] xs)
    startElements p xs = elementAt p xs
  private
    startMembers : Inner → List Char → Result (List (String × Value))
    startMembers p [] = incomplete
    startMembers p ('}' ∷ xs) = inj₂ (parsed [] xs)
    startMembers p xs = memberAt p xs
  private
    insideValue : Inner → List Char → Result Value
    insideValue p [] = incomplete
    insideValue p (c ∷ xs) = decodeHead (numberStart c) c xs (valueAt p xs) (λ ys → startElements p (whitespace ys)) (λ ys → startMembers p (whitespace ys))
  private
    afterElement : Inner → Value → List Char → Result (List Value)
    afterElement p v [] = incomplete
    afterElement p v (']' ∷ xs) = inj₂ (parsed (v ∷ []) xs)
    afterElement p v (',' ∷ xs) = mapParsed (λ vs → v ∷ vs) (elementAt p (whitespace xs))
    afterElement p v (c ∷ xs) = badCharacter c "after array element"
  private
    insideElement : Inner → List Char → Result (List Value)
    insideElement p xs = [_,_]′ inj₁ (λ r → afterElement p (Parsed.value r) (whitespace (Parsed.rest r))) (valueAt p xs)
  private
    afterMember : Inner → (String × Value) → List Char → Result (List (String × Value))
    afterMember p kv [] = incomplete
    afterMember p kv ('}' ∷ xs) = inj₂ (parsed (kv ∷ []) xs)
    afterMember p kv (',' ∷ xs) = mapParsed (λ kvs → kv ∷ kvs) (memberAt p (whitespace xs))
    afterMember p kv (c ∷ xs) = badCharacter c "after object key:value pair"
  private
    memberValue : Inner → String → List Char → Result (List (String × Value))
    memberValue p k [] = incomplete
    memberValue p k (':' ∷ xs) = [_,_]′ inj₁ (λ r → afterMember p (k , Parsed.value r) (whitespace (Parsed.rest r))) (valueAt p xs)
    memberValue p k (c ∷ xs) = badCharacter c "after object key"
  private
    insideMember : Inner → List Char → Result (List (String × Value))
    insideMember p [] = incomplete
    insideMember p ('\"' ∷ xs) = [_,_]′ inj₁ (λ r → memberValue p (Parsed.value r) (whitespace (Parsed.rest r))) (decodeQuoted xs)
    insideMember p (c ∷ xs) = badCharacter c "looking for beginning of object key string"
  private
    nextInner : Inner → Inner
    nextInner p = inside (insideValue p) (insideElement p) (insideMember p)
  private
    inputLayers : List Char → Inner
    inputLayers [] = inside (λ _ → incomplete) (λ _ → incomplete) (λ _ → incomplete)
    inputLayers (_ ∷ xs) = nextInner (nextInner (inputLayers xs))
  decodeElements : List Char → String ⊎ Parsed (List Value)
  decodeElements xs = startElements (inputLayers xs) (whitespace xs)
  decodeMembers : List Char → String ⊎ Parsed (List (String × Value))
  decodeMembers xs = startMembers (inputLayers xs) (whitespace xs)
  decodePrefix : List Char → String ⊎ Parsed Value
  decodePrefix [] = inj₁ "EOF"
  decodePrefix (c ∷ xs) = decodeHead (numberStart c) c xs (decodePrefix xs) decodeElements decodeMembers
  endOfInput : decodePrefix [] ≡ inj₁ "EOF"
  endOfInput = refl
  leadingSpace : (xs : _) → decodePrefix (' ' ∷ xs) ≡ decodePrefix xs
  leadingSpace xs = refl
  leadingTab : (xs : _) → decodePrefix ('	' ∷ xs) ≡ decodePrefix xs
  leadingTab xs = refl
  leadingCR : (xs : _) → decodePrefix ('\r' ∷ xs) ≡ decodePrefix xs
  leadingCR xs = refl
  leadingLF : (xs : _) → decodePrefix ('\n' ∷ xs) ≡ decodePrefix xs
  leadingLF xs = refl
  truePrefix : (xs : _) → decodePrefix ('t' ∷ ('r' ∷ ('u' ∷ ('e' ∷ xs)))) ≡ inj₂ (parsed (scalar (boolean true)) xs)
  truePrefix xs = refl
  falsePrefix : (xs : _) → decodePrefix ('f' ∷ ('a' ∷ ('l' ∷ ('s' ∷ ('e' ∷ xs))))) ≡ inj₂ (parsed (scalar (boolean false)) xs)
  falsePrefix xs = refl
  nullPrefix : (xs : _) → decodePrefix ('n' ∷ ('u' ∷ ('l' ∷ ('l' ∷ xs)))) ≡ inj₂ (parsed (scalar null) xs)
  nullPrefix xs = refl
  closeQuote : (xs : _) → decodeQuoted ('\"' ∷ xs) ≡ inj₂ (parsed "" xs)
  closeQuote xs = refl
  closeArray : (xs : _) → decodeElements (']' ∷ xs) ≡ inj₂ (parsed [] xs)
  closeArray xs = refl
  closeObject : (xs : _) → decodeMembers ('}' ∷ xs) ≡ inj₂ (parsed [] xs)
  closeObject xs = refl
  quotedPrefix : (xs : _) → (s : _) → (rest : _) → (decodeQuoted xs ≡ inj₂ (parsed s rest)) → decodePrefix ('\"' ∷ xs) ≡ inj₂ (parsed (scalar (text s)) rest)
  quotedPrefix xs s rest ok = cong (mapParsed (λ t → scalar (text t))) ok
  quotedError : (xs : _) → (e : _) → (decodeQuoted xs ≡ inj₁ e) → decodePrefix ('\"' ∷ xs) ≡ inj₁ e
  quotedError xs e err = cong (mapParsed (λ t → scalar (text t))) err
  private
    numericHead : (c : _) → (xs : _) → (numberStart c ≡ true) → decodePrefix (c ∷ xs) ≡ mapParsed (λ n → scalar (number n)) (decodeNumber (c ∷ xs))
    numericHead c xs starts = cong (λ b → decodeHead b c xs (decodePrefix xs) decodeElements decodeMembers) starts
  numericPrefix : (c : _) → (xs : _) → (s : _) → (rest : _) → (((toℕ c ≡ᵇ 45) ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))) ≡ true) → (decodeNumber (c ∷ xs) ≡ inj₂ (parsed s rest)) → decodePrefix (c ∷ xs) ≡ inj₂ (parsed (scalar (number s)) rest)
  numericPrefix c xs s rest starts ok = trans (numericHead c xs starts) (cong (mapParsed (λ n → scalar (number n))) ok)
  numericError : (c : _) → (xs : _) → (e : _) → (((toℕ c ≡ᵇ 45) ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))) ≡ true) → (decodeNumber (c ∷ xs) ≡ inj₁ e) → decodePrefix (c ∷ xs) ≡ inj₁ e
  numericError c xs e starts err = trans (numericHead c xs starts) (cong (mapParsed (λ n → scalar (number n))) err)
  arrayPrefix : (xs : _) → (vs : _) → (rest : _) → (decodeElements xs ≡ inj₂ (parsed vs rest)) → decodePrefix ('[' ∷ xs) ≡ inj₂ (parsed (array vs) rest)
  arrayPrefix xs vs rest ok = cong (mapParsed array) ok
  arrayError : (xs : _) → (e : _) → (decodeElements xs ≡ inj₁ e) → decodePrefix ('[' ∷ xs) ≡ inj₁ e
  arrayError xs e err = cong (mapParsed array) err
  objectPrefix : (xs : _) → (kvs : _) → (rest : _) → (decodeMembers xs ≡ inj₂ (parsed kvs rest)) → decodePrefix ('{' ∷ xs) ≡ inj₂ (parsed (object (keepLatest kvs)) rest)
  objectPrefix xs kvs rest ok = cong (mapParsed (λ kvs → object (keepLatest kvs))) ok
  objectError : (xs : _) → (e : _) → (decodeMembers xs ≡ inj₁ e) → decodePrefix ('{' ∷ xs) ≡ inj₁ e
  objectError xs e err = cong (mapParsed (λ kvs → object (keepLatest kvs))) err
  decodedSorted : decodePrefix (toList "{\"-?\":4,\"- \":2,\"-!\":3,\"-\":1,\"a$\":5,\"a\":{\"-?\":6},\"A\":7}") ≡ inj₂ (parsed (object (("-?" , scalar (number "4")) ∷ (("- " , scalar (number "2")) ∷ (("-!" , scalar (number "3")) ∷ (("-" , scalar (number "1")) ∷ (("a$" , scalar (number "5")) ∷ (("a" , object (("-?" , scalar (number "6")) ∷ [])) ∷ (("A" , scalar (number "7")) ∷ [])))))))) [])
  decodedSorted = refl
  decodedEscaping : decodePrefix (toList "{\"x\\u000b\\u2028\\u0085\":\"\\u000b\\u001f\\u007f\\u0085\\u2028\\u2029<&>/\"}") ≡ inj₂ (parsed (object ((fromList ('x' ∷ (fromℕ 11 ∷ (fromℕ 8232 ∷ (fromℕ 133 ∷ [])))) , scalar (text (fromList (fromℕ 11 ∷ (fromℕ 31 ∷ (fromℕ 127 ∷ (fromℕ 133 ∷ (fromℕ 8232 ∷ (fromℕ 8233 ∷ toList "<&>/"))))))))) ∷ [])) [])
  decodedEscaping = refl
  decodedDuplicate : decodePrefix (toList "{\"a\":1,\"\\u0061\":{\"z\":3},\"b\":2}") ≡ inj₂ (parsed (object (("a" , object (("z" , scalar (number "3")) ∷ [])) ∷ (("b" , scalar (number "2")) ∷ []))) [])
  decodedDuplicate = refl
  decodedMalformed : decodePrefix (toList "{\"a\":1,\"\\u0061\":nulx}") ≡ inj₁ "invalid character 'x' in literal null (expecting 'l')"
  decodedMalformed = refl
  decodedSeed : decodePrefix (toList "[\"λ<&>\\u2028\",{}]") ≡ inj₂ (parsed (array (scalar (text (fromList (toList "λ<&>" ++ (fromℕ 8232 ∷ [])))) ∷ (object [] ∷ []))) [])
  decodedSeed = refl
  decodedNumber : decodePrefix (toList "-94.00e+2") ≡ inj₂ (parsed (scalar (number "-94.00e+2")) [])
  decodedNumber = refl
  decodedStreamTwelve : decodePrefix (toList " 12xyz") ≡ inj₂ (parsed (scalar (number "12")) (toList "xyz"))
  decodedStreamTwelve = refl
  decodedStreamTrue : decodePrefix (toList "true false") ≡ inj₂ (parsed (scalar (boolean true)) (toList " false"))
  decodedStreamTrue = refl
  decodedOnlyTrue : decodePrefix (toList "true") ≡ inj₂ (parsed (scalar (boolean true)) [])
  decodedOnlyTrue = refl
  private
    letterRanges : List Char
    letterRanges = toList ("ªªµµººÀÖØöøˁˆˑˠˤˬˬˮˮͰʹͶͷͺͽͿͿΆΆΈΊΌΌΎΡΣϵϷҁҊԯԱՖՙՙՠֈאת" ++ˢ ("ׯײؠيٮٯٱۓەەۥۦۮۯۺۼۿۿܐܐܒܯݍޥޱޱߊߪߴߵߺߺࠀࠕࠚࠚࠤࠤࠨࠨࡀࡘࡠࡪࡰࢇࢉ࢏ࢠࣉ" ++ˢ ("ऄहऽऽॐॐक़ॡॱঀঅঌএঐওনপরললশহঽঽৎৎড়ঢ়য়ৡৰৱৼৼਅਊਏਐਓਨਪਰਲਲ਼ਵਸ਼ਸਹਖ਼ੜ" ++ˢ ("ਫ਼ਫ਼ੲੴઅઍએઑઓનપરલળવહઽઽૐૐૠૡૹૹଅଌଏଐଓନପରଲଳଵହଽଽଡ଼ଢ଼ୟୡୱୱஃஃஅஊஎஐ" ++ˢ ("ஒகஙசஜஜஞடணதநபமஹௐௐఅఌఎఐఒనపహఽఽౘౚ౜ౝౠౡಀಀಅಌಎಐಒನಪಳವಹಽಽ೜ೞೠೡ" ++ˢ ("ೱೲഄഌഎഐഒഺഽഽൎൎൔൖൟൡൺൿඅඖකනඳරලලවෆกะาำเๆກຂຄຄຆຊຌຣລລວະາຳຽຽ" ++ˢ ("ເໄໆໆໜໟༀༀཀཇཉཬྈྌကဪဿဿၐၕၚၝၡၡၥၦၮၰၵႁႎႎႠჅჇჇჍჍაჺჼቈቊቍቐቖቘቘቚቝ" ++ˢ ("በኈኊኍነኰኲኵኸኾዀዀዂዅወዖዘጐጒጕጘፚᎀᎏᎠᏵᏸᏽᐁᙬᙯᙿᚁᚚᚠᛪᛮᛸᜀᜑᜟᜱᝀᝑᝠᝬᝮᝰកឳ" ++ˢ ("ៗៗៜៜᠠᡸᢀᢄᢇᢨᢪᢪᢰᣵᤀᤞᥐᥭᥰᥴᦀᦫᦰᧉᨀᨖᨠᩔᪧᪧᬅᬳᭅᭌᮃᮠᮮᮯᮺᯥᰀᰣᱍᱏᱚᱽᲀᲊᲐᲺ" ++ˢ ("ᲽᲿᳩᳬᳮᳳᳵᳶᳺᳺᴀᶿḀἕἘἝἠὅὈὍὐὗὙὙὛὛὝὝὟώᾀᾴᾶᾼιιῂῄῆῌῐΐῖΊῠῬῲῴῶῼ" ++ˢ ("ⁱⁱⁿⁿₐₜℂℂℇℇℊℓℕℕℙℝℤℤΩΩℨℨKℭℯℹℼℿⅅⅉⅎⅎⅠↈⰀⳤⳫⳮⳲⳳⴀⴥⴧⴧⴭⴭⴰⵧⵯⵯ" ++ˢ ("ⶀⶖⶠⶦⶨⶮⶰⶶⶸⶾⷀⷆⷈⷎⷐⷖⷘⷞⸯⸯ々〇〡〩〱〵〸〼ぁゖゝゟァヺーヿㄅㄯㄱㆎㆠㆿㇰㇿ㐀䶿一ꒌꓐꓽ" ++ˢ ("ꔀꘌꘐꘟꘪꘫꙀꙮꙿꚝꚠꛯꜗꜟꜢꞈꞋꟜ꟱ꠁꠃꠅꠇꠊꠌꠢꡀꡳꢂꢳꣲꣷꣻꣻꣽꣾꤊꤥꤰꥆꥠꥼꦄꦲꧏꧏꧠꧤꧦꧯ" ++ˢ ("ꧺꧾꨀꨨꩀꩂꩄꩋꩠꩶꩺꩺꩾꪯꪱꪱꪵꪶꪹꪽꫀꫀꫂꫂꫛꫝꫠꫪꫲꫴꬁꬆꬉꬎꬑꬖꬠꬦꬨꬮꬰꭚꭜꭩꭰꯢ가힣ힰퟆ" ++ˢ ("ퟋퟻ豈舘並龎ﬀﬆﬓﬗיִיִײַﬨשׁזּטּלּמּמּנּסּףּפּצּﮱﯓﴽﵐﶏﶒﷇﷰﷻﹰﹴﹶﻼＡＺａｚｦﾾￂￇￊￏￒￗ" ++ˢ ("ￚￜ𐀀𐀋𐀍𐀦𐀨𐀺𐀼𐀽𐀿𐁍𐁐𐁝𐂀𐃺𐅀𐅴𐊀𐊜𐊠𐋐𐌀𐌟𐌭𐍊𐍐𐍵𐎀𐎝𐎠𐏃𐏈𐏏𐏑𐏕𐐀𐒝𐒰𐓓𐓘𐓻𐔀𐔧𐔰𐕣𐕰𐕺𐕼𐖊" ++ˢ ("𐖌𐖒𐖔𐖕𐖗𐖡𐖣𐖱𐖳𐖹𐖻𐖼𐗀𐗳𐘀𐜶𐝀𐝕𐝠𐝧𐞀𐞅𐞇𐞰𐞲𐞺𐠀𐠅𐠈𐠈𐠊𐠵𐠷𐠸𐠼𐠼𐠿𐡕𐡠𐡶𐢀𐢞𐣠𐣲𐣴𐣵𐤀𐤕𐤠𐤹" ++ˢ ("𐥀𐥙𐦀𐦷𐦾𐦿𐨀𐨀𐨐𐨓𐨕𐨗𐨙𐨵𐩠𐩼𐪀𐪜𐫀𐫇𐫉𐫤𐬀𐬵𐭀𐭕𐭠𐭲𐮀𐮑𐰀𐱈𐲀𐲲𐳀𐳲𐴀𐴣𐵊𐵥𐵯𐶅𐺀𐺩𐺰𐺱𐻂𐻇𐼀𐼜" ++ˢ ("𐼧𐼧𐼰𐽅𐽰𐾁𐾰𐿄𐿠𐿶𑀃𑀷𑁱𑁲𑁵𑁵𑂃𑂯𑃐𑃨𑄃𑄦𑅄𑅄𑅇𑅇𑅐𑅲𑅶𑅶𑆃𑆲𑇁𑇄𑇚𑇚𑇜𑇜𑈀𑈑𑈓𑈫𑈿𑉀𑊀𑊆𑊈𑊈𑊊𑊍" ++ˢ ("𑊏𑊝𑊟𑊨𑊰𑋞𑌅𑌌𑌏𑌐𑌓𑌨𑌪𑌰𑌲𑌳𑌵𑌹𑌽𑌽𑍐𑍐𑍝𑍡𑎀𑎉𑎋𑎋𑎎𑎎𑎐𑎵𑎷𑎷𑏑𑏑𑏓𑏓𑐀𑐴𑑇𑑊𑑟𑑡𑒀𑒯𑓄𑓅𑓇𑓇" ++ˢ ("𑖀𑖮𑗘𑗛𑘀𑘯𑙄𑙄𑚀𑚪𑚸𑚸𑜀𑜚𑝀𑝆𑠀𑠫𑢠𑣟𑣿𑤆𑤉𑤉𑤌𑤓𑤕𑤖𑤘𑤯𑤿𑤿𑥁𑥁𑦠𑦧𑦪𑧐𑧡𑧡𑧣𑧣𑨀𑨀𑨋𑨲𑨺𑨺𑩐𑩐" ++ˢ ("𑩜𑪉𑪝𑪝𑪰𑫸𑯀𑯠𑰀𑰈𑰊𑰮𑱀𑱀𑱲𑲏𑴀𑴆𑴈𑴉𑴋𑴰𑵆𑵆𑵠𑵥𑵧𑵨𑵪𑶉𑶘𑶘𑶰𑷛𑻠𑻲𑼂𑼂𑼄𑼐𑼒𑼳𑾰𑾰𒀀𒎙𒐀𒑮𒒀𒕃" ++ˢ ("𒾐𒿰𓀀𓐯𓑁𓑆𓑠𔏺𔐀𔙆𖄀𖄝𖠀𖨸𖩀𖩞𖩰𖪾𖫐𖫭𖬀𖬯𖭀𖭃𖭣𖭷𖭽𖮏𖵀𖵬𖹀𖹿𖺠𖺸𖺻𖻓𖼀𖽊𖽐𖽐𖾓𖾟𖿠𖿡𖿣𖿣𖿲𖿶𗀀𘳕" ++ˢ ("𘳿𘴞𘶀𘷲𚿰𚿳𚿵𚿻𚿽𚿾𛀀𛄢𛄲𛄲𛅐𛅒𛅕𛅕𛅤𛅧𛅰𛋻𛰀𛱪𛱰𛱼𛲀𛲈𛲐𛲙𝐀𝑔𝑖𝒜𝒞𝒟𝒢𝒢𝒥𝒦𝒩𝒬𝒮𝒹𝒻𝒻𝒽𝓃𝓅𝔅" ++ˢ ("𝔇𝔊𝔍𝔔𝔖𝔜𝔞𝔹𝔻𝔾𝕀𝕄𝕆𝕆𝕊𝕐𝕒𝚥𝚨𝛀𝛂𝛚𝛜𝛺𝛼𝜔𝜖𝜴𝜶𝝎𝝐𝝮𝝰𝞈𝞊𝞨𝞪𝟂𝟄𝟋𝼀𝼞𝼥𝼪𞀰𞁭𞄀𞄬𞄷𞄽" ++ˢ ("𞅎𞅎𞊐𞊭𞋀𞋫𞓐𞓫𞗐𞗭𞗰𞗰𞛀𞛞𞛠𞛢𞛤𞛥𞛧𞛭𞛰𞛴𞛾𞛿𞟠𞟦𞟨𞟫𞟭𞟮𞟰𞟾𞠀𞣄𞤀𞥃𞥋𞥋𞸀𞸃𞸅𞸟𞸡𞸢𞸤𞸤𞸧𞸧𞸩𞸲" ++ˢ ("𞸴𞸷𞸹𞸹𞸻𞸻𞹂𞹂𞹇𞹇𞹉𞹉𞹋𞹋𞹍𞹏𞹑𞹒𞹔𞹔𞹗𞹗𞹙𞹙𞹛𞹛𞹝𞹝𞹟𞹟𞹡𞹢𞹤𞹤𞹧𞹪𞹬𞹲𞹴𞹷𞹹𞹼𞹾𞹾𞺀𞺉𞺋𞺛𞺡𞺣" ++ˢ "𞺥𞺩𞺫𞺻𠀀𪛟𪜀𫠝𫠠𬺭𬺰𮯠𮯰𮹝丽𪘀𰀀𱍊𱍐𳑹")))))))))))))))))))))))))))
  private
    continuationRanges : List Char
    continuationRanges = toList ("ׇׇֽֿֿׁׂًؚ֑ׅ̀ͯ҃҇ׄؐ٩ٰٰ۪ۭۖۜ۟ۤۧۨ۰۹ܑܑܰ݊ަް߀߉߽߽߫߳ࠖ࠙ࠛࠣࠥࠧࠩ࠭" ++ˢ ("࡙࡛ࣣࢗ࢟࣊࣡ःऺ़ाॏ॑ॗॢॣ०९ঁঃ়়াৄেৈো্ৗৗৢৣ০৯৾৾ਁਃ਼਼ਾੂੇੈੋ੍ੑੑ੦ੱ" ++ˢ ("ੵੵઁઃ઼઼ાૅેૉો્ૢૣ૦૯ૺ૿ଁଃ଼଼ାୄେୈୋ୍୕ୗୢୣ୦୯ஂஂாூெைொ்ௗௗ௦௯ఀఄ఼఼" ++ˢ ("ాౄెైొ్ౕౖౢౣ౦౯ಁಃ಼಼ಾೄೆೈೊ್ೕೖೢೣ೦೯ೳೳഀഃ഻഼ാൄെൈൊ്ൗൗൢൣ൦൯ඁඃ්්" ++ˢ ("ාුූූෘෟ෦෯ෲෳััิฺ็๎๐๙ັັິຼ່໎໐໙༘༙༠༩༹༹༵༵༷༷༾༿྄ཱ྆྇ྍྗྙྼ࿆࿆ါှ" ++ˢ ("၀၉ၖၙၞၠၢၤၧၭၱၴႂႍႏႝ፝፟ᜒ᜕ᜲ᜴ᝒᝓᝲᝳ឴៓៝៝០៩᠋᠍᠏᠙ᢅᢆᢩᢩᤠᤫᤰ᤻᥆᥏᧐᧙ᨗᨛ" ++ˢ ("ᩕᩞ᩠᩿᩼᪉᪐᪙᪽ᪿ᪰᫝᫠᫫ᬀᬄ᬴᭄᭐᭙᭫᭳ᮀᮂᮡᮭ᮰᮹᯦᯳ᰤ᰷᱀᱉᱐᱙᳔᳨᳭᳭᳐᳒᳴᳴᳷᷿᳹᷀‿⁀" ++ˢ ("⁔⁔⃥゙゚⵿⵿〪〯⃐⃜⃡⃡⃰⳯⳱ⷠⷿ꘠꘩꙯꙯ꙴ꙽ꚞꚟ꛰꛱ꠂꠂ꠆꠆ꠋꠋꠣꠧ꠬꠬ꢀꢁꢴꣅ꣐꣙꣠꣱ꣿ꤉ꤦ꤭" ++ˢ ("ꥇ꥓ꦀꦃ꦳꧀꧐꧙ꧥꧥ꧰꧹ꨩꨶꩃꩃꩌꩍ꩐꩙ꩻꩽꪴꪰꪰꪲꪷꪸꪾ꪿꫁꫁ꫫꫯꫵ꫶ꯣꯪ꯬꯭꯰꯹ﬞﬞ︀️︠︯︳︴" ++ˢ ("﹍﹏０９＿＿𐇽𐇽𐋠𐋠𐍶𐍺𐒠𐒩𐨁𐨃𐨅𐨆𐨌𐨿𐨿𐨺𐫦𐨏𐨸𐫥𐴤𐴧𐴰𐴹𐵀𐵉𐵩𐵭𐺫𐺬𐻺𐻿𐽆𐽐𐾅𐾂𑀀𑀂𑀸𑁆𑁦𑁰𑁳𑁴" ++ˢ ("𑁿𑂂𑂰𑂺𑃂𑃂𑃰𑃹𑄀𑄂𑄧𑄴𑄶𑄿𑅅𑅆𑅳𑅳𑆀𑆂𑆳𑇀𑇉𑇌𑇎𑇙𑈬𑈷𑈾𑈾𑉁𑉁𑋟𑋪𑋰𑋹𑌀𑌃𑌻𑌼𑌾𑍄𑍇𑍈𑍋𑍍𑍗𑍗𑍢𑍣" ++ˢ ("𑍦𑍬𑍰𑍴𑎸𑏀𑏅𑏅𑏅𑏇𑏊𑏌𑏐𑏒𑏒𑏡𑏢𑐵𑑆𑑐𑑙𑑞𑑞𑒰𑓃𑓐𑓙𑖯𑖵𑖸𑗀𑗜𑗝𑘰𑙀𑙐𑙙𑚫𑚷𑛀𑛉𑛐𑛣𑜝𑜫𑜰𑜹𑠬𑠺" ++ˢ ("𑣠𑣩𑤰𑤵𑤷𑤸𑤻𑤾𑥀𑥀𑥂𑥃𑥐𑥙𑧑𑧗𑧚𑧠𑧤𑧤𑨁𑨊𑨳𑨹𑨻𑨾𑩇𑩇𑩑𑩛𑪊𑪙𑭠𑭧𑯰𑯹𑰯𑰶𑰸𑰿𑱐𑱙𑲒𑲧𑲩𑲶𑴱𑴶𑴺𑴺" ++ˢ ("𑴼𑴽𑴿𑵅𑵇𑵇𑵐𑵙𑶊𑶎𑶐𑶑𑶓𑶗𑶠𑶩𑷠𑷩𑻳𑻶𑼀𑼁𑼃𑼃𑼴𑼺𑼾𑽂𑽐𑽚𓑀𓑀𓑇𓑕𖄞𖄹𖩠𖩩𖫀𖫉𖫰𖫴𖬰𖬶𖭐𖭙𖵰𖵹𖽏𖽏" ++ˢ ("𖽑𖾇𖾏𖾒𖿤𖿤𖿰𖿱𛲝𛲞𜳰𜳹𜼀𜼭𜼰𜽆𝅩𝅥𝅲𝅻𝆂𝆋𝅭𝆅𝆪𝆭𝉂𝉄𝟎𝟿𝨀𝨶𝨻𝩬𝩵𝩵𝪄𝪄𝪛𝪟𝪡𝪯𞀀𞀆𞀈𞀘𞀛𞀡𞀣𞀤" ++ˢ "𞀦𞀪𞂏𞂏𞄰𞄶𞅀𞅉𞊮𞊮𞋬𞋹𞓬𞓹𞗯𞗮𞗱𞗺𞛣𞛣𞛦𞛦𞛮𞛯𞛵𞛵𞥊𞣐𞣖𞥄𞥐𞥙🯰🯹󠄀󠇯")))))))))))))))
  private
    inRanges : ℕ → List Char → Bool
    inRanges n [] = false
    inRanges n (lo ∷ []) = false
    inRanges n (lo ∷ (hi ∷ more)) = if (n <ᵇ toℕ lo) then false else (if (toℕ hi <ᵇ n) then inRanges n more else true)
  private
    asciiHead : ℕ → Bool
    asciiHead n = (n ≡ᵇ 36) ∨ ((n ≡ᵇ 95) ∨ (((64 <ᵇ n) ∧ (n <ᵇ 91)) ∨ ((96 <ᵇ n) ∧ (n <ᵇ 123))))
  canStart : Char → Bool
  canStart c = if (toℕ c <ᵇ 128) then asciiHead (toℕ c) else inRanges (toℕ c) letterRanges
  canContinue : Char → Bool
  canContinue c = canStart c ∨ (if (toℕ c <ᵇ 128) then digitCode (toℕ c) else inRanges (toℕ c) continuationRanges)
  reservedWords : List (List Char)
  reservedWords = map toList ("break" ∷ ("case" ∷ ("catch" ∷ ("class" ∷ ("const" ∷ ("continue" ∷ ("debugger" ∷ ("default" ∷ ("delete" ∷ ("do" ∷ ("else" ∷ ("export" ∷ ("extends" ∷ ("false" ∷ ("finally" ∷ ("for" ∷ ("function" ∷ ("if" ∷ ("import" ∷ ("in" ∷ ("instanceof" ∷ ("new" ∷ ("null" ∷ ("return" ∷ ("super" ∷ ("switch" ∷ ("this" ∷ ("throw" ∷ ("true" ∷ ("try" ∷ ("typeof" ∷ ("var" ∷ ("void" ∷ ("while" ∷ ("with" ∷ ("yield" ∷ []))))))))))))))))))))))))))))))))))))
  private
    sameChars : List Char → List Char → Bool
    sameChars [] [] = true
    sameChars [] (d ∷ ds) = false
    sameChars (c ∷ cs) [] = false
    sameChars (c ∷ cs) (d ∷ ds) = decision (c Ch.≟ d) ∧ sameChars cs ds
  private
    containsWord : List Char → List (List Char) → Bool
    containsWord w [] = false
    containsWord w (t ∷ ts) = sameChars w t ∨ containsWord w ts
  private
    selfChars : (cs : _) → sameChars cs cs ≡ true
    selfChars [] = refl
    selfChars (c ∷ cs) = trans (cong (λ b → b ∧ sameChars cs cs) (decisionYes (c Ch.≟ c) refl)) (selfChars cs)
  private
    decisionSound : {A : Set} → (d : Dec A) → (decision d ≡ true) → A
    decisionSound (yes v) p = v
    decisionSound (no _) ()
  private
    andLeft : (a : _) → (b : _) → ((a ∧ b) ≡ true) → a ≡ true
    andLeft true b p = refl
    andLeft false b ()
  private
    andRight : (a : _) → (b : _) → ((a ∧ b) ≡ true) → b ≡ true
    andRight true b p = p
    andRight false b ()
  private
    charsSound : (cs : _) → (ds : _) → (sameChars cs ds ≡ true) → cs ≡ ds
    charsSound [] [] ok = refl
    charsSound [] (d ∷ ds) ()
    charsSound (c ∷ cs) [] ()
    charsSound (c ∷ cs) (d ∷ ds) ok = let head = c Ch.≟ d; tail = sameChars cs ds in trans (cong (λ x → x ∷ cs) (decisionSound head (andLeft (decision head) tail ok))) (cong (λ xs → d ∷ xs) (charsSound cs ds (andRight (decision head) tail ok)))
  private
    orRight : (b : _) → (b ∨ true) ≡ true
    orRight true = refl
    orRight false = refl
  private
    includesWord : {w : _} → {ws : _} → Listed w ws → containsWord w ws ≡ true
    includesWord {w} (first {words}) = cong (λ b → b ∨ containsWord w words) (selfChars w)
    includesWord {w} (later {other} present) = trans (cong (λ b → sameChars w other ∨ b) (includesWord present)) (orRight (sameChars w other))
  private
    falseUnless : (b : _) → ((b ≡ true) → ⊥) → b ≡ false
    falseUnless false absent = refl
    falseUnless true absent = ⊥-elim (absent refl)
  private
    firstIfSame : {w : _} → {t : _} → {ts : _} → (w ≡ t) → Listed w (t ∷ ts)
    firstIfSame refl = first
  private
    excludesWord : (w : _) → (ws : _) → (Listed w ws → ⊥) → containsWord w ws ≡ false
    excludesWord w [] absent = refl
    excludesWord w (t ∷ ts) absent = trans (cong (λ b → b ∨ containsWord w ts) (falseUnless (sameChars w t) (λ ok → absent (firstIfSame (charsSound w t ok))))) (excludesWord w ts (λ hit → absent (later hit)))
  reserved : List Char → Bool
  reserved w = containsWord w reservedWords
  identifier : List Char → Bool
  identifier [] = false
  identifier (c ∷ cs) = canStart c ∧ (all canContinue cs ∧ not (reserved (c ∷ cs)))
  asciiStart : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → canStart c ≡ ((toℕ c ≡ᵇ 36) ∨ ((toℕ c ≡ᵇ 95) ∨ (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 91)) ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 123)))))
  asciiStart c isAscii = cong (λ b → if b then asciiHead (toℕ c) else inRanges (toℕ c) letterRanges) isAscii
  asciiContinue : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → canContinue c ≡ (canStart c ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58)))
  asciiContinue c isAscii = cong (λ b → canStart c ∨ (if b then digitCode (toℕ c) else inRanges (toℕ c) continuationRanges)) isAscii
  reservedIncluded : (w : _) → Listed w reservedWords → reserved w ≡ true
  reservedIncluded w = includesWord
  reservedExcluded : (w : _) → (Listed w reservedWords → ⊥) → reserved w ≡ false
  reservedExcluded w = excludesWord w reservedWords
  emptyIdentifier : identifier [] ≡ false
  emptyIdentifier = refl
  identifierForm : (c : _) → (cs : _) → identifier (c ∷ cs) ≡ (canStart c ∧ (all canContinue cs ∧ not (reserved (c ∷ cs))))
  identifierForm c cs = refl
  observedReservedWords : reservedWords ≡ map toList ("break" ∷ ("case" ∷ ("catch" ∷ ("class" ∷ ("const" ∷ ("continue" ∷ ("debugger" ∷ ("default" ∷ ("delete" ∷ ("do" ∷ ("else" ∷ ("export" ∷ ("extends" ∷ ("false" ∷ ("finally" ∷ ("for" ∷ ("function" ∷ ("if" ∷ ("import" ∷ ("in" ∷ ("instanceof" ∷ ("new" ∷ ("null" ∷ ("return" ∷ ("super" ∷ ("switch" ∷ ("this" ∷ ("throw" ∷ ("true" ∷ ("try" ∷ ("typeof" ∷ ("var" ∷ ("void" ∷ ("while" ∷ ("with" ∷ ("yield" ∷ []))))))))))))))))))))))))))))))))))))
  observedReservedWords = refl
  private
    upperHex : ℕ → Char
    upperHex n = fromℕ (if (n <ᵇ 10) then (48 + n) else (55 + n))
  private
    hexByte : ℕ → List Char
    hexByte n = upperHex (n / 16) ∷ (upperHex (n % 16) ∷ [])
  private
    unicodeEscape : Char → List Char
    unicodeEscape c = let n = toℕ c in '\\' ∷ ('u' ∷ (hexByte (n / 256) ++ hexByte (n % 256)))
  private
    controlEscape : Char → List Char
    controlEscape '	' = '\\' ∷ ('t' ∷ [])
    controlEscape '\n' = '\\' ∷ ('n' ∷ [])
    controlEscape '\r' = '\\' ∷ ('r' ∷ [])
    controlEscape c = if (toℕ c ≡ᵇ 8) then ('\\' ∷ ('b' ∷ [])) else (if (toℕ c ≡ᵇ 12) then ('\\' ∷ ('f' ∷ [])) else unicodeEscape c)
  private
    specialEscape : Char → List Char
    specialEscape '\"' = '\\' ∷ ('\"' ∷ [])
    specialEscape '\\' = '\\' ∷ ('\\' ∷ [])
    specialEscape c = unicodeEscape c
  private
    specialCode : ℕ → Bool
    specialCode n = (n ≡ᵇ 34) ∨ ((n ≡ᵇ 92) ∨ ((n ≡ᵇ 8232) ∨ (n ≡ᵇ 8233)))
  private
    escapeByClass : Char → Bool → Bool → Bool → List Char
    escapeByClass c false outside special = controlEscape c
    escapeByClass c true false special = unicodeEscape c
    escapeByClass c true true true = specialEscape c
    escapeByClass c true true false = c ∷ []
  escapeChar : Char → List Char
  escapeChar c = let n = toℕ c in escapeByClass c (31 <ᵇ n) ((n <ᵇ 127) ∨ (159 <ᵇ n)) (specialCode n)
  escapeBody : List Char → List Char
  escapeBody [] = []
  escapeBody (c ∷ cs) = escapeChar c ++ escapeBody cs
  quoteForward : String → String
  quoteForward s = fromList ('\"' ∷ (escapeBody (toList s) ++ ('\"' ∷ [])))
  escapeBodyEmpty : escapeBody [] ≡ []
  escapeBodyEmpty = refl
  escapeBodyNext : (c : _) → (cs : _) → escapeBody (c ∷ cs) ≡ (escapeChar c ++ escapeBody cs)
  escapeBodyNext c cs = refl
  private
    literalCase : (c : _) → {above : _} → {outside : _} → {special : _} → (above ≡ true) → (outside ≡ true) → (special ≡ false) → escapeByClass c above outside special ≡ (c ∷ [])
    literalCase c {above} {outside} {special} aboveOK outsideOK specialOK = trans (cong (λ b → escapeByClass c b outside special) aboveOK) (trans (cong (λ b → escapeByClass c true b special) outsideOK) (cong (escapeByClass c true true) specialOK))
  literalChar : (c : _) → ((31 <ᵇ toℕ c) ≡ true) → (((toℕ c <ᵇ 127) ∨ (159 <ᵇ toℕ c)) ≡ true) → (((toℕ c ≡ᵇ 34) ∨ ((toℕ c ≡ᵇ 92) ∨ ((toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233)))) ≡ false) → escapeChar c ≡ (c ∷ [])
  literalChar c = literalCase c
  quoteShape : (s : _) → quoteForward s ≡ fromList ('\"' ∷ (escapeBody (toList s) ++ ('\"' ∷ [])))
  quoteShape s = refl
  csi : String
  csi = fromList (fromℕ 27 ∷ ('[' ∷ []))
  csiPrefix : csi ≡ fromList (fromℕ 27 ∷ ('[' ∷ []))
  csiPrefix = refl
  paint : Bool → Shade → String → String
  paint false hue s = s
  paint true name s = csi ++ˢ ("34;1m" ++ˢ (s ++ˢ (csi ++ˢ "0;22m")))
  paint true container s = csi ++ˢ ("35m" ++ˢ (s ++ˢ (csi ++ˢ "0m")))
  paint true numeral s = csi ++ˢ ("31m" ++ˢ (s ++ˢ (csi ++ˢ "0m")))
  paint true quoted s = csi ++ˢ ("33m" ++ˢ (s ++ˢ (csi ++ˢ "0m")))
  paint true constant s = csi ++ˢ ("36m" ++ˢ (s ++ˢ (csi ++ˢ "0m")))
  paintPlain : (hue : _) → (s : _) → paint false hue s ≡ s
  paintPlain hue s = refl
  paintName : (s : _) → paint true name s ≡ (csi ++ˢ ("34;1m" ++ˢ (s ++ˢ (csi ++ˢ "0;22m"))))
  paintName s = refl
  paintContainer : (s : _) → paint true container s ≡ (csi ++ˢ ("35m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  paintContainer s = refl
  paintNumeral : (s : _) → paint true numeral s ≡ (csi ++ˢ ("31m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  paintNumeral s = refl
  paintQuoted : (s : _) → paint true quoted s ≡ (csi ++ˢ ("33m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  paintQuoted s = refl
  paintConstant : (s : _) → paint true constant s ≡ (csi ++ˢ ("36m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  paintConstant s = refl
  renderPayload : Bool → Payload → String
  renderPayload c (atom null) = paint c constant "null"
  renderPayload c (atom (boolean true)) = paint c constant "true"
  renderPayload c (atom (boolean false)) = paint c constant "false"
  renderPayload c (atom (number n)) = paint c numeral n
  renderPayload c (atom (text s)) = paint c quoted (quoteForward s)
  renderPayload c arrayMark = paint c container "[]"
  renderPayload c objectMark = paint c container "{}"
  payloadNull : (c : _) → renderPayload c (atom null) ≡ paint c constant "null"
  payloadNull c = refl
  payloadTrue : (c : _) → renderPayload c (atom (boolean true)) ≡ paint c constant "true"
  payloadTrue c = refl
  payloadFalse : (c : _) → renderPayload c (atom (boolean false)) ≡ paint c constant "false"
  payloadFalse c = refl
  payloadNumber : (c : _) → (n : _) → renderPayload c (atom (number n)) ≡ paint c numeral n
  payloadNumber c n = refl
  payloadText : (c : _) → (s : _) → renderPayload c (atom (text s)) ≡ paint c quoted (quoteForward s)
  payloadText c s = refl
  payloadArray : (c : _) → renderPayload c arrayMark ≡ paint c container "[]"
  payloadArray c = refl
  payloadObject : (c : _) → renderPayload c objectMark ≡ paint c container "{}"
  payloadObject c = refl
  private
    renderProperty : Bool → String → Bool → String
    renderProperty c k true = "." ++ˢ paint c name k
    renderProperty c k false = paint c container "[" ++ˢ (paint c quoted (quoteForward k) ++ˢ paint c container "]")
  assignmentPart : Bool → Segment → String
  assignmentPart c (property k) = renderProperty c k (identifier (toList k))
  assignmentPart c (index i) = paint c container "[" ++ˢ (paint c numeral (Nat.show i) ++ˢ paint c container "]")
  assignmentSuffix : Bool → List Segment → String
  assignmentSuffix c [] = ""
  assignmentSuffix c (p ∷ ps) = assignmentPart c p ++ˢ assignmentSuffix c ps
  assignmentDotted : (c : _) → (k : _) → (identifier (toList k) ≡ true) → assignmentPart c (property k) ≡ ("." ++ˢ paint c name k)
  assignmentDotted c k allowed = cong (renderProperty c k) allowed
  assignmentBracketed : (c : _) → (k : _) → (identifier (toList k) ≡ false) → assignmentPart c (property k) ≡ (paint c container "[" ++ˢ (paint c quoted (quoteForward k) ++ˢ paint c container "]"))
  assignmentBracketed c k quotedKey = cong (renderProperty c k) quotedKey
  assignmentIndex : (c : _) → (i : _) → assignmentPart c (index i) ≡ (paint c container "[" ++ˢ (paint c numeral (Nat.show i) ++ˢ paint c container "]"))
  assignmentIndex c i = refl
  assignmentSuffixEmpty : (c : _) → assignmentSuffix c [] ≡ ""
  assignmentSuffixEmpty c = refl
  assignmentSuffixNext : (c : _) → (p : _) → (ps : _) → assignmentSuffix c (p ∷ ps) ≡ (assignmentPart c p ++ˢ assignmentSuffix c ps)
  assignmentSuffixNext c p ps = refl
  pairPart : Bool → Segment → String
  pairPart c (property k) = paint c quoted (quoteForward k)
  pairPart c (index i) = paint c numeral (Nat.show i)
  private
    joinParts : String → List Segment → String → String
    joinParts front [] tail = front
    joinParts front (p ∷ ps) tail = front ++ˢ ("," ++ˢ tail)
  pairParts : Bool → List Segment → String
  pairParts c [] = ""
  pairParts c (p ∷ ps) = joinParts (pairPart c p) ps (pairParts c ps)
  pairProperty : (c : _) → (k : _) → pairPart c (property k) ≡ paint c quoted (quoteForward k)
  pairProperty c k = refl
  pairIndex : (c : _) → (i : _) → pairPart c (index i) ≡ paint c numeral (Nat.show i)
  pairIndex c i = refl
  pairPartsEmpty : (c : _) → pairParts c [] ≡ ""
  pairPartsEmpty c = refl
  pairPartsSingle : (c : _) → (p : _) → pairParts c (p ∷ []) ≡ pairPart c p
  pairPartsSingle c p = refl
  pairPartsNext : (c : _) → (p : _) → (q : _) → (ps : _) → pairParts c (p ∷ (q ∷ ps)) ≡ (pairPart c p ++ˢ ("," ++ˢ pairParts c (q ∷ ps)))
  pairPartsNext c p q ps = refl
  renderLine : Notation → Bool → Statement → String
  renderLine assignments c (assignment ps r) = paint c name "json" ++ˢ (assignmentSuffix c ps ++ˢ (" = " ++ˢ (renderPayload c r ++ˢ ";\n")))
  renderLine pairs c (assignment ps r) = paint c container "[" ++ˢ (paint c container "[" ++ˢ (pairParts c ps ++ˢ (paint c container "]" ++ˢ ("," ++ˢ (renderPayload c r ++ˢ (paint c container "]" ++ˢ "\n"))))))
  renderAssignment : (c : _) → (ps : _) → (r : _) → renderLine assignments c (assignment ps r) ≡ (paint c name "json" ++ˢ (assignmentSuffix c ps ++ˢ (" = " ++ˢ (renderPayload c r ++ˢ ";\n"))))
  renderAssignment c ps r = refl
  renderPair : (c : _) → (ps : _) → (r : _) → renderLine pairs c (assignment ps r) ≡ (paint c container "[" ++ˢ (paint c container "[" ++ˢ (pairParts c ps ++ˢ (paint c container "]" ++ˢ ("," ++ˢ (renderPayload c r ++ˢ (paint c container "]" ++ˢ "\n")))))))
  renderPair c ps r = refl
  observedColor : renderLine pairs true (assignment [] (atom (boolean true))) ≡ (csi ++ˢ ("35m[" ++ˢ (csi ++ˢ ("0m" ++ˢ (csi ++ˢ ("35m[" ++ˢ (csi ++ˢ ("0m" ++ˢ (csi ++ˢ ("35m]" ++ˢ (csi ++ˢ ("0m," ++ˢ (csi ++ˢ ("36mtrue" ++ˢ (csi ++ˢ ("0m" ++ˢ (csi ++ˢ ("35m]" ++ˢ (csi ++ˢ "0m\n")))))))))))))))))))
  observedColor = refl
  compareText : List Char → List Char → Ordering
  compareText [] [] = equal
  compareText [] (c ∷ cs) = before
  compareText (c ∷ cs) [] = after
  compareText (c ∷ cs) (d ∷ ds) = if (toℕ c <ᵇ toℕ d) then before else (if (toℕ d <ᵇ toℕ c) then after else compareText cs ds)
  compareEmpty : compareText [] [] ≡ equal
  compareEmpty = refl
  compareLeftEmpty : (c : _) → (cs : _) → compareText [] (c ∷ cs) ≡ before
  compareLeftEmpty c cs = refl
  compareRightEmpty : (c : _) → (cs : _) → compareText (c ∷ cs) [] ≡ after
  compareRightEmpty c cs = refl
  compareNext : (c : _) → (cs : _) → (d : _) → (ds : _) → compareText (c ∷ cs) (d ∷ ds) ≡ (if (toℕ c <ᵇ toℕ d) then before else (if (toℕ d <ᵇ toℕ c) then after else compareText cs ds))
  compareNext c cs d ds = refl
  private
    placeKey : {V : Set} → (String × V) → (String × V) → List (String × V) → List (String × V) → Ordering → List (String × V)
    placeKey kv jw xs added before = kv ∷ (jw ∷ xs)
    placeKey kv jw xs added equal = kv ∷ (jw ∷ xs)
    placeKey kv jw xs added after = jw ∷ added
  insertKey : {V : Set} → (String → List Char) → (String × V) → List (String × V) → List (String × V)
  insertKey rank kv [] = kv ∷ []
  insertKey rank kv (jw ∷ xs) = placeKey kv jw xs (insertKey rank kv xs) (compareText (rank (proj₁ kv)) (rank (proj₁ jw)))
  orderKeys : {V : Set} → (String → List Char) → List (String × V) → List (String × V)
  orderKeys rank [] = []
  orderKeys rank (kv ∷ xs) = insertKey rank kv (orderKeys rank xs)
  insertEmpty : {V : Set} → (rank : _) → (kv : _) → insertKey {V} rank kv [] ≡ (kv ∷ [])
  insertEmpty rank kv = refl
  insertBefore : {V : Set} → (rank : _) → (k : _) → (v : _) → (j : _) → (w : _) → (xs : _) → (compareText (rank k) (rank j) ≡ before) → insertKey {V} rank (k , v) ((j , w) ∷ xs) ≡ ((k , v) ∷ ((j , w) ∷ xs))
  insertBefore rank k v j w xs ordered = cong (placeKey (k , v) (j , w) xs (insertKey rank (k , v) xs)) ordered
  insertEqual : {V : Set} → (rank : _) → (k : _) → (v : _) → (j : _) → (w : _) → (xs : _) → (compareText (rank k) (rank j) ≡ equal) → insertKey {V} rank (k , v) ((j , w) ∷ xs) ≡ ((k , v) ∷ ((j , w) ∷ xs))
  insertEqual rank k v j w xs ordered = cong (placeKey (k , v) (j , w) xs (insertKey rank (k , v) xs)) ordered
  insertAfter : {V : Set} → (rank : _) → (k : _) → (v : _) → (j : _) → (w : _) → (xs : _) → (compareText (rank k) (rank j) ≡ after) → insertKey {V} rank (k , v) ((j , w) ∷ xs) ≡ ((j , w) ∷ insertKey rank (k , v) xs)
  insertAfter rank k v j w xs ordered = cong (placeKey (k , v) (j , w) xs (insertKey rank (k , v) xs)) ordered
  orderKeysEmpty : {V : Set} → (rank : _) → orderKeys {V} rank [] ≡ []
  orderKeysEmpty rank = refl
  orderKeysNext : {V : Set} → (rank : _) → (kv : _) → (xs : _) → orderKeys {V} rank (kv ∷ xs) ≡ insertKey rank kv (orderKeys rank xs)
  orderKeysNext rank kv xs = refl
  private
    assignmentRank : String → List Char
    assignmentRank key = toList (assignmentPart false (property key))
  private
    sortedNames : {V : Set} → (dollar nested upper : V) → orderKeys assignmentRank (("a$" , dollar) ∷ (("a" , nested) ∷ (("A" , upper) ∷ []))) ≡ (("A" , upper) ∷ (("a" , nested) ∷ (("a$" , dollar) ∷ [])))
    sortedNames dollar nested upper = refl
  private
    sortedThroughDash : {V : Set} → (dash dollar nested upper : V) → orderKeys assignmentRank (("-" , dash) ∷ (("a$" , dollar) ∷ (("a" , nested) ∷ (("A" , upper) ∷ [])))) ≡ (("A" , upper) ∷ (("a" , nested) ∷ (("a$" , dollar) ∷ (("-" , dash) ∷ []))))
    sortedThroughDash dash dollar nested upper = trans (cong (insertKey assignmentRank ("-" , dash)) (sortedNames dollar nested upper)) refl
  private
    sortedThroughBang : {V : Set} → (bang dash dollar nested upper : V) → orderKeys assignmentRank (("-!" , bang) ∷ (("-" , dash) ∷ (("a$" , dollar) ∷ (("a" , nested) ∷ (("A" , upper) ∷ []))))) ≡ (("A" , upper) ∷ (("a" , nested) ∷ (("a$" , dollar) ∷ (("-!" , bang) ∷ (("-" , dash) ∷ [])))))
    sortedThroughBang bang dash dollar nested upper = trans (cong (insertKey assignmentRank ("-!" , bang)) (sortedThroughDash dash dollar nested upper)) refl
  private
    sortedThroughSpace : {V : Set} → (space bang dash dollar nested upper : V) → orderKeys assignmentRank (("- " , space) ∷ (("-!" , bang) ∷ (("-" , dash) ∷ (("a$" , dollar) ∷ (("a" , nested) ∷ (("A" , upper) ∷ [])))))) ≡ (("A" , upper) ∷ (("a" , nested) ∷ (("a$" , dollar) ∷ (("- " , space) ∷ (("-!" , bang) ∷ (("-" , dash) ∷ []))))))
    sortedThroughSpace space bang dash dollar nested upper = trans (cong (insertKey assignmentRank ("- " , space)) (sortedThroughBang bang dash dollar nested upper)) refl
  sortedKeyOrder : {V : Set} → (question space bang dash dollar nested upper : V) → orderKeys (λ key → toList (assignmentPart false (property key))) (("-?" , question) ∷ (("- " , space) ∷ (("-!" , bang) ∷ (("-" , dash) ∷ (("a$" , dollar) ∷ (("a" , nested) ∷ (("A" , upper) ∷ []))))))) ≡ (("A" , upper) ∷ (("a" , nested) ∷ (("a$" , dollar) ∷ (("- " , space) ∷ (("-!" , bang) ∷ (("-" , dash) ∷ (("-?" , question) ∷ [])))))))
  sortedKeyOrder question space bang dash dollar nested upper = trans (cong (insertKey assignmentRank ("-?" , question)) (sortedThroughSpace space bang dash dollar nested upper)) refl
  duplicateKeyOrder : {V : Set} → (a b : V) → orderKeys (λ key → toList (assignmentPart false (property key))) (("a" , a) ∷ (("b" , b) ∷ [])) ≡ (("a" , a) ∷ (("b" , b) ∷ []))
  duplicateKeyOrder a b = refl
  shownSortedRows : foldr _++ˢ_ "" (map (renderLine assignments false) (assignment [] objectMark ∷ (assignment (property "A" ∷ []) (atom (number "7")) ∷ (assignment (property "a" ∷ []) objectMark ∷ (assignment (property "a" ∷ (property "-?" ∷ [])) (atom (number "6")) ∷ (assignment (property "a$" ∷ []) (atom (number "5")) ∷ (assignment (property "- " ∷ []) (atom (number "2")) ∷ (assignment (property "-!" ∷ []) (atom (number "3")) ∷ (assignment (property "-" ∷ []) (atom (number "1")) ∷ (assignment (property "-?" ∷ []) (atom (number "4")) ∷ [])))))))))) ≡ "json = {};\njson.A = 7;\njson.a = {};\njson.a[\"-?\"] = 6;\njson.a$ = 5;\njson[\"- \"] = 2;\njson[\"-!\"] = 3;\njson[\"-\"] = 1;\njson[\"-?\"] = 4;\n"
  shownSortedRows = refl
  shownEscapingRows : foldr _++ˢ_ "" (map (renderLine pairs false) (assignment [] objectMark ∷ (assignment (property (fromList ('x' ∷ (fromℕ 11 ∷ (fromℕ 8232 ∷ (fromℕ 133 ∷ []))))) ∷ []) (atom (text (fromList (fromℕ 11 ∷ (fromℕ 31 ∷ (fromℕ 127 ∷ (fromℕ 133 ∷ (fromℕ 8232 ∷ (fromℕ 8233 ∷ toList "<&>/"))))))))) ∷ []))) ≡ "[[],{}]\n[[\"x\\u000B\\u2028\\u0085\"],\"\\u000B\\u001F\\u007F\\u0085\\u2028\\u2029<&>/\"]\n"
  shownEscapingRows = refl
  shownDuplicateRows : foldr _++ˢ_ "" (map (renderLine assignments false) (assignment [] objectMark ∷ (assignment (property "a" ∷ []) objectMark ∷ (assignment (property "a" ∷ (property "z" ∷ [])) (atom (number "3")) ∷ (assignment (property "b" ∷ []) (atom (number "2")) ∷ []))))) ≡ "json = {};\njson.a = {};\njson.a.z = 3;\njson.b = 2;\n"
  shownDuplicateRows = refl
  shownSeedRows : foldr _++ˢ_ "" (map (renderLine assignments false) (assignment [] arrayMark ∷ (assignment (index 0 ∷ []) (atom (text (fromList (toList "λ<&>" ++ (fromℕ 8232 ∷ []))))) ∷ (assignment (index 1 ∷ []) objectMark ∷ [])))) ≡ "json = [];\njson[0] = \"λ<&>\\u2028\";\njson[1] = {};\n"
  shownSeedRows = refl
  shownNumberRows : foldr _++ˢ_ "" (map (renderLine assignments false) (assignment [] (atom (number "-94.00e+2")) ∷ [])) ≡ "json = -94.00e+2;\n"
  shownNumberRows = refl
  shownStreamTwelveRows : foldr _++ˢ_ "" (map (renderLine pairs false) (assignment (index 0 ∷ []) (atom (number "12")) ∷ [])) ≡ "[[0],12]\n"
  shownStreamTwelveRows = refl
  shownStreamTrueRows : foldr _++ˢ_ "" (map (renderLine pairs false) (assignment (index 1 ∷ []) (atom (boolean true)) ∷ [])) ≡ "[[1],true]\n"
  shownStreamTrueRows = refl
  shownOnlyTrueRows : foldr _++ˢ_ "" (map (renderLine assignments false) (assignment (index 0 ∷ []) (atom (boolean true)) ∷ [])) ≡ "json[0] = true;\n"
  shownOnlyTrueRows = refl
  pairOpening : renderLine pairs false (assignment [] arrayMark) ≡ "[[],[]]\n"
  pairOpening = refl
  assignmentOpening : renderLine assignments false (assignment [] arrayMark) ≡ "json = [];\n"
  assignmentOpening = refl
