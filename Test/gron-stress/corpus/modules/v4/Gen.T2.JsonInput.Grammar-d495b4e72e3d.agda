module Gen.T2.JsonInput.Grammar where

  open import Agda.Builtin.Char using (primCharEquality; primNatToChar)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (Bool; false; true; _∧_; _∨_)
  open import Data.Char using (Char; toℕ)
  open import Data.List using (List; []; _∷_; [_]; _++_; any; take)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_)
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  data Expectation : Set where
    valueStart : Expectation
    inWord : String → Char → Expectation
    objectKey : Expectation
    afterKey : Expectation
    afterMember : Expectation
    afterElement : Expectation
    integerDigit : Expectation
    fractionalDigit : Expectation
    exponentDigit : Expectation
    insideString : Expectation
    afterEscape : Expectation
    unicodeDigit : Expectation
    afterDocument : Expectation
    exceededDepth : Expectation
  data Fault : Set where
    missingDocument : Fault
    incompleteDocument : Fault
    unexpected : Char → Expectation → Fault
  data Prefix (A : Set) : Set where
    consumed : A → List Char → Prefix A
    failed : Fault → Prefix A
  record Comparison : Set where
    constructor comparison
    field
      charRefl : (c : Char) → primCharEquality c c ≡ true
      charReflects : (c d : Char) → (primCharEquality c d ≡ true) → c ≡ d
      stringRefl : (s : String) → primStringEquality s s ≡ true
      stringReflects : (s t : String) → (primStringEquality s t ≡ true) → s ≡ t
  record Layout : Set where
    constructor layoutRules
    field
      isSpace : Char → Bool
      spaceClass : (c : Char) → isSpace c ≡ (primCharEquality c ' ' ∨ (primCharEquality c '	' ∨ (primCharEquality c '\r' ∨ primCharEquality c '\n')))
      trimSpace : List Char → List Char
      trimEmpty : trimSpace [] ≡ []
      trimHead : (c : Char) → (xs : List Char) → (isSpace c ≡ true) → trimSpace (c ∷ xs) ≡ trimSpace xs
      keepHead : (c : Char) → (xs : List Char) → (isSpace c ≡ false) → trimSpace (c ∷ xs) ≡ (c ∷ xs)
  record Constructors (A : Set) : Set where
    constructor constructors
    field
      nullValue : A
      booleanValue : Bool → A
      numericValue : String → A
      textValue : String → A
      objectValue : List (String × A) → A
      arrayValue : List A → A
  postulate
    decimalDigit : Char → Bool
  postulate
    hexadecimalDigit : Char → Maybe ℕ
  postulate
    hexPrefix : ℕ → ℕ → List Char → Prefix ℕ
  postulate
    isHighSurrogate : ℕ → Bool
  postulate
    isLowSurrogate : ℕ → Bool
  postulate
    utf16Escape : Comparison → ℕ → List Char → Prefix Char
  postulate
    escapePrefix : Comparison → List Char → Prefix Char
  postulate
    stringBody : Comparison → List Char → Prefix String
  postulate
    decimalRange : (c : _) → decimalDigit c ≡ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))
  postulate
    hexDecimal : (c : _) → (decimalDigit c ≡ true) → hexadecimalDigit c ≡ just (toℕ c ∸ 48)
  postulate
    hexUppercase : (c : _) → (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 71)) ≡ true) → hexadecimalDigit c ≡ just (toℕ c ∸ 55)
  postulate
    hexLowercase : (c : _) → (((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 103)) ≡ true) → hexadecimalDigit c ≡ just (toℕ c ∸ 87)
  postulate
    nonHex : (c : _) → ((decimalDigit c ∨ (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 71)) ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 103)))) ≡ false) → hexadecimalDigit c ≡ nothing
  postulate
    hexComplete : (acc : _) → (xs : _) → hexPrefix 0 acc xs ≡ consumed acc xs
  postulate
    hexIncomplete : (n : _) → (acc : _) → hexPrefix (suc n) acc [] ≡ failed incompleteDocument
  postulate
    hexUnexpected : (n : _) → (acc : _) → (c : _) → (xs : _) → (hexadecimalDigit c ≡ nothing) → hexPrefix (suc n) acc (c ∷ xs) ≡ failed (unexpected c unicodeDigit)
  postulate
    hexNext : (n : _) → (acc : _) → (c : _) → (xs : _) → (d : _) → (hexadecimalDigit c ≡ just d) → hexPrefix (suc n) acc (c ∷ xs) ≡ hexPrefix n ((16 * acc) + d) xs
  postulate
    highRange : (n : _) → isHighSurrogate n ≡ ((55295 <ᵇ n) ∧ (n <ᵇ 56320))
  postulate
    lowRange : (n : _) → isLowSurrogate n ≡ ((56319 <ᵇ n) ∧ (n <ᵇ 57344))
  postulate
    ordinaryUnit : (eqs : Comparison) → (n : _) → (xs : _) → ((n <ᵇ 65536) ≡ true) → ((isHighSurrogate n ∨ isLowSurrogate n) ≡ false) → utf16Escape eqs n xs ≡ consumed (primNatToChar n) xs
  postulate
    isolatedLow : (eqs : Comparison) → (n : _) → (xs : _) → (isLowSurrogate n ≡ true) → utf16Escape eqs n xs ≡ consumed (primNatToChar 65533) xs
  postulate
    noSecondUnit : (eqs : Comparison) → (n : _) → (xs : _) → (isHighSurrogate n ≡ true) → (take 2 xs ≢ ('\\' ∷ ('u' ∷ []))) → utf16Escape eqs n xs ≡ consumed (primNatToChar 65533) xs
  postulate
    malformedSecondUnit : (eqs : Comparison) → (n : _) → (xs : _) → (fault : _) → (isHighSurrogate n ≡ true) → (hexPrefix 4 0 xs ≡ failed fault) → utf16Escape eqs n ('\\' ∷ ('u' ∷ xs)) ≡ consumed (primNatToChar 65533) ('\\' ∷ ('u' ∷ xs))
  postulate
    unmatchedSecondUnit : (eqs : Comparison) → (n : _) → (m : _) → (xs : _) → (rest : _) → (isHighSurrogate n ≡ true) → (hexPrefix 4 0 xs ≡ consumed m rest) → (isLowSurrogate m ≡ false) → utf16Escape eqs n ('\\' ∷ ('u' ∷ xs)) ≡ consumed (primNatToChar 65533) ('\\' ∷ ('u' ∷ xs))
  postulate
    pairedUnits : (eqs : Comparison) → (n : _) → (m : _) → (xs : _) → (rest : _) → (isHighSurrogate n ≡ true) → (hexPrefix 4 0 xs ≡ consumed m rest) → (isLowSurrogate m ≡ true) → utf16Escape eqs n ('\\' ∷ ('u' ∷ xs)) ≡ consumed (primNatToChar (65536 + ((1024 * (n ∸ 55296)) + (m ∸ 56320)))) rest
  postulate
    absentEscape : (eqs : Comparison) → escapePrefix eqs [] ≡ failed incompleteDocument
  postulate
    quoteEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('\"' ∷ xs) ≡ consumed '\"' xs
  postulate
    slashEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('/' ∷ xs) ≡ consumed '/' xs
  postulate
    backslashEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('\\' ∷ xs) ≡ consumed '\\' xs
  postulate
    backspaceEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('b' ∷ xs) ≡ consumed (primNatToChar 8) xs
  postulate
    formfeedEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('f' ∷ xs) ≡ consumed (primNatToChar 12) xs
  postulate
    newlineEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('n' ∷ xs) ≡ consumed '\n' xs
  postulate
    returnEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('r' ∷ xs) ≡ consumed '\r' xs
  postulate
    tabEscape : (eqs : Comparison) → (xs : _) → escapePrefix eqs ('t' ∷ xs) ≡ consumed '	' xs
  postulate
    escapedUnit : (eqs : Comparison) → (xs : _) → (n : _) → (rest : _) → (hexPrefix 4 0 xs ≡ consumed n rest) → escapePrefix eqs ('u' ∷ xs) ≡ utf16Escape eqs n rest
  postulate
    malformedUnit : (eqs : Comparison) → (xs : _) → (err : _) → (hexPrefix 4 0 xs ≡ failed err) → escapePrefix eqs ('u' ∷ xs) ≡ failed err
  postulate
    unknownEscape : (eqs : Comparison) → (c : _) → (xs : _) → (any (primCharEquality c) (toList "\"/\\bfnrtu") ≡ false) → escapePrefix eqs (c ∷ xs) ≡ failed (unexpected c afterEscape)
  postulate
    bodyUnclosed : (eqs : Comparison) → stringBody eqs [] ≡ failed incompleteDocument
  postulate
    bodyClosed : (eqs : Comparison) → (xs : _) → stringBody eqs ('\"' ∷ xs) ≡ consumed "" xs
  postulate
    bodyControl : (eqs : Comparison) → (c : _) → (xs : _) → ((toℕ c <ᵇ 32) ≡ true) → stringBody eqs (c ∷ xs) ≡ failed (unexpected c insideString)
  postulate
    bodyCharacter : (eqs : Comparison) → (c : _) → (xs : _) → (s : _) → (rest : _) → ((toℕ c <ᵇ 32) ≡ false) → (any (primCharEquality c) (toList "\"\\") ≡ false) → (stringBody eqs xs ≡ consumed s rest) → stringBody eqs (c ∷ xs) ≡ consumed (fromList ([ c ]) ++ˢ s) rest
  postulate
    bodyAfterCharacterError : (eqs : Comparison) → (c : _) → (xs : _) → (e : _) → ((toℕ c <ᵇ 32) ≡ false) → (any (primCharEquality c) (toList "\"\\") ≡ false) → (stringBody eqs xs ≡ failed e) → stringBody eqs (c ∷ xs) ≡ failed e
  postulate
    bodyEscape : (eqs : Comparison) → (xs : _) → (c : _) → (mid : _) → (s : _) → (rest : _) → (escapePrefix eqs xs ≡ consumed c mid) → (stringBody eqs mid ≡ consumed s rest) → stringBody eqs ('\\' ∷ xs) ≡ consumed (fromList ([ c ]) ++ˢ s) rest
  postulate
    bodyEscapeError : (eqs : Comparison) → (xs : _) → (e : _) → (escapePrefix eqs xs ≡ failed e) → stringBody eqs ('\\' ∷ xs) ≡ failed e
  postulate
    bodyAfterEscapeError : (eqs : Comparison) → (xs : _) → (c : _) → (mid : _) → (e : _) → (escapePrefix eqs xs ≡ consumed c mid) → (stringBody eqs mid ≡ failed e) → stringBody eqs ('\\' ∷ xs) ≡ failed e
  postulate
    digitSpan : List Char → List Char × List Char
  postulate
    requiredDigits : Expectation → List Char → Prefix (List Char)
  postulate
    unsignedInteger : Comparison → List Char → Prefix (List Char)
  postulate
    signedInteger : Comparison → List Char → Prefix (List Char)
  postulate
    fraction : Comparison → List Char → Prefix (List Char)
  postulate
    exponentBody : Comparison → List Char → Prefix (List Char)
  postulate
    exponent : Comparison → List Char → Prefix (List Char)
  postulate
    numberPrefix : Comparison → List Char → Prefix String
  postulate
    literalSuffix : {A : Set} → Comparison → A → String → List Char → List Char → Prefix A
  postulate
    matchingValues : {A : Set} → Comparison → String → List (String × A) → List A
  postulate
    resolveFields : {A : Set} → Comparison → List (String × A) → List (String × A)
  postulate
    noDigitInput : digitSpan [] ≡ ([] , [])
  postulate
    stopDigitSpan : (c : _) → (xs : _) → (decimalDigit c ≡ false) → digitSpan (c ∷ xs) ≡ ([] , (c ∷ xs))
  postulate
    extendDigitSpan : (c : _) → (xs : _) → (ds : _) → (rest : _) → (decimalDigit c ≡ true) → (digitSpan xs ≡ (ds , rest)) → digitSpan (c ∷ xs) ≡ ((c ∷ ds) , rest)
  postulate
    missingDigits : (site : _) → requiredDigits site [] ≡ failed incompleteDocument
  postulate
    rejectedDigits : (site : _) → (c : _) → (xs : _) → (decimalDigit c ≡ false) → requiredDigits site (c ∷ xs) ≡ failed (unexpected c site)
  postulate
    acceptedDigits : (site : _) → (c : _) → (xs : _) → (ds : _) → (rest : _) → (decimalDigit c ≡ true) → (digitSpan xs ≡ (ds , rest)) → requiredDigits site (c ∷ xs) ≡ consumed (c ∷ ds) rest
  postulate
    zeroInteger : (eqs : Comparison) → (xs : _) → unsignedInteger eqs ('0' ∷ xs) ≡ consumed ([ '0' ]) xs
  postulate
    otherInteger : (eqs : Comparison) → (xs : _) → (take 1 xs ≢ ([ '0' ])) → unsignedInteger eqs xs ≡ requiredDigits integerDigit xs
  postulate
    positiveInteger : (eqs : Comparison) → (xs : _) → (take 1 xs ≢ ([ '-' ])) → signedInteger eqs xs ≡ unsignedInteger eqs xs
  postulate
    negativeInteger : (eqs : Comparison) → (xs : _) → (ds : _) → (rest : _) → (unsignedInteger eqs xs ≡ consumed ds rest) → signedInteger eqs ('-' ∷ xs) ≡ consumed ('-' ∷ ds) rest
  postulate
    negativeIntegerError : (eqs : Comparison) → (xs : _) → (e : _) → (unsignedInteger eqs xs ≡ failed e) → signedInteger eqs ('-' ∷ xs) ≡ failed e
  postulate
    noFraction : (eqs : Comparison) → (xs : _) → (take 1 xs ≢ ([ '.' ])) → fraction eqs xs ≡ consumed [] xs
  postulate
    fractionWithDigits : (eqs : Comparison) → (xs : _) → (ds : _) → (rest : _) → (requiredDigits fractionalDigit xs ≡ consumed ds rest) → fraction eqs ('.' ∷ xs) ≡ consumed ('.' ∷ ds) rest
  postulate
    fractionWithoutDigits : (eqs : Comparison) → (xs : _) → (e : _) → (requiredDigits fractionalDigit xs ≡ failed e) → fraction eqs ('.' ∷ xs) ≡ failed e
  postulate
    exponentWithoutSign : (eqs : Comparison) → (xs : _) → (take 1 xs ≢ ([ '+' ])) → (take 1 xs ≢ ([ '-' ])) → exponentBody eqs xs ≡ requiredDigits exponentDigit xs
  postulate
    exponentWithSign : (eqs : Comparison) → (c : _) → (xs : _) → (ds : _) → (rest : _) → ((primCharEquality c '+' ∨ primCharEquality c '-') ≡ true) → (requiredDigits exponentDigit xs ≡ consumed ds rest) → exponentBody eqs (c ∷ xs) ≡ consumed (c ∷ ds) rest
  postulate
    exponentSignError : (eqs : Comparison) → (c : _) → (xs : _) → (e : _) → ((primCharEquality c '+' ∨ primCharEquality c '-') ≡ true) → (requiredDigits exponentDigit xs ≡ failed e) → exponentBody eqs (c ∷ xs) ≡ failed e
  postulate
    noExponent : (eqs : Comparison) → (xs : _) → (take 1 xs ≢ ([ 'e' ])) → (take 1 xs ≢ ([ 'E' ])) → exponent eqs xs ≡ consumed [] xs
  postulate
    exponentWithDigits : (eqs : Comparison) → (c : _) → (xs : _) → (ds : _) → (rest : _) → ((primCharEquality c 'e' ∨ primCharEquality c 'E') ≡ true) → (exponentBody eqs xs ≡ consumed ds rest) → exponent eqs (c ∷ xs) ≡ consumed (c ∷ ds) rest
  postulate
    exponentWithoutDigits : (eqs : Comparison) → (c : _) → (xs : _) → (e : _) → ((primCharEquality c 'e' ∨ primCharEquality c 'E') ≡ true) → (exponentBody eqs xs ≡ failed e) → exponent eqs (c ∷ xs) ≡ failed e
  postulate
    numberWithParts : (eqs : Comparison) → (xs : _) → (i : _) → (r : _) → (f : _) → (q : _) → (d : _) → (rest : _) → (signedInteger eqs xs ≡ consumed i r) → (fraction eqs r ≡ consumed f q) → (exponent eqs q ≡ consumed d rest) → numberPrefix eqs xs ≡ consumed (fromList (i ++ (f ++ d))) rest
  postulate
    numberIntegerError : (eqs : Comparison) → (xs : _) → (e : _) → (signedInteger eqs xs ≡ failed e) → numberPrefix eqs xs ≡ failed e
  postulate
    numberFractionError : (eqs : Comparison) → (xs : _) → (i : _) → (r : _) → (e : _) → (signedInteger eqs xs ≡ consumed i r) → (fraction eqs r ≡ failed e) → numberPrefix eqs xs ≡ failed e
  postulate
    numberExponentError : (eqs : Comparison) → (xs : _) → (i : _) → (r : _) → (f : _) → (q : _) → (e : _) → (signedInteger eqs xs ≡ consumed i r) → (fraction eqs r ≡ consumed f q) → (exponent eqs q ≡ failed e) → numberPrefix eqs xs ≡ failed e
  postulate
    wordComplete : {A : Set} → (eqs : Comparison) → (a : _) → (word : _) → (xs : _) → literalSuffix {A} eqs a word [] xs ≡ consumed a xs
  postulate
    wordIncomplete : {A : Set} → (eqs : Comparison) → (a : _) → (word : _) → (c : _) → (cs : _) → literalSuffix {A} eqs a word (c ∷ cs) [] ≡ failed incompleteDocument
  postulate
    wordMatched : {A : Set} → (eqs : Comparison) → (a : _) → (word : _) → (c : _) → (cs : _) → (xs : _) → literalSuffix {A} eqs a word (c ∷ cs) (c ∷ xs) ≡ literalSuffix {A} eqs a word cs xs
  postulate
    wordMismatch : {A : Set} → (eqs : Comparison) → (a : _) → (word : _) → (c : _) → (d : _) → (cs : _) → (xs : _) → (primCharEquality c d ≡ false) → literalSuffix {A} eqs a word (c ∷ cs) (d ∷ xs) ≡ failed (unexpected d (inWord word c))
  postulate
    noMatchingValues : {A : Set} → (eqs : Comparison) → (k : _) → matchingValues {A} eqs k [] ≡ []
  postulate
    nextMatchingValue : {A : Set} → (eqs : Comparison) → (k : _) → (v : _) → (fields : _) → matchingValues {A} eqs k ((k , v) ∷ fields) ≡ (matchingValues {A} eqs k fields ++ ([ v ]))
  postulate
    otherMatchingValue : {A : Set} → (eqs : Comparison) → (k : _) → (l : _) → (v : _) → (fields : _) → (primStringEquality k l ≡ false) → matchingValues {A} eqs k ((l , v) ∷ fields) ≡ matchingValues {A} eqs k fields
  postulate
    resolveEmpty : {A : Set} → (eqs : Comparison) → resolveFields {A} eqs [] ≡ []
  postulate
    resolveAbsent : {A : Set} → (eqs : Comparison) → (k : _) → (fields : _) → (matchingValues {A} eqs k fields ≡ []) → matchingValues {A} eqs k (resolveFields {A} eqs fields) ≡ []
  postulate
    resolveNewest : {A : Set} → (eqs : Comparison) → (k : _) → (v : _) → (older : _) → (fields : _) → (matchingValues {A} eqs k fields ≡ (v ∷ older)) → matchingValues {A} eqs k (resolveFields {A} eqs fields) ≡ ([ v ])
  postulate
    valueAtDepth : {A : Set} → Comparison → Layout → Constructors A → ℕ → List Char → Prefix A
  postulate
    arrayItems : {A : Set} → Comparison → Layout → Constructors A → ℕ → Bool → List Char → Prefix (List A)
  postulate
    arrayTail : {A : Set} → Comparison → Layout → Constructors A → ℕ → List Char → Prefix (List A)
  postulate
    objectItems : {A : Set} → Comparison → Layout → Constructors A → ℕ → Bool → List Char → Prefix (List (String × A))
  postulate
    objectTail : {A : Set} → Comparison → Layout → Constructors A → ℕ → List Char → Prefix (List (String × A))
  postulate
    memberPrefix : {A : Set} → Comparison → Layout → Constructors A → ℕ → List Char → Prefix (String × A)
  postulate
    memberValue : {A : Set} → Comparison → Layout → Constructors A → ℕ → List Char → Prefix A
  postulate
    emptyPrefix : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → valueAtDepth {A} eqs layout build budget [] ≡ failed missingDocument
  postulate
    leadingSpace : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (c : _) → (xs : _) → (Layout.isSpace layout c ≡ true) → valueAtDepth {A} eqs layout build budget (c ∷ xs) ≡ valueAtDepth {A} eqs layout build budget xs
  postulate
    unexpectedStart : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (c : _) → (xs : _) → ((Layout.isSpace layout c ∨ (decimalDigit c ∨ any (primCharEquality c) (toList "-tfn\"[{"))) ≡ false) → valueAtDepth {A} eqs layout build budget (c ∷ xs) ≡ failed (unexpected c valueStart)
  postulate
    truePrefix : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → valueAtDepth {A} eqs layout build budget ('t' ∷ xs) ≡ literalSuffix {A} eqs (Constructors.booleanValue build true) "true" (toList "rue") xs
  postulate
    falsePrefix : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → valueAtDepth {A} eqs layout build budget ('f' ∷ xs) ≡ literalSuffix {A} eqs (Constructors.booleanValue build false) "false" (toList "alse") xs
  postulate
    nullPrefix : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → valueAtDepth {A} eqs layout build budget ('n' ∷ xs) ≡ literalSuffix {A} eqs (Constructors.nullValue build) "null" (toList "ull") xs
  postulate
    numberValue : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (c : _) → (xs : _) → (s : _) → (rest : _) → ((decimalDigit c ∨ primCharEquality c '-') ≡ true) → (numberPrefix eqs (c ∷ xs) ≡ consumed s rest) → valueAtDepth {A} eqs layout build budget (c ∷ xs) ≡ consumed (Constructors.numericValue build s) rest
  postulate
    numberValueError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (c : _) → (xs : _) → (e : _) → ((decimalDigit c ∨ primCharEquality c '-') ≡ true) → (numberPrefix eqs (c ∷ xs) ≡ failed e) → valueAtDepth {A} eqs layout build budget (c ∷ xs) ≡ failed e
  postulate
    stringValue : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (s : _) → (rest : _) → (stringBody eqs xs ≡ consumed s rest) → valueAtDepth {A} eqs layout build budget ('\"' ∷ xs) ≡ consumed (Constructors.textValue build s) rest
  postulate
    stringValueError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (e : _) → (stringBody eqs xs ≡ failed e) → valueAtDepth {A} eqs layout build budget ('\"' ∷ xs) ≡ failed e
  postulate
    arrayValue : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (vs : _) → (rest : _) → (arrayItems {A} eqs layout build budget true xs ≡ consumed vs rest) → valueAtDepth {A} eqs layout build (suc budget) ('[' ∷ xs) ≡ consumed (Constructors.arrayValue build vs) rest
  postulate
    arrayValueError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (e : _) → (arrayItems {A} eqs layout build budget true xs ≡ failed e) → valueAtDepth {A} eqs layout build (suc budget) ('[' ∷ xs) ≡ failed e
  postulate
    objectValue : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (fields : _) → (rest : _) → (objectItems {A} eqs layout build budget true xs ≡ consumed fields rest) → valueAtDepth {A} eqs layout build (suc budget) ('{' ∷ xs) ≡ consumed (Constructors.objectValue build (resolveFields {A} eqs fields)) rest
  postulate
    objectValueError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (e : _) → (objectItems {A} eqs layout build budget true xs ≡ failed e) → valueAtDepth {A} eqs layout build (suc budget) ('{' ∷ xs) ≡ failed e
  postulate
    arrayAtDepthLimit : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (xs : _) → valueAtDepth {A} eqs layout build zero ('[' ∷ xs) ≡ failed (unexpected '[' exceededDepth)
  postulate
    objectAtDepthLimit : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (xs : _) → valueAtDepth {A} eqs layout build zero ('{' ∷ xs) ≡ failed (unexpected '{' exceededDepth)
  postulate
    arrayItemsEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (Layout.trimSpace layout xs ≡ []) → arrayItems {A} eqs layout build budget empty xs ≡ failed incompleteDocument
  postulate
    arrayEmpty : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (']' ∷ rest)) → arrayItems {A} eqs layout build budget true xs ≡ consumed [] rest
  postulate
    arrayItem : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (v : _) → (mid : _) → (vs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c ']') ≡ false) → (valueAtDepth {A} eqs layout build budget (c ∷ cs) ≡ consumed v mid) → (arrayTail {A} eqs layout build budget mid ≡ consumed vs rest) → arrayItems {A} eqs layout build budget empty xs ≡ consumed (v ∷ vs) rest
  postulate
    arrayItemError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (e : _) → (Layout.trimSpace layout xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c ']') ≡ false) → (valueAtDepth {A} eqs layout build budget (c ∷ cs) ≡ failed e) → arrayItems {A} eqs layout build budget empty xs ≡ failed e
  postulate
    arrayAfterItemError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (v : _) → (mid : _) → (e : _) → (Layout.trimSpace layout xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c ']') ≡ false) → (valueAtDepth {A} eqs layout build budget (c ∷ cs) ≡ consumed v mid) → (arrayTail {A} eqs layout build budget mid ≡ failed e) → arrayItems {A} eqs layout build budget empty xs ≡ failed e
  postulate
    arrayTailEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (Layout.trimSpace layout xs ≡ []) → arrayTail {A} eqs layout build budget xs ≡ failed incompleteDocument
  postulate
    arrayTailClose : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (']' ∷ rest)) → arrayTail {A} eqs layout build budget xs ≡ consumed [] rest
  postulate
    arrayTailComma : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (',' ∷ rest)) → arrayTail {A} eqs layout build budget xs ≡ arrayItems {A} eqs layout build budget false rest
  postulate
    arrayTailUnexpected : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (c : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (c ∷ rest)) → ((primCharEquality c ']' ∨ primCharEquality c ',') ≡ false) → arrayTail {A} eqs layout build budget xs ≡ failed (unexpected c afterElement)
  postulate
    objectItemsEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (Layout.trimSpace layout xs ≡ []) → objectItems {A} eqs layout build budget empty xs ≡ failed incompleteDocument
  postulate
    objectEmpty : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ ('}' ∷ rest)) → objectItems {A} eqs layout build budget true xs ≡ consumed [] rest
  postulate
    objectItem : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (entry : _) → (mid : _) → (fields : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c '}') ≡ false) → (memberPrefix {A} eqs layout build budget (c ∷ cs) ≡ consumed entry mid) → (objectTail {A} eqs layout build budget mid ≡ consumed fields rest) → objectItems {A} eqs layout build budget empty xs ≡ consumed (entry ∷ fields) rest
  postulate
    objectItemError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (e : _) → (Layout.trimSpace layout xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c '}') ≡ false) → (memberPrefix {A} eqs layout build budget (c ∷ cs) ≡ failed e) → objectItems {A} eqs layout build budget empty xs ≡ failed e
  postulate
    objectAfterItemError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (entry : _) → (mid : _) → (e : _) → (Layout.trimSpace layout xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c '}') ≡ false) → (memberPrefix {A} eqs layout build budget (c ∷ cs) ≡ consumed entry mid) → (objectTail {A} eqs layout build budget mid ≡ failed e) → objectItems {A} eqs layout build budget empty xs ≡ failed e
  postulate
    objectTailEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (Layout.trimSpace layout xs ≡ []) → objectTail {A} eqs layout build budget xs ≡ failed incompleteDocument
  postulate
    objectTailClose : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ ('}' ∷ rest)) → objectTail {A} eqs layout build budget xs ≡ consumed [] rest
  postulate
    objectTailComma : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (',' ∷ rest)) → objectTail {A} eqs layout build budget xs ≡ objectItems {A} eqs layout build budget false rest
  postulate
    objectTailUnexpected : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (c : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (c ∷ rest)) → ((primCharEquality c '}' ∨ primCharEquality c ',') ≡ false) → objectTail {A} eqs layout build budget xs ≡ failed (unexpected c afterMember)
  postulate
    memberEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → memberPrefix {A} eqs layout build budget [] ≡ failed incompleteDocument
  postulate
    memberBadStart : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (c : _) → (xs : _) → (primCharEquality c '\"' ≡ false) → memberPrefix {A} eqs layout build budget (c ∷ xs) ≡ failed (unexpected c objectKey)
  postulate
    memberWithValue : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (k : _) → (mid : _) → (v : _) → (rest : _) → (stringBody eqs xs ≡ consumed k mid) → (memberValue {A} eqs layout build budget mid ≡ consumed v rest) → memberPrefix {A} eqs layout build budget ('\"' ∷ xs) ≡ consumed (k , v) rest
  postulate
    memberKeyError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (e : _) → (stringBody eqs xs ≡ failed e) → memberPrefix {A} eqs layout build budget ('\"' ∷ xs) ≡ failed e
  postulate
    memberValueError : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (k : _) → (mid : _) → (e : _) → (stringBody eqs xs ≡ consumed k mid) → (memberValue {A} eqs layout build budget mid ≡ failed e) → memberPrefix {A} eqs layout build budget ('\"' ∷ xs) ≡ failed e
  postulate
    valueAfterColon : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (':' ∷ rest)) → (valueAtDepth {A} eqs layout build budget rest ≢ failed missingDocument) → memberValue {A} eqs layout build budget xs ≡ valueAtDepth {A} eqs layout build budget rest
  postulate
    valueEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (Layout.trimSpace layout xs ≡ []) → memberValue {A} eqs layout build budget xs ≡ failed incompleteDocument
  postulate
    valueAfterColonEOF : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (':' ∷ rest)) → (valueAtDepth {A} eqs layout build budget rest ≡ failed missingDocument) → memberValue {A} eqs layout build budget xs ≡ failed incompleteDocument
  postulate
    memberMissingColon : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → (budget : _) → (xs : _) → (c : _) → (rest : _) → (Layout.trimSpace layout xs ≡ (c ∷ rest)) → (primCharEquality c ':' ≡ false) → memberValue {A} eqs layout build budget xs ≡ failed (unexpected c afterKey)
  postulate
    leadingNumberExample : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → valueAtDepth eqs layout build 10000 (toList " 	\r\n1x") ≡ consumed (Constructors.numericValue build "1") ([ 'x' ])
  postulate
    leadingZeroExample : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → valueAtDepth eqs layout build 10000 (toList "[01]") ≡ failed (unexpected '1' afterElement)
  postulate
    exponentErrorExample : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → valueAtDepth eqs layout build 10000 (toList "[1e+]") ≡ failed (unexpected ']' exponentDigit)
  postulate
    surrogateExample : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → valueAtDepth eqs layout build 10000 (toList "[\"\\uD83D\\uDE00\",\"\\uD800\",\"\\uDC00\",\"\\uD800\\u0041\",\"a\\/b\"]") ≡ consumed (Constructors.arrayValue build (Constructors.textValue build (fromList ([ primNatToChar 128512 ])) ∷ (Constructors.textValue build (fromList ([ primNatToChar 65533 ])) ∷ (Constructors.textValue build (fromList ([ primNatToChar 65533 ])) ∷ (Constructors.textValue build (fromList (primNatToChar 65533 ∷ ([ 'A' ]))) ∷ ([ Constructors.textValue build "a/b" ])))))) []
  postulate
    nestedExample : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → valueAtDepth eqs layout build 10000 (toList "[[\"a\"],1][[\"b\"],2]") ≡ consumed (Constructors.arrayValue build (Constructors.arrayValue build ([ Constructors.textValue build "a" ]) ∷ ([ Constructors.numericValue build "1" ]))) (toList "[[\"b\"],2]")
  record RepeatedKeys {A : Set} (eqs : Comparison) (layout : Layout) (build : Constructors A) : Set where
    constructor repeatedKeys
    field
      selectedFields : List (String × A)
      repeatedKeyPrefix : valueAtDepth eqs layout build 10000 (toList "{\"a\":{\"x\":1},\"a\":{\"y\":2},\"\\u0062\":0,\"b\":1}") ≡ consumed (Constructors.objectValue build selectedFields) []
      latestA : matchingValues eqs "a" selectedFields ≡ (Constructors.objectValue build (("y" , Constructors.numericValue build "2") ∷ []) ∷ [])
      latestB : matchingValues eqs "b" selectedFields ≡ (Constructors.numericValue build "1" ∷ [])
  postulate
    repeatedKeyExample : {A : Set} → (eqs : Comparison) → (layout : Layout) → (build : Constructors A) → RepeatedKeys eqs layout build
