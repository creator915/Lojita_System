module Gen.T2.JsonInput where

  open import Agda.Builtin.Char using (primCharEquality; primNatToChar)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (Bool; false; true; _∧_; _∨_)
  open import Data.Char using (Char; toℕ)
  open import Data.List using (List; []; _∷_; [_]; _++_; any; take)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_; _≡ᵇ_)
  open import Data.Nat.DivMod using (_/_; _%_)
  open import Data.Product using (_×_; _,_)
  open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  data Json : Set where
    jsonNull : Json
    jsonBool : Bool → Json
    jsonNumber : String → Json
    jsonText : String → Json
    jsonObject : List (String × Json) → Json
    jsonArray : List Json → Json
  data Document : Set where
    parsed : Json → Document
    rejected : String → Document
  record StreamReply : Set where
    constructor streamReply
    field
      status : ℕ
      values : List Json
      diagnostic : String
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
  postulate
    whitespace : Char → Bool
  postulate
    jsonWhitespace : (c : _) → whitespace c ≡ (primCharEquality c ' ' ∨ (primCharEquality c '	' ∨ (primCharEquality c '\r' ∨ primCharEquality c '\n')))
  postulate
    skipWhitespace : List Char → List Char
  postulate
    skipEmpty : skipWhitespace [] ≡ []
  postulate
    skipSpace : (c : _) → (xs : _) → (whitespace c ≡ true) → skipWhitespace (c ∷ xs) ≡ skipWhitespace xs
  postulate
    keepNonspace : (c : _) → (xs : _) → (whitespace c ≡ false) → skipWhitespace (c ∷ xs) ≡ (c ∷ xs)
  postulate
    diagnosticGlyph : Char → String
  postulate
    printableAscii : (c : _) → (((31 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 127)) ≡ true) → (primCharEquality c '\'' ≡ false) → (primCharEquality c '\\' ≡ false) → diagnosticGlyph c ≡ fromList ([ c ])
  postulate
    apostropheGlyph : diagnosticGlyph '\'' ≡ "\\'"
  postulate
    backslashGlyph : diagnosticGlyph '\\' ≡ "\\\\"
  postulate
    bellGlyph : diagnosticGlyph (primNatToChar 7) ≡ "\\a"
  postulate
    verticalTabGlyph : diagnosticGlyph (primNatToChar 11) ≡ "\\v"
  postulate
    backspaceGlyph : diagnosticGlyph (primNatToChar 8) ≡ "\\b"
  postulate
    tabGlyph : diagnosticGlyph '	' ≡ "\\t"
  postulate
    newlineGlyph : diagnosticGlyph '\n' ≡ "\\n"
  postulate
    formfeedGlyph : diagnosticGlyph (primNatToChar 12) ≡ "\\f"
  postulate
    returnGlyph : diagnosticGlyph '\r' ≡ "\\r"
  postulate
    diagnosticNibble : ℕ → Char
  postulate
    decimalNibble : (n : _) → ((n <ᵇ 10) ≡ true) → diagnosticNibble n ≡ primNatToChar (48 + n)
  postulate
    alphabeticNibble : (n : _) → (((9 <ᵇ n) ∧ (n <ᵇ 16)) ≡ true) → diagnosticNibble n ≡ primNatToChar (87 + n)
  postulate
    hexControlGlyph : (c : _) → (((toℕ c <ᵇ 32) ∨ (toℕ c ≡ᵇ 127)) ≡ true) → (any (primCharEquality c) (primNatToChar 7 ∷ (primNatToChar 8 ∷ ('	' ∷ ('\n' ∷ (primNatToChar 11 ∷ (primNatToChar 12 ∷ ('\r' ∷ []))))))) ≡ false) → diagnosticGlyph c ≡ ("\\x" ++ˢ fromList (diagnosticNibble (toℕ c / 16) ∷ (diagnosticNibble (toℕ c % 16) ∷ [])))
  postulate
    glyphTwoBytes : (c : _) → (((127 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 2048)) ≡ true) → diagnosticGlyph c ≡ fromList ([ primNatToChar (192 + (toℕ c / 64)) ])
  postulate
    glyphThreeBytes : (c : _) → (((2047 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 65536)) ≡ true) → diagnosticGlyph c ≡ fromList ([ primNatToChar (224 + (toℕ c / 4096)) ])
  postulate
    glyphFourBytes : (c : _) → ((65535 <ᵇ toℕ c) ≡ true) → diagnosticGlyph c ≡ fromList ([ primNatToChar (240 + (toℕ c / 262144)) ])
  postulate
    contextText : Expectation → String
  postulate
    startingValueMessage : contextText valueStart ≡ " looking for beginning of value"
  postulate
    unfinishedWordMessage : (word : _) → (c : _) → contextText (inWord word c) ≡ (" in literal " ++ˢ (word ++ˢ (" (expecting '" ++ˢ (fromList ([ c ]) ++ˢ "')"))))
  postulate
    objectKeyMessage : contextText objectKey ≡ " looking for beginning of object key string"
  postulate
    colonMessage : contextText afterKey ≡ " after object key"
  postulate
    memberMessage : contextText afterMember ≡ " after object key:value pair"
  postulate
    elementMessage : contextText afterElement ≡ " after array element"
  postulate
    integerMessage : contextText integerDigit ≡ " in numeric literal"
  postulate
    fractionMessage : contextText fractionalDigit ≡ " after decimal point in numeric literal"
  postulate
    exponentMessage : contextText exponentDigit ≡ " in exponent of numeric literal"
  postulate
    stringMessage : contextText insideString ≡ " in string literal"
  postulate
    escapeMessage : contextText afterEscape ≡ " in string escape code"
  postulate
    unicodeMessage : contextText unicodeDigit ≡ " in \\u hexadecimal character escape"
  postulate
    trailingMessage : contextText afterDocument ≡ " after top-level value"
  postulate
    depthMessage : contextText exceededDepth ≡ " exceeded max depth"
  postulate
    faultText : Fault → String
  postulate
    missingMessage : faultText missingDocument ≡ "EOF"
  postulate
    incompleteMessage : faultText incompleteDocument ≡ "unexpected EOF"
  postulate
    invalidMessage : (c : _) → (site : _) → faultText (unexpected c site) ≡ ("invalid character '" ++ˢ (diagnosticGlyph c ++ˢ ("'" ++ˢ contextText site)))
  postulate
    decimalDigit : Char → Bool
  postulate
    decimalRange : (c : _) → decimalDigit c ≡ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))
  postulate
    hexadecimalDigit : Char → Maybe ℕ
  postulate
    hexDecimal : (c : _) → (decimalDigit c ≡ true) → hexadecimalDigit c ≡ just (toℕ c ∸ 48)
  postulate
    hexUppercase : (c : _) → (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 71)) ≡ true) → hexadecimalDigit c ≡ just (toℕ c ∸ 55)
  postulate
    hexLowercase : (c : _) → (((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 103)) ≡ true) → hexadecimalDigit c ≡ just (toℕ c ∸ 87)
  postulate
    nonHex : (c : _) → ((decimalDigit c ∨ (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 71)) ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 103)))) ≡ false) → hexadecimalDigit c ≡ nothing
  postulate
    hexPrefix : ℕ → ℕ → List Char → Prefix ℕ
  postulate
    hexComplete : (acc : _) → (xs : _) → hexPrefix 0 acc xs ≡ consumed acc xs
  postulate
    hexIncomplete : (n : _) → (acc : _) → hexPrefix (suc n) acc [] ≡ failed incompleteDocument
  postulate
    hexUnexpected : (n : _) → (acc : _) → (c : _) → (xs : _) → (hexadecimalDigit c ≡ nothing) → hexPrefix (suc n) acc (c ∷ xs) ≡ failed (unexpected c unicodeDigit)
  postulate
    hexNext : (n : _) → (acc : _) → (c : _) → (xs : _) → (d : _) → (hexadecimalDigit c ≡ just d) → hexPrefix (suc n) acc (c ∷ xs) ≡ hexPrefix n ((16 * acc) + d) xs
  postulate
    isHighSurrogate : ℕ → Bool
  postulate
    isLowSurrogate : ℕ → Bool
  postulate
    highRange : (n : _) → isHighSurrogate n ≡ ((55295 <ᵇ n) ∧ (n <ᵇ 56320))
  postulate
    lowRange : (n : _) → isLowSurrogate n ≡ ((56319 <ᵇ n) ∧ (n <ᵇ 57344))
  postulate
    utf16Escape : ℕ → List Char → Prefix Char
  postulate
    ordinaryUnit : (n : _) → (xs : _) → ((n <ᵇ 65536) ≡ true) → ((isHighSurrogate n ∨ isLowSurrogate n) ≡ false) → utf16Escape n xs ≡ consumed (primNatToChar n) xs
  postulate
    isolatedLow : (n : _) → (xs : _) → (isLowSurrogate n ≡ true) → utf16Escape n xs ≡ consumed (primNatToChar 65533) xs
  postulate
    noSecondUnit : (n : _) → (xs : _) → (isHighSurrogate n ≡ true) → (take 2 xs ≢ ('\\' ∷ ('u' ∷ []))) → utf16Escape n xs ≡ consumed (primNatToChar 65533) xs
  postulate
    malformedSecondUnit : (n : _) → (xs : _) → (fault : _) → (isHighSurrogate n ≡ true) → (hexPrefix 4 0 xs ≡ failed fault) → utf16Escape n ('\\' ∷ ('u' ∷ xs)) ≡ consumed (primNatToChar 65533) ('\\' ∷ ('u' ∷ xs))
  postulate
    unmatchedSecondUnit : (n : _) → (m : _) → (xs : _) → (rest : _) → (isHighSurrogate n ≡ true) → (hexPrefix 4 0 xs ≡ consumed m rest) → (isLowSurrogate m ≡ false) → utf16Escape n ('\\' ∷ ('u' ∷ xs)) ≡ consumed (primNatToChar 65533) ('\\' ∷ ('u' ∷ xs))
  postulate
    pairedUnits : (n : _) → (m : _) → (xs : _) → (rest : _) → (isHighSurrogate n ≡ true) → (hexPrefix 4 0 xs ≡ consumed m rest) → (isLowSurrogate m ≡ true) → utf16Escape n ('\\' ∷ ('u' ∷ xs)) ≡ consumed (primNatToChar (65536 + ((1024 * (n ∸ 55296)) + (m ∸ 56320)))) rest
  postulate
    escapePrefix : List Char → Prefix Char
  postulate
    absentEscape : escapePrefix [] ≡ failed incompleteDocument
  postulate
    quoteEscape : (xs : _) → escapePrefix ('\"' ∷ xs) ≡ consumed '\"' xs
  postulate
    slashEscape : (xs : _) → escapePrefix ('/' ∷ xs) ≡ consumed '/' xs
  postulate
    backslashEscape : (xs : _) → escapePrefix ('\\' ∷ xs) ≡ consumed '\\' xs
  postulate
    backspaceEscape : (xs : _) → escapePrefix ('b' ∷ xs) ≡ consumed (primNatToChar 8) xs
  postulate
    formfeedEscape : (xs : _) → escapePrefix ('f' ∷ xs) ≡ consumed (primNatToChar 12) xs
  postulate
    newlineEscape : (xs : _) → escapePrefix ('n' ∷ xs) ≡ consumed '\n' xs
  postulate
    returnEscape : (xs : _) → escapePrefix ('r' ∷ xs) ≡ consumed '\r' xs
  postulate
    tabEscape : (xs : _) → escapePrefix ('t' ∷ xs) ≡ consumed '	' xs
  postulate
    escapedUnit : (xs : _) → (n : _) → (rest : _) → (hexPrefix 4 0 xs ≡ consumed n rest) → escapePrefix ('u' ∷ xs) ≡ utf16Escape n rest
  postulate
    malformedUnit : (xs : _) → (err : _) → (hexPrefix 4 0 xs ≡ failed err) → escapePrefix ('u' ∷ xs) ≡ failed err
  postulate
    unknownEscape : (c : _) → (xs : _) → (any (primCharEquality c) (toList "\"/\\bfnrtu") ≡ false) → escapePrefix (c ∷ xs) ≡ failed (unexpected c afterEscape)
  postulate
    stringBody : List Char → Prefix String
  postulate
    bodyUnclosed : stringBody [] ≡ failed incompleteDocument
  postulate
    bodyClosed : (xs : _) → stringBody ('\"' ∷ xs) ≡ consumed "" xs
  postulate
    bodyControl : (c : _) → (xs : _) → ((toℕ c <ᵇ 32) ≡ true) → stringBody (c ∷ xs) ≡ failed (unexpected c insideString)
  postulate
    bodyCharacter : (c : _) → (xs : _) → (s : _) → (rest : _) → ((toℕ c <ᵇ 32) ≡ false) → (any (primCharEquality c) (toList "\"\\") ≡ false) → (stringBody xs ≡ consumed s rest) → stringBody (c ∷ xs) ≡ consumed (fromList ([ c ]) ++ˢ s) rest
  postulate
    bodyAfterCharacterError : (c : _) → (xs : _) → (e : _) → ((toℕ c <ᵇ 32) ≡ false) → (any (primCharEquality c) (toList "\"\\") ≡ false) → (stringBody xs ≡ failed e) → stringBody (c ∷ xs) ≡ failed e
  postulate
    bodyEscape : (xs : _) → (c : _) → (mid : _) → (s : _) → (rest : _) → (escapePrefix xs ≡ consumed c mid) → (stringBody mid ≡ consumed s rest) → stringBody ('\\' ∷ xs) ≡ consumed (fromList ([ c ]) ++ˢ s) rest
  postulate
    bodyEscapeError : (xs : _) → (e : _) → (escapePrefix xs ≡ failed e) → stringBody ('\\' ∷ xs) ≡ failed e
  postulate
    bodyAfterEscapeError : (xs : _) → (c : _) → (mid : _) → (e : _) → (escapePrefix xs ≡ consumed c mid) → (stringBody mid ≡ failed e) → stringBody ('\\' ∷ xs) ≡ failed e
  postulate
    digitSpan : List Char → List Char × List Char
  postulate
    noDigitInput : digitSpan [] ≡ ([] , [])
  postulate
    stopDigitSpan : (c : _) → (xs : _) → (decimalDigit c ≡ false) → digitSpan (c ∷ xs) ≡ ([] , (c ∷ xs))
  postulate
    extendDigitSpan : (c : _) → (xs : _) → (ds : _) → (rest : _) → (decimalDigit c ≡ true) → (digitSpan xs ≡ (ds , rest)) → digitSpan (c ∷ xs) ≡ ((c ∷ ds) , rest)
  postulate
    requiredDigits : Expectation → List Char → Prefix (List Char)
  postulate
    missingDigits : (site : _) → requiredDigits site [] ≡ failed incompleteDocument
  postulate
    rejectedDigits : (site : _) → (c : _) → (xs : _) → (decimalDigit c ≡ false) → requiredDigits site (c ∷ xs) ≡ failed (unexpected c site)
  postulate
    acceptedDigits : (site : _) → (c : _) → (xs : _) → (ds : _) → (rest : _) → (decimalDigit c ≡ true) → (digitSpan xs ≡ (ds , rest)) → requiredDigits site (c ∷ xs) ≡ consumed (c ∷ ds) rest
  postulate
    unsignedInteger : List Char → Prefix (List Char)
  postulate
    zeroInteger : (xs : _) → unsignedInteger ('0' ∷ xs) ≡ consumed ([ '0' ]) xs
  postulate
    otherInteger : (xs : _) → (take 1 xs ≢ ([ '0' ])) → unsignedInteger xs ≡ requiredDigits integerDigit xs
  postulate
    signedInteger : List Char → Prefix (List Char)
  postulate
    positiveInteger : (xs : _) → (take 1 xs ≢ ([ '-' ])) → signedInteger xs ≡ unsignedInteger xs
  postulate
    negativeInteger : (xs : _) → (ds : _) → (rest : _) → (unsignedInteger xs ≡ consumed ds rest) → signedInteger ('-' ∷ xs) ≡ consumed ('-' ∷ ds) rest
  postulate
    negativeIntegerError : (xs : _) → (e : _) → (unsignedInteger xs ≡ failed e) → signedInteger ('-' ∷ xs) ≡ failed e
  postulate
    fraction : List Char → Prefix (List Char)
  postulate
    noFraction : (xs : _) → (take 1 xs ≢ ([ '.' ])) → fraction xs ≡ consumed [] xs
  postulate
    fractionWithDigits : (xs : _) → (ds : _) → (rest : _) → (requiredDigits fractionalDigit xs ≡ consumed ds rest) → fraction ('.' ∷ xs) ≡ consumed ('.' ∷ ds) rest
  postulate
    fractionWithoutDigits : (xs : _) → (e : _) → (requiredDigits fractionalDigit xs ≡ failed e) → fraction ('.' ∷ xs) ≡ failed e
  postulate
    exponentBody : List Char → Prefix (List Char)
  postulate
    exponentWithoutSign : (xs : _) → (take 1 xs ≢ ([ '+' ])) → (take 1 xs ≢ ([ '-' ])) → exponentBody xs ≡ requiredDigits exponentDigit xs
  postulate
    exponentWithSign : (c : _) → (xs : _) → (ds : _) → (rest : _) → ((primCharEquality c '+' ∨ primCharEquality c '-') ≡ true) → (requiredDigits exponentDigit xs ≡ consumed ds rest) → exponentBody (c ∷ xs) ≡ consumed (c ∷ ds) rest
  postulate
    exponentSignError : (c : _) → (xs : _) → (e : _) → ((primCharEquality c '+' ∨ primCharEquality c '-') ≡ true) → (requiredDigits exponentDigit xs ≡ failed e) → exponentBody (c ∷ xs) ≡ failed e
  postulate
    exponent : List Char → Prefix (List Char)
  postulate
    noExponent : (xs : _) → (take 1 xs ≢ ([ 'e' ])) → (take 1 xs ≢ ([ 'E' ])) → exponent xs ≡ consumed [] xs
  postulate
    exponentWithDigits : (c : _) → (xs : _) → (ds : _) → (rest : _) → ((primCharEquality c 'e' ∨ primCharEquality c 'E') ≡ true) → (exponentBody xs ≡ consumed ds rest) → exponent (c ∷ xs) ≡ consumed (c ∷ ds) rest
  postulate
    exponentWithoutDigits : (c : _) → (xs : _) → (e : _) → ((primCharEquality c 'e' ∨ primCharEquality c 'E') ≡ true) → (exponentBody xs ≡ failed e) → exponent (c ∷ xs) ≡ failed e
  postulate
    numberPrefix : List Char → Prefix String
  postulate
    numberWithParts : (xs : _) → (i : _) → (r : _) → (f : _) → (q : _) → (d : _) → (rest : _) → (signedInteger xs ≡ consumed i r) → (fraction r ≡ consumed f q) → (exponent q ≡ consumed d rest) → numberPrefix xs ≡ consumed (fromList (i ++ (f ++ d))) rest
  postulate
    numberIntegerError : (xs : _) → (e : _) → (signedInteger xs ≡ failed e) → numberPrefix xs ≡ failed e
  postulate
    numberFractionError : (xs : _) → (i : _) → (r : _) → (e : _) → (signedInteger xs ≡ consumed i r) → (fraction r ≡ failed e) → numberPrefix xs ≡ failed e
  postulate
    numberExponentError : (xs : _) → (i : _) → (r : _) → (f : _) → (q : _) → (e : _) → (signedInteger xs ≡ consumed i r) → (fraction r ≡ consumed f q) → (exponent q ≡ failed e) → numberPrefix xs ≡ failed e
  postulate
    literalSuffix : Json → String → List Char → List Char → Prefix Json
  postulate
    wordComplete : (a : _) → (word : _) → (xs : _) → literalSuffix a word [] xs ≡ consumed a xs
  postulate
    wordIncomplete : (a : _) → (word : _) → (c : _) → (cs : _) → literalSuffix a word (c ∷ cs) [] ≡ failed incompleteDocument
  postulate
    wordMatched : (a : _) → (word : _) → (c : _) → (cs : _) → (xs : _) → literalSuffix a word (c ∷ cs) (c ∷ xs) ≡ literalSuffix a word cs xs
  postulate
    wordMismatch : (a : _) → (word : _) → (c : _) → (d : _) → (cs : _) → (xs : _) → (primCharEquality c d ≡ false) → literalSuffix a word (c ∷ cs) (d ∷ xs) ≡ failed (unexpected d (inWord word c))
  postulate
    matchingValues : String → List (String × Json) → List Json
  postulate
    noMatchingValues : (k : _) → matchingValues k [] ≡ []
  postulate
    nextMatchingValue : (k : _) → (v : _) → (fields : _) → matchingValues k ((k , v) ∷ fields) ≡ (matchingValues k fields ++ ([ v ]))
  postulate
    otherMatchingValue : (k : _) → (l : _) → (v : _) → (fields : _) → (primStringEquality k l ≡ false) → matchingValues k ((l , v) ∷ fields) ≡ matchingValues k fields
  postulate
    resolveFields : List (String × Json) → List (String × Json)
  postulate
    resolveEmpty : resolveFields [] ≡ []
  postulate
    resolveAbsent : (k : _) → (fields : _) → (matchingValues k fields ≡ []) → matchingValues k (resolveFields fields) ≡ []
  postulate
    resolveNewest : (k : _) → (v : _) → (older : _) → (fields : _) → (matchingValues k fields ≡ (v ∷ older)) → matchingValues k (resolveFields fields) ≡ ([ v ])
  postulate
    maxNesting : ℕ
  postulate
    nestingCapacity : maxNesting ≡ 10000
  postulate
    valueAtDepth : ℕ → List Char → Prefix Json
  postulate
    valuePrefix : List Char → Prefix Json
  postulate
    arrayItems : ℕ → Bool → List Char → Prefix (List Json)
  postulate
    arrayTail : ℕ → List Char → Prefix (List Json)
  postulate
    objectItems : ℕ → Bool → List Char → Prefix (List (String × Json))
  postulate
    objectTail : ℕ → List Char → Prefix (List (String × Json))
  postulate
    memberPrefix : ℕ → List Char → Prefix (String × Json)
  postulate
    memberValue : ℕ → List Char → Prefix Json
  postulate
    topLevelBudget : (xs : _) → valuePrefix xs ≡ valueAtDepth maxNesting xs
  postulate
    emptyPrefix : (budget : _) → valueAtDepth budget [] ≡ failed missingDocument
  postulate
    leadingSpace : (budget : _) → (c : _) → (xs : _) → (whitespace c ≡ true) → valueAtDepth budget (c ∷ xs) ≡ valueAtDepth budget xs
  postulate
    unexpectedStart : (budget : _) → (c : _) → (xs : _) → ((whitespace c ∨ (decimalDigit c ∨ any (primCharEquality c) (toList "-tfn\"[{"))) ≡ false) → valueAtDepth budget (c ∷ xs) ≡ failed (unexpected c valueStart)
  postulate
    truePrefix : (budget : _) → (xs : _) → valueAtDepth budget ('t' ∷ xs) ≡ literalSuffix (jsonBool true) "true" (toList "rue") xs
  postulate
    falsePrefix : (budget : _) → (xs : _) → valueAtDepth budget ('f' ∷ xs) ≡ literalSuffix (jsonBool false) "false" (toList "alse") xs
  postulate
    nullPrefix : (budget : _) → (xs : _) → valueAtDepth budget ('n' ∷ xs) ≡ literalSuffix jsonNull "null" (toList "ull") xs
  postulate
    numberValue : (budget : _) → (c : _) → (xs : _) → (s : _) → (rest : _) → ((decimalDigit c ∨ primCharEquality c '-') ≡ true) → (numberPrefix (c ∷ xs) ≡ consumed s rest) → valueAtDepth budget (c ∷ xs) ≡ consumed (jsonNumber s) rest
  postulate
    numberValueError : (budget : _) → (c : _) → (xs : _) → (e : _) → ((decimalDigit c ∨ primCharEquality c '-') ≡ true) → (numberPrefix (c ∷ xs) ≡ failed e) → valueAtDepth budget (c ∷ xs) ≡ failed e
  postulate
    stringValue : (budget : _) → (xs : _) → (s : _) → (rest : _) → (stringBody xs ≡ consumed s rest) → valueAtDepth budget ('\"' ∷ xs) ≡ consumed (jsonText s) rest
  postulate
    stringValueError : (budget : _) → (xs : _) → (e : _) → (stringBody xs ≡ failed e) → valueAtDepth budget ('\"' ∷ xs) ≡ failed e
  postulate
    arrayValue : (budget : _) → (xs : _) → (vs : _) → (rest : _) → (arrayItems budget true xs ≡ consumed vs rest) → valueAtDepth (suc budget) ('[' ∷ xs) ≡ consumed (jsonArray vs) rest
  postulate
    arrayValueError : (budget : _) → (xs : _) → (e : _) → (arrayItems budget true xs ≡ failed e) → valueAtDepth (suc budget) ('[' ∷ xs) ≡ failed e
  postulate
    objectValue : (budget : _) → (xs : _) → (fields : _) → (rest : _) → (objectItems budget true xs ≡ consumed fields rest) → valueAtDepth (suc budget) ('{' ∷ xs) ≡ consumed (jsonObject (resolveFields fields)) rest
  postulate
    objectValueError : (budget : _) → (xs : _) → (e : _) → (objectItems budget true xs ≡ failed e) → valueAtDepth (suc budget) ('{' ∷ xs) ≡ failed e
  postulate
    arrayAtDepthLimit : (xs : _) → valueAtDepth zero ('[' ∷ xs) ≡ failed (unexpected '[' exceededDepth)
  postulate
    objectAtDepthLimit : (xs : _) → valueAtDepth zero ('{' ∷ xs) ≡ failed (unexpected '{' exceededDepth)
  postulate
    arrayItemsEOF : (budget : _) → (empty : _) → (xs : _) → (skipWhitespace xs ≡ []) → arrayItems budget empty xs ≡ failed incompleteDocument
  postulate
    arrayEmpty : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ (']' ∷ rest)) → arrayItems budget true xs ≡ consumed [] rest
  postulate
    arrayItem : (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (v : _) → (mid : _) → (vs : _) → (rest : _) → (skipWhitespace xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c ']') ≡ false) → (valueAtDepth budget (c ∷ cs) ≡ consumed v mid) → (arrayTail budget mid ≡ consumed vs rest) → arrayItems budget empty xs ≡ consumed (v ∷ vs) rest
  postulate
    arrayItemError : (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (e : _) → (skipWhitespace xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c ']') ≡ false) → (valueAtDepth budget (c ∷ cs) ≡ failed e) → arrayItems budget empty xs ≡ failed e
  postulate
    arrayAfterItemError : (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (v : _) → (mid : _) → (e : _) → (skipWhitespace xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c ']') ≡ false) → (valueAtDepth budget (c ∷ cs) ≡ consumed v mid) → (arrayTail budget mid ≡ failed e) → arrayItems budget empty xs ≡ failed e
  postulate
    arrayTailEOF : (budget : _) → (xs : _) → (skipWhitespace xs ≡ []) → arrayTail budget xs ≡ failed incompleteDocument
  postulate
    arrayTailClose : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ (']' ∷ rest)) → arrayTail budget xs ≡ consumed [] rest
  postulate
    arrayTailComma : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ (',' ∷ rest)) → arrayTail budget xs ≡ arrayItems budget false rest
  postulate
    arrayTailUnexpected : (budget : _) → (xs : _) → (c : _) → (rest : _) → (skipWhitespace xs ≡ (c ∷ rest)) → ((primCharEquality c ']' ∨ primCharEquality c ',') ≡ false) → arrayTail budget xs ≡ failed (unexpected c afterElement)
  postulate
    objectItemsEOF : (budget : _) → (empty : _) → (xs : _) → (skipWhitespace xs ≡ []) → objectItems budget empty xs ≡ failed incompleteDocument
  postulate
    objectEmpty : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ ('}' ∷ rest)) → objectItems budget true xs ≡ consumed [] rest
  postulate
    objectItem : (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (entry : _) → (mid : _) → (fields : _) → (rest : _) → (skipWhitespace xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c '}') ≡ false) → (memberPrefix budget (c ∷ cs) ≡ consumed entry mid) → (objectTail budget mid ≡ consumed fields rest) → objectItems budget empty xs ≡ consumed (entry ∷ fields) rest
  postulate
    objectItemError : (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (e : _) → (skipWhitespace xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c '}') ≡ false) → (memberPrefix budget (c ∷ cs) ≡ failed e) → objectItems budget empty xs ≡ failed e
  postulate
    objectAfterItemError : (budget : _) → (empty : _) → (xs : _) → (c : _) → (cs : _) → (entry : _) → (mid : _) → (e : _) → (skipWhitespace xs ≡ (c ∷ cs)) → ((empty ∧ primCharEquality c '}') ≡ false) → (memberPrefix budget (c ∷ cs) ≡ consumed entry mid) → (objectTail budget mid ≡ failed e) → objectItems budget empty xs ≡ failed e
  postulate
    objectTailEOF : (budget : _) → (xs : _) → (skipWhitespace xs ≡ []) → objectTail budget xs ≡ failed incompleteDocument
  postulate
    objectTailClose : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ ('}' ∷ rest)) → objectTail budget xs ≡ consumed [] rest
  postulate
    objectTailComma : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ (',' ∷ rest)) → objectTail budget xs ≡ objectItems budget false rest
  postulate
    objectTailUnexpected : (budget : _) → (xs : _) → (c : _) → (rest : _) → (skipWhitespace xs ≡ (c ∷ rest)) → ((primCharEquality c '}' ∨ primCharEquality c ',') ≡ false) → objectTail budget xs ≡ failed (unexpected c afterMember)
  postulate
    memberEOF : (budget : _) → memberPrefix budget [] ≡ failed incompleteDocument
  postulate
    memberBadStart : (budget : _) → (c : _) → (xs : _) → (primCharEquality c '\"' ≡ false) → memberPrefix budget (c ∷ xs) ≡ failed (unexpected c objectKey)
  postulate
    memberWithValue : (budget : _) → (xs : _) → (k : _) → (mid : _) → (v : _) → (rest : _) → (stringBody xs ≡ consumed k mid) → (memberValue budget mid ≡ consumed v rest) → memberPrefix budget ('\"' ∷ xs) ≡ consumed (k , v) rest
  postulate
    memberKeyError : (budget : _) → (xs : _) → (e : _) → (stringBody xs ≡ failed e) → memberPrefix budget ('\"' ∷ xs) ≡ failed e
  postulate
    memberValueError : (budget : _) → (xs : _) → (k : _) → (mid : _) → (e : _) → (stringBody xs ≡ consumed k mid) → (memberValue budget mid ≡ failed e) → memberPrefix budget ('\"' ∷ xs) ≡ failed e
  postulate
    valueAfterColon : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ (':' ∷ rest)) → (valueAtDepth budget rest ≢ failed missingDocument) → memberValue budget xs ≡ valueAtDepth budget rest
  postulate
    valueEOF : (budget : _) → (xs : _) → (skipWhitespace xs ≡ []) → memberValue budget xs ≡ failed incompleteDocument
  postulate
    valueAfterColonEOF : (budget : _) → (xs : _) → (rest : _) → (skipWhitespace xs ≡ (':' ∷ rest)) → (valueAtDepth budget rest ≡ failed missingDocument) → memberValue budget xs ≡ failed incompleteDocument
  postulate
    memberMissingColon : (budget : _) → (xs : _) → (c : _) → (rest : _) → (skipWhitespace xs ≡ (c ∷ rest)) → (primCharEquality c ':' ≡ false) → memberValue budget xs ≡ failed (unexpected c afterKey)
  postulate
    firstDocument : List Char → Document
  postulate
    firstDocumentFound : (xs : _) → (v : _) → (rest : _) → (valuePrefix xs ≡ consumed v rest) → firstDocument xs ≡ parsed v
  postulate
    firstDocumentFault : (xs : _) → (e : _) → (valuePrefix xs ≡ failed e) → firstDocument xs ≡ rejected (faultText e)
  postulate
    readDocument : String → Document
  postulate
    readDocumentLaw : (s : _) → readDocument s ≡ firstDocument (toList s)
  postulate
    strictDocument : List Char → Document
  postulate
    strictDocumentFound : (xs : _) → (v : _) → (rest : _) → (valuePrefix xs ≡ consumed v rest) → (skipWhitespace rest ≡ []) → strictDocument xs ≡ parsed v
  postulate
    strictDocumentTrailing : (xs : _) → (v : _) → (rest : _) → (c : _) → (cs : _) → (valuePrefix xs ≡ consumed v rest) → (skipWhitespace rest ≡ (c ∷ cs)) → strictDocument xs ≡ rejected (faultText (unexpected c afterDocument))
  postulate
    strictDocumentInvalid : (xs : _) → (c : _) → (site : _) → (valuePrefix xs ≡ failed (unexpected c site)) → strictDocument xs ≡ rejected (faultText (unexpected c site))
  postulate
    strictDocumentMissing : (xs : _) → (valuePrefix xs ≡ failed missingDocument) → strictDocument xs ≡ rejected "unexpected end of JSON input"
  postulate
    strictDocumentIncomplete : (xs : _) → (valuePrefix xs ≡ failed incompleteDocument) → strictDocument xs ≡ rejected "unexpected end of JSON input"
  record FrameScan : Set where
    constructor frameScan
    field
      frames : List (List Char)
      tooLong : Bool
  postulate
    utf8Width : Char → ℕ
  postulate
    asciiWidth : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → utf8Width c ≡ 1
  postulate
    twoByteWidth : (c : _) → (((127 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 2048)) ≡ true) → utf8Width c ≡ 2
  postulate
    threeByteWidth : (c : _) → (((2047 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 65536)) ≡ true) → utf8Width c ≡ 3
  postulate
    fourByteWidth : (c : _) → ((65535 <ᵇ toℕ c) ≡ true) → utf8Width c ≡ 4
  postulate
    byteCount : List Char → ℕ
  postulate
    noBytes : byteCount [] ≡ 0
  postulate
    moreBytes : (c : _) → (xs : _) → byteCount (c ∷ xs) ≡ (utf8Width c + byteCount xs)
  postulate
    lineContent : List Char → List Char
  postulate
    noLineContent : lineContent [] ≡ []
  postulate
    stripFinalCR : (xs : _) → lineContent (xs ++ ([ '\r' ])) ≡ xs
  postulate
    keepFinalChar : (xs : _) → (c : _) → (primCharEquality c '\r' ≡ false) → lineContent (xs ++ ([ c ])) ≡ (xs ++ ([ c ]))
  postulate
    frameLimit : ℕ
  postulate
    lineBufferCapacity : frameLimit ≡ 1048576
  postulate
    physicalLines : List Char → FrameScan
  postulate
    noPhysicalLines : physicalLines [] ≡ frameScan [] false
  postulate
    terminatedLine : (xs : _) → (ys : _) → (ls : _) → (capped : _) → (any (primCharEquality '\n') xs ≡ false) → ((byteCount xs <ᵇ frameLimit) ≡ true) → (physicalLines ys ≡ frameScan ls capped) → physicalLines (xs ++ ('\n' ∷ ys)) ≡ frameScan (lineContent xs ∷ ls) capped
  postulate
    finalLine : (c : _) → (xs : _) → (any (primCharEquality '\n') (c ∷ xs) ≡ false) → ((byteCount (c ∷ xs) <ᵇ frameLimit) ≡ true) → physicalLines (c ∷ xs) ≡ frameScan ([ lineContent (c ∷ xs) ]) false
  postulate
    oversizedLine : (xs : _) → (ys : _) → (any (primCharEquality '\n') xs ≡ false) → ((byteCount xs <ᵇ frameLimit) ≡ false) → physicalLines (xs ++ ('\n' ∷ ys)) ≡ frameScan [] true
  postulate
    oversizedFinalLine : (c : _) → (xs : _) → (any (primCharEquality '\n') (c ∷ xs) ≡ false) → ((byteCount (c ∷ xs) <ᵇ frameLimit) ≡ false) → physicalLines (c ∷ xs) ≡ frameScan [] true
  record DocumentSequence : Set where
    constructor documentSequence
    field
      documents : List Json
      interruption : Maybe String
  postulate
    decodeLines : List (List Char) → DocumentSequence
  postulate
    decodeWithoutLines : decodeLines [] ≡ documentSequence [] nothing
  postulate
    decodeUntilFault : (line : _) → (more : _) → (e : _) → (firstDocument line ≡ rejected e) → decodeLines (line ∷ more) ≡ documentSequence [] (just e)
  postulate
    decodeNextLine : (line : _) → (more : _) → (v : _) → (vs : _) → (e : _) → (firstDocument line ≡ parsed v) → (decodeLines more ≡ documentSequence vs e) → decodeLines (line ∷ more) ≡ documentSequence (v ∷ vs) e
  postulate
    readStream : String → StreamReply
  postulate
    streamReadComplete : (s : _) → (ls : _) → (vs : _) → (physicalLines (toList s) ≡ frameScan ls false) → (decodeLines ls ≡ documentSequence vs nothing) → readStream s ≡ streamReply 0 vs ""
  postulate
    streamReadMalformed : (s : _) → (ls : _) → (capped : _) → (vs : _) → (e : _) → (physicalLines (toList s) ≡ frameScan ls capped) → (decodeLines ls ≡ documentSequence vs (just e)) → readStream s ≡ streamReply 3 vs ("failed to form statements: " ++ˢ (e ++ˢ "\n"))
  postulate
    streamReadCapped : (s : _) → (ls : _) → (vs : _) → (physicalLines (toList s) ≡ frameScan ls true) → (decodeLines ls ≡ documentSequence vs nothing) → readStream s ≡ streamReply 3 vs "error reading multiline input: bufio.Scanner: token too long: %!s(MISSING)\n"
  postulate
    numberPrefixFixture : readDocument " 	\r\n1x" ≡ parsed (jsonNumber "1")
  postulate
    leadingZeroFixture : readDocument "[01]" ≡ rejected "invalid character '1' after array element"
  postulate
    failureAfterExponentFixture : readDocument "[1e+]" ≡ rejected "invalid character ']' in exponent of numeric literal"
  postulate
    nulFixture : readDocument (fromList ([ primNatToChar 0 ])) ≡ rejected "invalid character '\\x00' looking for beginning of value"
  postulate
    decodedDuplicateFixture : (fs : _) → (readDocument "{\"a\":{\"x\":1},\"a\":{\"y\":2},\"\\u0062\":0,\"b\":1}" ≡ parsed (jsonObject fs)) → (matchingValues "a" fs ≡ (jsonObject (("y" , jsonNumber "2") ∷ []) ∷ [])) × (matchingValues "b" fs ≡ (jsonNumber "1" ∷ []))
  postulate
    surrogateFixture : readDocument "[\"\\uD83D\\uDE00\",\"\\uD800\",\"\\uDC00\",\"\\uD800\\u0041\",\"a\\/b\"]" ≡ parsed (jsonArray (jsonText (fromList ([ primNatToChar 128512 ])) ∷ (jsonText (fromList ([ primNatToChar 65533 ])) ∷ (jsonText (fromList ([ primNatToChar 65533 ])) ∷ (jsonText (fromList (primNatToChar 65533 ∷ ([ 'A' ]))) ∷ ([ jsonText "a/b" ]))))))
  postulate
    quotedCRLFFixture : readStream "\"a\r\n" ≡ streamReply 3 [] "failed to form statements: unexpected EOF\n"
  postulate
    strictTailFixture : strictDocument (toList "[[\"a\"],1][[\"b\"],2]") ≡ rejected "invalid character '[' after top-level value"
  postulate
    strictBlankFixture : strictDocument (toList " \r	") ≡ rejected "unexpected end of JSON input"
  postulate
    oneValueOnLineFixture : readStream "true null\n" ≡ streamReply 0 (jsonBool true ∷ []) ""
  postulate
    blankLineStopsFixture : readStream "true\n\nnull\n" ≡ streamReply 3 (jsonBool true ∷ []) "failed to form statements: EOF\n"
