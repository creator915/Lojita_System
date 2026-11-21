module Gen.T1.GronText where

  open import Agda.Builtin.Nat using (div-helper)
  open import Agda.Builtin.String using (primStringEquality; primShowNat)
  open import Agda.Builtin.Char using (Char; primCharToNat; primNatToChar)
  open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _<ᵇ_)
  import Data.Nat.Show as Nat
  open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
  open import Data.List using (List; []; _∷_; length; take; reverse; map) renaming (_++_ to _++ˡ_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.String using (String; fromList; toList; _++_)
  import Data.Sum as Sum
  open Sum using (_⊎_; inj₁; inj₂)
  open import Data.Unit using (⊤; tt)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Context.Blueprint using (PortLift; portLift; keepPort; Commutes₁)
  import Gen.T0.Gron as Base

  data StatementEncoding : Set where
    assignments : StatementEncoding
    tuples : StatementEncoding

  data AssignmentRead : Set where
    skipped : AssignmentRead
    accepted : Base.Statement → AssignmentRead
    rejected : (fragment reason : String) → AssignmentRead

  notationOf : List Char → Base.KeyNotation
  notationOf ('.' ∷ _) = Base.dotted
  notationOf _ = Base.bracketed

  keyPort : PortLift Base.KeyNotation (List Char)
  keyPort = portLift notationOf

  private
    within : ℕ → ℕ → ℕ → Bool
    within lo hi n = not (n <ᵇ lo) ∧ (n <ᵇ hi)

    digit : Char → Bool
    digit c = within 48 58 (primCharToNat c)

    sameChar : Char → Char → Bool
    sameChar c d = primCharToNat c ≡ᵇ primCharToNat d

    jsonSpace : Char → Bool
    jsonSpace c = let n = primCharToNat c in (n ≡ᵇ 32) ∨ ((n ≡ᵇ 9) ∨ ((n ≡ᵇ 13) ∨ (n ≡ᵇ 10)))

    skipSpace : List Char → List Char
    skipSpace [] = []
    skipSpace (c ∷ cs) = if jsonSpace c then skipSpace cs else (c ∷ cs)

    scanWhile : (Char → Bool) → List Char → List Char × List Char
    scanWhile p [] = [] , []
    scanWhile p (c ∷ cs) with p c
    scanWhile p (c ∷ cs) | false = [] , (c ∷ cs)
    scanWhile p (c ∷ cs) | true = let result = scanWhile p cs in (c ∷ proj₁ result) , proj₂ result

    hexDigit : ℕ → Char
    hexDigit n = primNatToChar (if (n <ᵇ 10) then (48 + n) else (87 + n))

    utf8Lead : ℕ → ℕ
    utf8Lead n = if (n <ᵇ 128) then n else (if (n <ᵇ 2048) then (192 + div-helper 0 63 n 63) else (if (n <ᵇ 65536) then (224 + div-helper 0 4095 n 4095) else (240 + div-helper 0 262143 n 262143)))

    diagnosticChar : Char → String
    diagnosticChar c = let n = primCharToNat c; apostrophe = primNatToChar 39; high = div-helper 0 15 n 15 in if (n ≡ᵇ 39) then "'\\''" else (if (n ≡ᵇ 92) then "'\\\\'" else (if (n ≡ᵇ 7) then "'\\a'" else (if (n ≡ᵇ 8) then "'\\b'" else (if (n ≡ᵇ 9) then "'\\t'" else (if (n ≡ᵇ 10) then "'\\n'" else (if (n ≡ᵇ 11) then "'\\v'" else (if (n ≡ᵇ 12) then "'\\f'" else (if (n ≡ᵇ 13) then "'\\r'" else (if ((n <ᵇ 32) ∨ (n ≡ᵇ 127)) then fromList (apostrophe ∷ ('\\' ∷ ('x' ∷ (hexDigit high ∷ (hexDigit (n ∸ (16 * high)) ∷ (apostrophe ∷ [])))))) else fromList (apostrophe ∷ (primNatToChar (utf8Lead n) ∷ (apostrophe ∷ []))))))))))))

    invalid : {A : Set} → String → List Char → String ⊎ A
    invalid context [] = inj₁ "unexpected EOF"
    invalid context (c ∷ _) = inj₁ ("invalid character " ++ (diagnosticChar c ++ (" " ++ context)))

    Parsed : Set → Set
    Parsed A = String ⊎ (A × List Char)

    chain : {A B : Set} → Parsed A → (A → List Char → Parsed B) → Parsed B
    chain (inj₁ reason) next = inj₁ reason
    chain (inj₂ (value , rest)) next = next value rest

    hexValue : Char → Maybe ℕ
    hexValue c = let n = primCharToNat c in if within 48 58 n then just (n ∸ 48) else (if within 65 71 n then just (n ∸ 55) else (if within 97 103 n then just (n ∸ 87) else nothing))

    readHex : ℕ → ℕ → List Char → Parsed ℕ
    readHex zero n cs = inj₂ (n , cs)
    readHex (suc count) n [] = inj₁ "unexpected EOF"
    readHex (suc count) n (c ∷ cs) with hexValue c
    readHex (suc count) n (c ∷ cs) | nothing = invalid "in \\u hexadecimal character escape" (c ∷ cs)
    readHex (suc count) n (c ∷ cs) | (just d) = readHex count ((16 * n) + d) cs

    combineSurrogates : ℕ → List Char → Parsed Char
    combineSurrogates high (cs@('\\' ∷ ('u' ∷ digits))) with readHex 4 0 digits
    combineSurrogates high (cs@('\\' ∷ ('u' ∷ digits))) | (inj₁ _) = inj₂ ('�' , cs)
    combineSurrogates high (cs@('\\' ∷ ('u' ∷ digits))) | (inj₂ (low , rest)) = if within 56320 57344 low then inj₂ (primNatToChar ((65536 + ((high ∸ 55296) * 1024)) + (low ∸ 56320)) , rest) else inj₂ ('�' , cs)
    combineSurrogates high cs = inj₂ ('�' , cs)

    decodeCodePoint : ℕ → List Char → Parsed Char
    decodeCodePoint n cs = if within 55296 56320 n then combineSurrogates n cs else (if within 56320 57344 n then inj₂ ('�' , cs) else inj₂ (primNatToChar n , cs))

    decodeEscape : List Char → Parsed Char
    decodeEscape ('\"' ∷ cs) = inj₂ ('\"' , cs)
    decodeEscape ('\\' ∷ cs) = inj₂ ('\\' , cs)
    decodeEscape ('/' ∷ cs) = inj₂ ('/' , cs)
    decodeEscape ('b' ∷ cs) = inj₂ (primNatToChar 8 , cs)
    decodeEscape ('f' ∷ cs) = inj₂ (primNatToChar 12 , cs)
    decodeEscape ('n' ∷ cs) = inj₂ (primNatToChar 10 , cs)
    decodeEscape ('r' ∷ cs) = inj₂ (primNatToChar 13 , cs)
    decodeEscape ('t' ∷ cs) = inj₂ (primNatToChar 9 , cs)
    decodeEscape ('u' ∷ cs) = chain (readHex 4 0 cs) decodeCodePoint
    decodeEscape cs = invalid "in string escape code" cs

    stringChars : ℕ → List Char → List Char → Parsed String
    stringChars zero rev cs = inj₁ "unexpected EOF"
    stringChars (suc fuel) rev [] = inj₁ "unexpected EOF"
    stringChars (suc fuel) rev ('\"' ∷ cs) = inj₂ (fromList (reverse rev) , cs)
    stringChars (suc fuel) rev ('\\' ∷ cs) = chain (decodeEscape cs) (λ c rest → stringChars fuel (c ∷ rev) rest)
    stringChars (suc fuel) rev (c ∷ cs) = if (primCharToNat c <ᵇ 32) then invalid "in string literal" (c ∷ cs) else stringChars fuel (c ∷ rev) cs

    needDigits : String → List Char → Parsed (List Char)
    needDigits context [] = invalid context []
    needDigits context (cs@(c ∷ _)) = if digit c then inj₂ (scanWhile digit cs) else invalid context cs

    prefixDigits : List Char → Parsed (List Char) → Parsed (List Char)
    prefixDigits prefix parsed = chain parsed (λ digits rest → inj₂ ((prefix ++ˡ digits) , rest))

    integerPart : List Char → Parsed (List Char)
    integerPart ('0' ∷ cs) = inj₂ (('0' ∷ []) , cs)
    integerPart cs = needDigits "in numeric literal" cs

    fractionPart : List Char → Parsed (List Char)
    fractionPart ('.' ∷ cs) = prefixDigits ('.' ∷ []) (needDigits "after decimal point in numeric literal" cs)
    fractionPart cs = inj₂ ([] , cs)

    signedExponent : Char → List Char → Parsed (List Char)
    signedExponent marker ('+' ∷ cs) = prefixDigits (marker ∷ ('+' ∷ [])) (needDigits "in exponent of numeric literal" cs)
    signedExponent marker ('-' ∷ cs) = prefixDigits (marker ∷ ('-' ∷ [])) (needDigits "in exponent of numeric literal" cs)
    signedExponent marker cs = prefixDigits (marker ∷ []) (needDigits "in exponent of numeric literal" cs)

    exponentPart : List Char → Parsed (List Char)
    exponentPart ('e' ∷ cs) = signedExponent 'e' cs
    exponentPart ('E' ∷ cs) = signedExponent 'E' cs
    exponentPart cs = inj₂ ([] , cs)

    parseNumberWith : (List Char → Parsed (List Char)) → List Char → List Char → Parsed Base.JSON
    parseNumberWith readInteger sign cs =
      chain (readInteger cs) (λ integer afterInteger →
        chain (fractionPart afterInteger) (λ fraction afterFraction →
          chain (exponentPart afterFraction) (λ exponent rest →
            inj₂ (Base.jNumber (fromList (sign ++ˡ (integer ++ˡ (fraction ++ˡ exponent)))) , rest))))

    parseNumber : List Char → List Char → Parsed Base.JSON
    parseNumber = parseNumberWith integerPart

    readLiteral : String → List Char → List Char → Parsed ⊤
    readLiteral name [] cs = inj₂ (tt , cs)
    readLiteral name (expected ∷ chars) [] = inj₁ "unexpected EOF"
    readLiteral name (expected ∷ chars) (c ∷ cs) = if sameChar expected c then readLiteral name chars cs else invalid ("in literal " ++ (name ++ (" (expecting " ++ (diagnosticChar expected ++ ")")))) (c ∷ cs)

    literalValue : String → String → Base.JSON → List Char → Parsed Base.JSON
    literalValue name suffix value cs = chain (readLiteral name (toList suffix) cs) (λ _ rest → inj₂ (value , rest))

    arrayAfter : ℕ → List Base.JSON → List Char → Parsed Base.JSON
    arrayItems : ℕ → List Base.JSON → List Char → Parsed Base.JSON
    arrayStart : ℕ → List Char → Parsed Base.JSON
    objectAfter : ℕ → List (String × Base.JSON) → List Char → Parsed Base.JSON
    objectColon : ℕ → List (String × Base.JSON) → String → List Char → Parsed Base.JSON
    objectItems : ℕ → List (String × Base.JSON) → List Char → Parsed Base.JSON
    objectStart : ℕ → List Char → Parsed Base.JSON
    jsonValue : ℕ → List Char → Parsed Base.JSON

  arrayAfter fuel rev (']' ∷ cs) = inj₂ (Base.jArray (reverse rev) , cs)
  arrayAfter fuel rev (',' ∷ cs) = arrayItems fuel rev (skipSpace cs)
  arrayAfter fuel rev cs = invalid "after array element" cs

  arrayItems zero rev cs = inj₁ "unexpected EOF"
  arrayItems (suc fuel) rev cs = chain (jsonValue fuel cs) (λ value rest → arrayAfter fuel (value ∷ rev) (skipSpace rest))

  arrayStart fuel (']' ∷ cs) = inj₂ (Base.jArray [] , cs)
  arrayStart fuel cs = arrayItems fuel [] cs

  objectAfter fuel rev ('}' ∷ cs) = inj₂ (Base.jObject (reverse rev) , cs)
  objectAfter fuel rev (',' ∷ cs) = objectItems fuel rev (skipSpace cs)
  objectAfter fuel rev cs = invalid "after object key:value pair" cs

  objectColon fuel rev name (':' ∷ cs) = chain (jsonValue fuel (skipSpace cs)) (λ value rest → objectAfter fuel ((name , value) ∷ rev) (skipSpace rest))
  objectColon fuel rev name cs = invalid "after object key" cs

  objectItems zero rev cs = inj₁ "unexpected EOF"
  objectItems (suc fuel) rev ('\"' ∷ cs) = chain (stringChars fuel [] cs) (λ name rest → objectColon fuel rev name (skipSpace rest))
  objectItems (suc fuel) rev cs = invalid "looking for beginning of object key string" cs

  objectStart fuel ('}' ∷ cs) = inj₂ (Base.jObject [] , cs)
  objectStart fuel cs = objectItems fuel [] cs

  jsonValue zero cs = inj₁ "unexpected EOF"
  jsonValue (suc fuel) [] = inj₁ "unexpected EOF"
  jsonValue (suc fuel) ('n' ∷ cs) = literalValue "null" "ull" Base.jNull cs
  jsonValue (suc fuel) ('t' ∷ cs) = literalValue "true" "rue" (Base.jBool true) cs
  jsonValue (suc fuel) ('f' ∷ cs) = literalValue "false" "alse" (Base.jBool false) cs
  jsonValue (suc fuel) ('[' ∷ cs) = arrayStart fuel (skipSpace cs)
  jsonValue (suc fuel) ('{' ∷ cs) = objectStart fuel (skipSpace cs)
  jsonValue (suc fuel) ('\"' ∷ cs) = chain (stringChars fuel [] cs) (λ text rest → inj₂ (Base.jString text , rest))
  jsonValue (suc fuel) ('-' ∷ cs) = parseNumber ('-' ∷ []) cs
  jsonValue (suc fuel) (cs@(c ∷ _)) = if digit c then parseNumber [] cs else invalid "looking for beginning of value" cs

  readDocument : String → String ⊎ Base.JSON
  readDocument text with skipSpace (toList text)
  readDocument text | [] = inj₁ "EOF"
  readDocument text | (cs@(_ ∷ _)) = Sum.map (λ reason → reason) proj₁ (jsonValue (suc (length cs)) cs)

  private
    indexDigits : ℕ → List Char → Maybe ℕ
    indexDigits n [] = if (n <ᵇ 9223372036854775808) then just n else nothing
    indexDigits n (c ∷ cs) = if digit c then indexDigits ((10 * n) + (primCharToNat c ∸ 48)) cs else nothing

    indexText : List Char → Maybe ℕ
    indexText [] = nothing
    indexText ('-' ∷ ('0' ∷ [])) = just zero
    indexText cs = indexDigits zero cs

    normalizeTupleValue : Base.JSON → Base.JSON
    normalizeTupleValue (Base.jString text) = Base.jString (if primStringEquality text "<>&" then "<&>" else text)
    normalizeTupleValue value = value

    isDotted : Base.KeyNotation → Bool
    isDotted Base.dotted = true
    isDotted Base.bracketed = false

    pathWord : List Char → List Char × List Char
    pathWord [] = [] , []
    pathWord (cs@(c ∷ _)) = if isDotted (Base.keyNotation (fromList (c ∷ []))) then scanWhile (λ d → isDotted (Base.keyNotation (fromList ('_' ∷ (d ∷ []))))) cs else ([] , cs)

    PathRead : Set
    PathRead = List Char ⊎ (List Base.Segment × List Char)

    closePathBracket : ℕ → List Base.Segment → Base.Segment → List Char → PathRead
    readPathBracket : ℕ → List Base.Segment → List Char → PathRead
    readPathTail : ℕ → List Base.Segment → List Char → PathRead

  closePathBracket fuel rev segment (']' ∷ cs) = readPathTail fuel (segment ∷ rev) (skipSpace cs)
  closePathBracket fuel rev segment cs = inj₁ cs

  readPathBracket fuel rev ('\"' ∷ cs) with stringChars (suc fuel) [] cs
  readPathBracket fuel rev ('\"' ∷ cs) | (inj₁ _) = inj₁ cs
  readPathBracket fuel rev ('\"' ∷ cs) | (inj₂ (name , rest)) = closePathBracket fuel rev (Base.key name) (skipSpace rest)
  readPathBracket fuel rev cs with scanWhile digit cs
  readPathBracket fuel rev cs | (digits , rest) with indexText digits
  readPathBracket fuel rev cs | (digits , rest) | nothing = inj₁ rest
  readPathBracket fuel rev cs | (digits , rest) | (just n) = closePathBracket fuel rev (Base.index n) (skipSpace rest)

  readPathTail zero rev cs = inj₁ cs
  readPathTail (suc fuel) rev ('=' ∷ cs) = inj₂ (reverse rev , cs)
  readPathTail (suc fuel) rev ('[' ∷ cs) = readPathBracket fuel rev (skipSpace cs)
  readPathTail (suc fuel) rev ('.' ∷ cs) with pathWord (skipSpace cs)
  readPathTail (suc fuel) rev ('.' ∷ cs) | ([] , rest) = inj₁ rest
  readPathTail (suc fuel) rev ('.' ∷ cs) | ((c ∷ name) , rest) = readPathTail fuel (Base.key (fromList (c ∷ name)) ∷ rev) (skipSpace rest)
  readPathTail (suc fuel) rev cs = inj₁ cs

  private
    readPathStart : ℕ → List Char → PathRead
    readPathStart fuel cs with pathWord cs
    readPathStart fuel cs | ([] , rest) = inj₁ rest
    readPathStart fuel cs | ((c ∷ name) , rest) = let root = fromList (c ∷ name); rev = if primStringEquality root "json" then [] else (Base.key root ∷ []) in readPathTail fuel rev (skipSpace rest)

    fragmentBefore : List Char → List Char → String
    fragmentBefore whole rest = fromList (take (length whole ∸ length rest) whole)

    withoutValue : List Char → List Char → AssignmentRead
    withoutValue whole rest = rejected (fragmentBefore whole rest) "statement has no value"

    assignmentEnd : List Char → List Base.Segment → Base.JSON → List Char → AssignmentRead
    assignmentEnd whole path value (';' ∷ _) = accepted (Base.statement path value)
    assignmentEnd whole path value rest = withoutValue whole rest

    numberAssignmentEnd : List Char → List Base.Segment → Base.JSON → List Char → AssignmentRead
    numberAssignmentEnd whole path value [] = withoutValue whole []
    numberAssignmentEnd whole path value (';' ∷ _) = accepted (Base.statement path value)
    numberAssignmentEnd whole path value (_ ∷ cs) = numberAssignmentEnd whole path value cs

    emptyValue : List Char → List Base.Segment → Base.JSON → Char → List Char → AssignmentRead
    emptyValue whole path value closer cs with skipSpace cs
    emptyValue whole path value closer cs | [] = withoutValue whole cs
    emptyValue whole path value closer cs | (c ∷ rest) = if sameChar closer c then assignmentEnd whole path value (skipSpace rest) else withoutValue whole cs

    assignmentJSON : Bool → List Char → Parsed Base.JSON
    assignmentJSON true ('-' ∷ cs) = parseNumberWith (needDigits "in numeric literal") ('-' ∷ []) cs
    assignmentJSON true (cs@(c ∷ _)) =
      if digit c then parseNumberWith (needDigits "in numeric literal") [] cs
      else jsonValue (suc (length cs)) cs
    assignmentJSON _ cs = jsonValue (suc (length cs)) cs

    assignmentValue : Bool → List Char → List Base.Segment → List Char → AssignmentRead
    assignmentValue values whole path ('{' ∷ cs) = emptyValue whole path (Base.jObject []) '}' cs
    assignmentValue values whole path ('[' ∷ cs) = emptyValue whole path (Base.jArray []) ']' cs
    assignmentValue values whole path [] = withoutValue whole []
    assignmentValue values whole path (cs@(';' ∷ _)) = withoutValue whole cs
    assignmentValue values whole path cs with assignmentJSON values cs
    assignmentValue values whole path cs | (inj₁ reason) = rejected (fromList whole) reason
    assignmentValue values whole path cs | (inj₂ (Base.jNumber spelling , rest)) =
      if values then assignmentEnd whole path (Base.jNumber spelling) (skipSpace rest)
      else numberAssignmentEnd whole path (Base.jNumber spelling) rest
    assignmentValue values whole path cs | (inj₂ (value , rest)) =
      assignmentEnd whole path (if values then normalizeTupleValue value else value) (skipSpace rest)

    assignmentLine : Bool → List Char → List Char → AssignmentRead
    assignmentLine values whole [] = skipped
    assignmentLine values whole (cs@('/' ∷ ('/' ∷ _))) =
      if values ∨ (length cs <ᵇ length whole) then skipped else rejected "" "invalid statement"
    assignmentLine values whole (cs@(_ ∷ _)) with readPathStart (suc (length cs)) cs
    assignmentLine values whole (cs@(_ ∷ _)) | (inj₁ rest) = rejected (fragmentBefore whole rest) "invalid statement"
    assignmentLine values whole (cs@(_ ∷ _)) | (inj₂ (path , rest)) = assignmentValue values whole path (skipSpace rest)

  readAssignment : String → AssignmentRead
  readAssignment text = let cs = toList text in assignmentLine false cs (skipSpace cs)

  readValueAssignment : String → AssignmentRead
  readValueAssignment text = let cs = toList text in assignmentLine true cs (skipSpace cs)

  private
    controlEscape : ℕ → List Char
    controlEscape n = '\\' ∷ ('u' ∷ ('0' ∷ ('0' ∷ ((if (n <ᵇ 16) then '0' else '1') ∷ (hexDigit (if (n <ᵇ 16) then n else (n ∸ 16)) ∷ [])))))

    escapeCharacter : Bool → Char → List Char
    escapeCharacter _ '\"' = toList "\\\""
    escapeCharacter _ '\\' = toList "\\\\"
    escapeCharacter true '&' = toList "\\u0026"
    escapeCharacter true '<' = toList "\\u003c"
    escapeCharacter true '>' = toList "\\u003e"
    escapeCharacter _ c = let n = primCharToNat c in if (n ≡ᵇ 8) then toList "\\b" else (if (n ≡ᵇ 9) then toList "\\t" else (if (n ≡ᵇ 10) then toList "\\n" else (if (n ≡ᵇ 12) then toList "\\f" else (if (n ≡ᵇ 13) then toList "\\r" else (if (n ≡ᵇ 8232) then toList "\\u2028" else (if (n ≡ᵇ 8233) then toList "\\u2029" else (if (n <ᵇ 32) then controlEscape n else (c ∷ []))))))))

    escapeChars : Bool → List Char → List Char
    escapeChars html [] = []
    escapeChars html (c ∷ cs) = escapeCharacter html c ++ˡ escapeChars html cs

    quoteChars : Bool → String → List Char
    quoteChars html text = '\"' ∷ (escapeChars html (toList text) ++ˡ ('\"' ∷ []))

    keyCharacters : Base.KeyNotation → String → List Char
    keyCharacters Base.dotted k = '.' ∷ toList k
    keyCharacters Base.bracketed k = '[' ∷ (quoteChars true k ++ˡ (']' ∷ []))

  renderKey : String → List Char
  renderKey k = keyCharacters (Base.keyNotation k) k

  private
    ansiPrefix : String
    ansiPrefix = fromList (primNatToChar 27 ∷ ('[' ∷ []))

    paint : Base.Style → String → String → String → String
    paint Base.plain start stop text = text
    paint Base.ansi start stop text = ansiPrefix ++ (start ++ ("m" ++ (text ++ (ansiPrefix ++ (stop ++ "m")))))

    punct : Base.Style → String → String
    punct style = paint style "35" "0"

    identifier : Base.Style → String → String
    identifier style = paint style "34;1" "0;22"

    escapeJSONValue : List Char → List Char
    escapeJSONValue [] = []
    escapeJSONValue ('<' ∷ ('&' ∷ ('>' ∷ cs))) = '<' ∷ ('>' ∷ ('&' ∷ escapeJSONValue cs))
    escapeJSONValue (c ∷ cs) = escapeCharacter false c ++ˡ escapeJSONValue cs

    quotedValue : Base.Style → String → String
    quotedValue style text = paint style "32" "0" "\"" ++ (paint style "33" "0" (fromList (escapeJSONValue (toList text))) ++ paint style "32" "0" "\"")

    objectKey : Base.Style → String → String
    objectKey style name = identifier style "\"" ++ (identifier style (fromList (escapeChars false (toList name))) ++ identifier style "\"")

    linePrefix : Bool → String → String
    linePrefix true indent = "\n" ++ indent
    linePrefix false indent = ""

    objectSeparator : Bool → Base.Style → String
    objectSeparator multiline style = paint style "1" "22" ":" ++ (if multiline then " " else "")

    formatArray : Bool → Base.Style → String → String → List Base.JSON → String
    formatObject : Bool → Base.Style → String → String → List (String × Base.JSON) → String
    formatValue : Bool → Base.Style → String → Base.JSON → String

  formatArray multiline style indent separator [] = ""
  formatArray multiline style indent separator (value ∷ rest) = separator ++ (linePrefix multiline indent ++ (formatValue multiline style indent value ++ formatArray multiline style indent (paint style "1" "22" ",") rest))

  formatObject multiline style indent separator [] = ""
  formatObject multiline style indent separator ((name , value) ∷ rest) = separator ++ (linePrefix multiline indent ++ (objectKey style name ++ (objectSeparator multiline style ++ (formatValue multiline style indent value ++ formatObject multiline style indent (paint style "1" "22" ",") rest))))

  formatValue multiline style indent Base.jNull = paint style "36" "0" "null"
  formatValue multiline style indent (Base.jBool true) = paint style "36" "0" "true"
  formatValue multiline style indent (Base.jBool false) = paint style "36" "0" "false"
  formatValue multiline style indent (Base.jNumber spelling) = paint style "31" "0" spelling
  formatValue multiline style indent (Base.jString text) = quotedValue style text
  formatValue multiline style indent (Base.jArray []) = punct style "[]"
  formatValue multiline style indent (Base.jArray items) = punct style "[" ++ (formatArray multiline style (indent ++ "  ") "" items ++ (linePrefix multiline indent ++ punct style "]"))
  formatValue multiline style indent (Base.jObject []) = punct style "{}"
  formatValue multiline style indent (Base.jObject fields) = punct style "{" ++ (formatObject multiline style (indent ++ "  ") "" fields ++ (linePrefix multiline indent ++ punct style "}"))

  private
    statementValue : Base.Style → Base.JSON → String
    statementValue style (Base.jString text) = paint style "33" "0" (fromList (quoteChars false text))
    statementValue style value = formatValue false style "" value

    assignmentKey : Base.Style → String → String
    assignmentKey Base.plain name = fromList (renderKey name)
    assignmentKey Base.ansi name with Base.keyNotation name
    assignmentKey Base.ansi name | Base.dotted = "." ++ identifier Base.ansi name
    assignmentKey Base.ansi name | Base.bracketed = punct Base.ansi "[" ++ (paint Base.ansi "33" "0" (fromList (quoteChars true name)) ++ punct Base.ansi "]")

    formatAssignmentPath : Base.Style → List Base.Segment → String
    formatAssignmentPath style [] = ""
    formatAssignmentPath style ((Base.key name) ∷ rest) = assignmentKey style name ++ formatAssignmentPath style rest
    formatAssignmentPath style ((Base.index n) ∷ rest) = punct style "[" ++ (paint style "31" "0" (Nat.show n) ++ (punct style "]" ++ formatAssignmentPath style rest))

    tupleSegment : Base.Style → Base.Segment → String
    tupleSegment style (Base.key name) = paint style "33" "0" (fromList (quoteChars false name))
    tupleSegment style (Base.index n) = paint style "31" "0" (Nat.show n)

    formatTuplePath : Base.Style → String → List Base.Segment → String
    formatTuplePath style separator [] = ""
    formatTuplePath style separator (part ∷ rest) = separator ++ (tupleSegment style part ++ formatTuplePath style "," rest)

  renderStatement : StatementEncoding → Base.Style → Base.Statement → String
  renderStatement assignments style (Base.statement path value) = identifier style "json" ++ (formatAssignmentPath style path ++ (" = " ++ (statementValue style value ++ ";\n")))
  renderStatement tuples style (Base.statement path value) = punct style "[" ++ (punct style "[" ++ (formatTuplePath style "" path ++ (punct style "]" ++ ("," ++ (statementValue style value ++ (punct style "]" ++ "\n"))))))

  renderJSON : Base.Style → Base.JSON → String
  renderJSON Base.plain value = formatValue true Base.plain "" value ++ "\n"
  renderJSON Base.ansi value = formatValue false Base.ansi "" value ++ "\n"

  private
    quotient : ℕ → ℕ → ℕ
    quotient numerator denominator =
      let predecessor = denominator ∸ 1
      in div-helper 0 predecessor numerator predecessor

    powerWithFuel : ℕ → ℕ → ℕ → ℕ
    powerWithFuel zero base exponent = 1
    powerWithFuel (suc fuel) base exponent =
      if exponent ≡ᵇ 0 then 1
      else
        let half = quotient exponent 2
            squarePower = powerWithFuel fuel (base * base) half
        in if exponent ≡ᵇ (2 * half) then squarePower else base * squarePower

    power : ℕ → ℕ → ℕ
    power base exponent = powerWithFuel exponent base exponent

    evenNumber : ℕ → Bool
    evenNumber n = n ≡ᵇ (2 * quotient n 2)

    nearestInteger : ℕ → ℕ → ℕ
    nearestInteger numerator denominator =
      let floor = quotient numerator denominator
          twiceRemainder = 2 * (numerator ∸ (floor * denominator))
      in if (twiceRemainder <ᵇ denominator) ∨
            ((twiceRemainder ≡ᵇ denominator) ∧ evenNumber floor)
         then floor else suc floor

    decimalDigits : ℕ → List Char → ℕ
    decimalDigits n [] = n
    decimalDigits n (c ∷ cs) = decimalDigits ((10 * n) + (primCharToNat c ∸ 48)) cs

    signedOffset : List Char → ℕ × ℕ
    signedOffset ('-' ∷ cs) = 0 , decimalDigits 0 cs
    signedOffset ('+' ∷ cs) = decimalDigits 0 cs , 0
    signedOffset cs = decimalDigits 0 cs , 0

    exponentOffset : List Char → ℕ × ℕ
    exponentOffset ('e' ∷ cs) = signedOffset cs
    exponentOffset ('E' ∷ cs) = signedOffset cs
    exponentOffset _ = 0 , 0

    decimalMagnitude : List Char → ℕ → List Char → Maybe (ℕ × ℕ)
    decimalMagnitude digits fractionalPlaces suffix with proj₂ (scanWhile (sameChar '0') digits) | exponentOffset suffix
    decimalMagnitude digits fractionalPlaces suffix | [] | _ = just (0 , 1)
    decimalMagnitude digits fractionalPlaces suffix | (significant@(_ ∷ _)) | (upward , downward) =
      let negativePlaces = downward + fractionalPlaces
          places = length significant + upward
      in if (negativePlaces + 309) <ᵇ places then nothing
         else if (places + 323) <ᵇ negativePlaces then just (0 , 1)
         else just (decimalDigits 0 significant * power 10 (upward ∸ negativePlaces) ,
                    power 10 (negativePlaces ∸ upward))

    decimalRatio : List Char → Maybe (ℕ × ℕ)
    decimalRatio cs with scanWhile digit cs
    decimalRatio cs | (whole , ('.' ∷ digits)) with scanWhile digit digits
    decimalRatio cs | (whole , ('.' ∷ digits)) | (fraction , suffix) =
      decimalMagnitude (whole ++ˡ fraction) (length fraction) suffix
    decimalRatio cs | (whole , suffix) = decimalMagnitude whole 0 suffix

    findScale : (fuel base numerator denominator lower upper : ℕ) → ℕ
    findScale zero base numerator denominator lower upper = lower
    findScale (suc fuel) base numerator denominator lower upper =
      let middle = quotient (lower + upper) 2
      in if middle ≡ᵇ lower then lower
         else if numerator <ᵇ (denominator * power base middle)
         then findScale fuel base numerator denominator lower middle
         else findScale fuel base numerator denominator middle upper

    -- Scale zero uses the subnormal quantum. Higher scales double that quantum.
    roundBinary : ℕ → ℕ → Maybe (ℕ × ℕ)
    roundBinary numerator denominator with numerator ≡ᵇ 0
    roundBinary numerator denominator | true = just (0 , 0)
    roundBinary numerator denominator | false =
      let scale = findScale 11 2 (numerator * power 2 1022) denominator 0 2046
          scaledNumerator = numerator * power 2 (1074 ∸ scale)
          scaledDenominator = denominator * power 2 (scale ∸ 1074)
          significand = nearestInteger scaledNumerator scaledDenominator
      in if significand <ᵇ 9007199254740992 then just (significand , scale)
         else if scale <ᵇ 2045 then just (4503599627370496 , suc scale)
         else nothing

    inDecimalWindow : Bool → ℕ → ℕ → ℕ → Bool
    inDecimalWindow true lower upper n = not (n <ᵇ lower) ∧ not (upper <ᵇ n)
    inDecimalWindow false lower upper n = (lower <ᵇ n) ∧ (n <ᵇ upper)

    shortestDigits : (fuel : ℕ) → (includeEndpoints : Bool) →
                     (denominator center lower upper precision : ℕ) → ℕ × ℕ
    shortestDigits zero includeEndpoints denominator center lower upper precision =
      nearestInteger center denominator , precision
    shortestDigits (suc fuel) includeEndpoints denominator center lower upper precision =
      let nearest = nearestInteger center denominator
          floor = quotient center denominator
          other = if nearest ≡ᵇ floor then suc floor else floor
      in if inDecimalWindow includeEndpoints lower upper (nearest * denominator)
         then (nearest , precision)
         else if inDecimalWindow includeEndpoints lower upper (other * denominator)
         then (other , precision)
         else shortestDigits fuel includeEndpoints denominator (10 * center)
                (10 * lower) (10 * upper) (suc precision)

    fixedDigits : ℕ → List Char → List Char
    fixedDigits zero [] = []
    fixedDigits zero (cs@(_ ∷ _)) = '.' ∷ cs
    fixedDigits (suc places) [] = '0' ∷ fixedDigits places []
    fixedDigits (suc places) (c ∷ cs) = c ∷ fixedDigits places cs

    renderDecimal : ℕ → ℕ → ℕ → String
    renderDecimal order precision coefficient =
      let digits = toList (primShowNat coefficient)
          significant = reverse (proj₂ (scanWhile (sameChar '0') (reverse digits)))
          before = order + length digits
          after = 324 + precision
      in if ((before + 5) <ᵇ after) ∨ ((after + 21) <ᵇ before)
         then fromList (fixedDigits 1 significant) ++
              (if before <ᵇ suc after
               then "e-" ++ primShowNat (suc after ∸ before)
               else "e+" ++ primShowNat (before ∸ suc after))
         else if after <ᵇ before
         then fromList (fixedDigits (before ∸ after) significant)
         else "0." ++ fromList (fixedDigits (after ∸ before) [] ++ˡ significant)

    -- A quarter of the binary step also represents the closer lower midpoint
    -- at the first value of a normal binade above the subnormal range.
    shortest64 : ℕ → ℕ → String
    shortest64 significand scale with significand ≡ᵇ 0
    shortest64 significand scale | true = "0"
    shortest64 significand scale | false =
      let numeratorFactor = power 2 (scale ∸ 1074)
          denominatorFactor = power 2 (1074 ∸ scale)
          order = findScale 10 10 ((significand * numeratorFactor) * power 10 324)
                    denominatorFactor 0 633
          factor = numeratorFactor * power 10 (324 ∸ order)
          denominator = (4 * denominatorFactor) * power 10 (order ∸ 324)
          center = 4 * significand
          lowerDistance = if (significand ≡ᵇ 4503599627370496) ∧ (0 <ᵇ scale) then 1 else 2
          digits = shortestDigits 17 (evenNumber significand) denominator (center * factor)
                     ((center ∸ lowerDistance) * factor) ((center + 2) * factor) 0
      in renderDecimal order (proj₂ digits) (proj₁ digits)

    binary64Magnitude : List Char → Maybe String
    binary64Magnitude cs with decimalRatio cs
    binary64Magnitude cs | nothing = nothing
    binary64Magnitude cs | (just (numerator , denominator)) =
      mapMaybe (λ result → shortest64 (proj₁ result) (proj₂ result)) (roundBinary numerator denominator)

    binary64Spelling : List Char → Maybe String
    binary64Spelling ('-' ∷ cs) = mapMaybe (λ magnitude → "-" ++ magnitude) (binary64Magnitude cs)
    binary64Spelling cs = binary64Magnitude cs

    tupleNumberText : String → String ⊎ String
    tupleNumberText spelling with binary64Spelling (toList spelling)
    tupleNumberText spelling | nothing =
      inj₁ ("json: cannot unmarshal number " ++ (spelling ++ " into Go value of type float64"))
    tupleNumberText spelling | (just text) = inj₂ text

    bindResult : {A B : Set} → String ⊎ A → (A → String ⊎ B) → String ⊎ B
    bindResult (inj₁ reason) next = inj₁ reason
    bindResult (inj₂ value) next = next value

    normalizeTupleNumbers : Base.JSON → String ⊎ Base.JSON
    normalizeTupleArray : List Base.JSON → String ⊎ List Base.JSON
    normalizeTupleObject : List (String × Base.JSON) → String ⊎ List (String × Base.JSON)

  normalizeTupleNumbers (Base.jNumber spelling) = Sum.map (λ reason → reason) Base.jNumber (tupleNumberText spelling)
  normalizeTupleNumbers (Base.jArray values) = Sum.map (λ reason → reason) Base.jArray (normalizeTupleArray values)
  normalizeTupleNumbers (Base.jObject fields) = Sum.map (λ reason → reason) Base.jObject (normalizeTupleObject fields)
  normalizeTupleNumbers value = inj₂ value

  normalizeTupleArray [] = inj₂ []
  normalizeTupleArray (value ∷ rest) =
    bindResult (normalizeTupleNumbers value) (λ normalized →
      Sum.map (λ reason → reason) (λ values → normalized ∷ values) (normalizeTupleArray rest))

  normalizeTupleObject [] = inj₂ []
  normalizeTupleObject ((name , value) ∷ rest) =
    bindResult (normalizeTupleNumbers value) (λ normalized →
      Sum.map (λ reason → reason) (λ fields → (name , normalized) ∷ fields) (normalizeTupleObject rest))

  private
    tupleSegments : List Base.JSON → Maybe (String ⊎ List Base.Segment)
    tupleSegments [] = just (inj₂ [])
    tupleSegments ((Base.jString name) ∷ rest) with tupleSegments rest
    tupleSegments ((Base.jString name) ∷ rest) | nothing = nothing
    tupleSegments ((Base.jString name) ∷ rest) | (just segments) =
      just (Sum.map (λ reason → reason) (λ path → Base.key name ∷ path) segments)
    tupleSegments ((Base.jNumber spelling) ∷ rest) with tupleSegments rest
    tupleSegments ((Base.jNumber spelling) ∷ rest) | nothing = nothing
    tupleSegments ((Base.jNumber spelling) ∷ rest) | (just segments) with indexText (toList spelling)
    tupleSegments ((Base.jNumber spelling) ∷ rest) | (just segments) | nothing = just (inj₁ spelling)
    tupleSegments ((Base.jNumber spelling) ∷ rest) | (just segments) | (just n) =
      just (Sum.map (λ reason → reason) (λ path → Base.index n ∷ path) segments)
    tupleSegments (_ ∷ _) = nothing

    tuplePathText : List Base.JSON → String
    tuplePathText [] = ""
    tuplePathText ((Base.jString name) ∷ rest) = fromList (renderKey name) ++ tuplePathText rest
    tuplePathText ((Base.jNumber spelling) ∷ rest) = "[" ++ (spelling ++ ("]" ++ tuplePathText rest))
    tuplePathText (_ ∷ rest) = tuplePathText rest

    tupleLayout : Base.JSON → String ⊎ Base.Statement
    tupleLayout (Base.jArray ((Base.jArray _) ∷ ((Base.jArray (_ ∷ _)) ∷ []))) = inj₁ "invalid JSON layout"
    tupleLayout (Base.jArray ((Base.jArray _) ∷ ((Base.jObject (_ ∷ _)) ∷ []))) = inj₁ "invalid JSON layout"
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) with tupleSegments parts
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) | nothing = inj₁ "invalid JSON layout"
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) | (just (inj₁ spelling)) =
      let assignment = "json" ++ (tuplePathText parts ++ (" = " ++ (statementValue Base.plain value ++ ";")))
      in inj₁ ("ungron failed for `" ++ (assignment ++ ("`: invalid integer key `" ++ (spelling ++ "`"))))
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) | (just (inj₂ path)) =
      inj₂ (Base.statement path (normalizeTupleValue value))
    tupleLayout _ = inj₁ "invalid JSON layout"

    finishTuple : Parsed Base.JSON → String ⊎ Base.Statement
    finishTuple (inj₁ reason) = inj₁ (if primStringEquality reason "unexpected EOF" then "unexpected end of JSON input" else reason)
    finishTuple (inj₂ (value , rest)) with skipSpace rest
    finishTuple (inj₂ (value , rest)) | [] = bindResult (normalizeTupleNumbers value) tupleLayout
    finishTuple (inj₂ (value , rest)) | (cs@(_ ∷ _)) = invalid "after top-level value" cs

  readTuple : String → String ⊎ Base.Statement
  readTuple text = let cs = skipSpace (toList text) in finishTuple (jsonValue (suc (length cs)) cs)

  keySquare : Commutes₁ (keepPort String) keyPort (λ _ → ⊤) _≡_ Base.keyNotation renderKey
  keySquare k _ with Base.keyNotation k
  keySquare k _ | Base.dotted = refl
  keySquare k _ | Base.bracketed = refl

  dottedKeyText : (k : String) → (Base.keyNotation k ≡ Base.dotted) → renderKey k ≡ ('.' ∷ toList k)
  dottedKeyText k eq rewrite eq = refl

  reservedKeyText : fromList (renderKey "class") ≡ "[\"class\"]"
  reservedKeyText = refl

  bracketKeyText : fromList (renderKey "a\"b\\c\n") ≡ "[\"a\\\"b\\\\c\\n\"]"
  bracketKeyText = refl

  joiningKeyText : fromList (renderKey (fromList ('a' ∷ (primNatToChar 8204 ∷ [])))) ≡ fromList ('[' ∷ ('\"' ∷ ('a' ∷ (primNatToChar 8204 ∷ ('\"' ∷ (']' ∷ []))))))
  joiningKeyText = refl

  firstDocument : readDocument "1 2" ≡ inj₂ (Base.jNumber "1")
  firstDocument = refl

  numericSpellings : readDocument "[1.0,1e+02,-0,9007199254740993,1e-09,1e-7,1e20]" ≡ inj₂ (Base.jArray (Base.jNumber "1.0" ∷ (Base.jNumber "1e+02" ∷ (Base.jNumber "-0" ∷ (Base.jNumber "9007199254740993" ∷ (Base.jNumber "1e-09" ∷ (Base.jNumber "1e-7" ∷ (Base.jNumber "1e20" ∷ []))))))))
  numericSpellings = refl

  stringEscapes : Sum.map (λ reason → reason) (λ value → renderStatement assignments Base.plain (Base.statement [] value)) (readDocument "\"<>&\\u2028\\u2029\\ud800\"") ≡ inj₂ "json = \"<>&\\u2028\\u2029�\";\n"
  stringEscapes = refl

  duplicateDocument : Sum.map (λ reason → reason) (Base.flatten Base.sortPaths) (readDocument "{\"a\":{\"x\":1},\"a\":{\"y\":2},\"b\":1,\"b\":2}") ≡ inj₂ (Base.statement [] (Base.jObject []) ∷ (Base.statement (Base.key "a" ∷ []) (Base.jObject []) ∷ (Base.statement (Base.key "a" ∷ (Base.key "y" ∷ [])) (Base.jNumber "2") ∷ (Base.statement (Base.key "b" ∷ []) (Base.jNumber "2") ∷ []))))
  duplicateDocument = refl

  emptyDocument : readDocument "" ≡ inj₁ "EOF"
  emptyDocument = refl

  truncatedDocument : readDocument "{\"k\":100" ≡ inj₁ "unexpected EOF"
  truncatedDocument = refl

  badArrayValue : readDocument "[29,]" ≡ inj₁ "invalid character ']' looking for beginning of value"
  badArrayValue = refl

  missingObjectColon : readDocument "{\"146\" 146}" ≡ inj₁ "invalid character '1' after object key"
  missingObjectColon = refl

  missingObjectComma : readDocument "{\"k\":219 \"j\":0}" ≡ inj₁ "invalid character '\"' after object key:value pair"
  missingObjectComma = refl

  missingArrayComma : readDocument "[72 null]" ≡ inj₁ "invalid character 'n' after array element"
  missingArrayComma = refl

  badStringEscape : readDocument "\"105\\q\"" ≡ inj₁ "invalid character 'q' in string escape code"
  badStringEscape = refl

  badLiteral : readDocument "[nul14]" ≡ inj₁ "invalid character '1' in literal null (expecting 'l')"
  badLiteral = refl

  badExponent : readDocument "[71e+]" ≡ inj₁ "invalid character ']' in exponent of numeric literal"
  badExponent = refl

  badHexEscape : readDocument "[\"\\u245g\"]" ≡ inj₁ "invalid character 'g' in \\u hexadecimal character escape"
  badHexEscape = refl

  emptyAssignmentLine : readAssignment "" ≡ skipped
  emptyAssignmentLine = refl

  compactAssignment : readAssignment "json.a=1;" ≡ accepted (Base.statement (Base.key "a" ∷ []) (Base.jNumber "1"))
  compactAssignment = refl

  rewrittenRoot : readAssignment "renamed.a = 1;" ≡ accepted (Base.statement (Base.key "renamed" ∷ (Base.key "a" ∷ [])) (Base.jNumber "1"))
  rewrittenRoot = refl

  escapedAssignmentKey : readAssignment "json[\"a = b.c\\\"d\\\\e\"] = true;" ≡ accepted (Base.statement (Base.key "a = b.c\"d\\e" ∷ []) (Base.jBool true))
  escapedAssignmentKey = refl

  paddedIndex : readAssignment "json.a[01] = 3;" ≡ accepted (Base.statement (Base.key "a" ∷ (Base.index 1 ∷ [])) (Base.jNumber "3"))
  paddedIndex = refl

  trailingComment : readAssignment "json.a = 1; // tail" ≡ accepted (Base.statement (Base.key "a" ∷ []) (Base.jNumber "1"))
  trailingComment = refl

  largeExponent : readAssignment "json = 1e9999;" ≡ accepted (Base.statement [] (Base.jNumber "1e9999"))
  largeExponent = refl

  assignmentNumberSpellings :
    map readAssignment ("json.a = 1.0;" ∷ "json.b = 1e+02;" ∷ "json.c = -0;" ∷ "json.d = 9007199254740993;" ∷ []) ≡
      (accepted (Base.statement (Base.key "a" ∷ []) (Base.jNumber "1.0")) ∷
       accepted (Base.statement (Base.key "b" ∷ []) (Base.jNumber "1e+02")) ∷
       accepted (Base.statement (Base.key "c" ∷ []) (Base.jNumber "-0")) ∷
       accepted (Base.statement (Base.key "d" ∷ []) (Base.jNumber "9007199254740993")) ∷ [])
  assignmentNumberSpellings = refl

  assignmentFirstNumber :
    map readAssignment ("json = 01;" ∷ "json = -012;" ∷ "json = 01.5;" ∷ "json = 1 2;" ∷ []) ≡
      (accepted (Base.statement [] (Base.jNumber "0")) ∷
       accepted (Base.statement [] (Base.jNumber "-0")) ∷
       accepted (Base.statement [] (Base.jNumber "0")) ∷
       accepted (Base.statement [] (Base.jNumber "1")) ∷ [])
  assignmentFirstNumber = refl

  missingSemicolon : readAssignment "json.a = 1" ≡ rejected "json.a = 1" "statement has no value"
  missingSemicolon = refl

  leadingZeroWithoutSemicolon : readAssignment "json = 01" ≡ rejected "json = 01" "statement has no value"
  leadingZeroWithoutSemicolon = refl

  leadingComment : readAssignment "// comment" ≡ rejected "" "invalid statement"
  leadingComment = refl

  indentedComment : readAssignment "  // comment" ≡ skipped
  indentedComment = refl

  singleQuotedKey : readAssignment "json['a'] = 2;" ≡ rejected "json[" "invalid statement"
  singleQuotedKey = refl

  inlineObject : readAssignment "json.a = {\"x\":2};" ≡ rejected "json.a = {" "statement has no value"
  inlineObject = refl

  valuesComment : readValueAssignment "// comment" ≡ skipped
  valuesComment = refl

  valuesLeadingZero : readValueAssignment "json = 01;" ≡ accepted (Base.statement [] (Base.jNumber "01"))
  valuesLeadingZero = refl

  valuesScalarAssignments :
    map readValueAssignment ("json.a[2] = 1e+02;" ∷ "json.n = null;" ∷ "json[\"with space\"] = \"<>&\";" ∷ []) ≡
      (accepted (Base.statement (Base.key "a" ∷ Base.index 2 ∷ []) (Base.jNumber "1e+02")) ∷
       accepted (Base.statement (Base.key "n" ∷ []) Base.jNull) ∷
       accepted (Base.statement (Base.key "with space" ∷ []) (Base.jString "<&>")) ∷ [])
  valuesScalarAssignments = refl

  tupleRoot : readTuple "[[],{}]" ≡ inj₂ (Base.statement [] (Base.jObject []))
  tupleRoot = refl

  tupleEmptyArray : readTuple "[[],[]]" ≡ inj₂ (Base.statement [] (Base.jArray []))
  tupleEmptyArray = refl

  tuplePath : readTuple "[[\"a\",2],\"<>&\"]" ≡ inj₂ (Base.statement (Base.key "a" ∷ (Base.index 2 ∷ [])) (Base.jString "<&>"))
  tuplePath = refl

  tuplePathType : readTuple "[[true],1]" ≡ inj₁ "invalid JSON layout"
  tuplePathType = refl

  tupleArity : readTuple "[[\"a\"],1,2]" ≡ inj₁ "invalid JSON layout"
  tupleArity = refl

  blankTuple : readTuple "" ≡ inj₁ "unexpected end of JSON input"
  blankTuple = refl

  tupleBinary64Numbers :
    map readTuple ("[[0],1.0]" ∷ "[[1],1e+02]" ∷ "[[2],-0]" ∷ "[[3],9007199254740993]" ∷
                   "[[4],9007199254740995]" ∷ "[[5],1e-6]" ∷ "[[6],1e-7]" ∷ "[[7],1e20]" ∷
                   "[[8],1e21]" ∷ "[[9],-1e-999]" ∷ "[[10],0.100000000000000005]" ∷
                   "[[11],5e-324]" ∷ []) ≡
      (inj₂ (Base.statement (Base.index 0 ∷ []) (Base.jNumber "1")) ∷
       inj₂ (Base.statement (Base.index 1 ∷ []) (Base.jNumber "100")) ∷
       inj₂ (Base.statement (Base.index 2 ∷ []) (Base.jNumber "-0")) ∷
       inj₂ (Base.statement (Base.index 3 ∷ []) (Base.jNumber "9007199254740992")) ∷
       inj₂ (Base.statement (Base.index 4 ∷ []) (Base.jNumber "9007199254740996")) ∷
       inj₂ (Base.statement (Base.index 5 ∷ []) (Base.jNumber "0.000001")) ∷
       inj₂ (Base.statement (Base.index 6 ∷ []) (Base.jNumber "1e-7")) ∷
       inj₂ (Base.statement (Base.index 7 ∷ []) (Base.jNumber "100000000000000000000")) ∷
       inj₂ (Base.statement (Base.index 8 ∷ []) (Base.jNumber "1e+21")) ∷
       inj₂ (Base.statement (Base.index 9 ∷ []) (Base.jNumber "-0")) ∷
       inj₂ (Base.statement (Base.index 10 ∷ []) (Base.jNumber "0.1")) ∷
       inj₂ (Base.statement (Base.index 11 ∷ []) (Base.jNumber "5e-324")) ∷ [])
  tupleBinary64Numbers = refl

  tupleNestedValue : readTuple "[[],{\"a\":[1.0,1e+02,-0,9007199254740993]}]" ≡ inj₁ "invalid JSON layout"
  tupleNestedValue = refl

  tupleNumberOverflow : readTuple "[[],1e9999]" ≡ inj₁ "json: cannot unmarshal number 1e9999 into Go value of type float64"
  tupleNumberOverflow = refl

  tupleFractionalIndex : readTuple "[[1.9],true]" ≡ inj₁ "ungron failed for `json[1.9] = true;`: invalid integer key `1.9`"
  tupleFractionalIndex = refl

  tupleExponentIndex : readTuple "[[1e0],true]" ≡ inj₂ (Base.statement (Base.index 1 ∷ []) (Base.jBool true))
  tupleExponentIndex = refl

  plainAssignment : renderStatement assignments Base.plain (Base.statement (Base.key "items" ∷ (Base.index 10 ∷ [])) (Base.jNumber "1e+02")) ≡ "json.items[10] = 1e+02;\n"
  plainAssignment = refl

  plainBracketAssignment : renderStatement assignments Base.plain (Base.statement (Base.key "two words" ∷ []) (Base.jObject [])) ≡ "json[\"two words\"] = {};\n"
  plainBracketAssignment = refl

  plainTuple : renderStatement tuples Base.plain (Base.statement (Base.key "items" ∷ (Base.index 2 ∷ [])) Base.jNull) ≡ "[[\"items\",2],null]\n"
  plainTuple = refl

  coloredAssignment : renderStatement assignments Base.ansi (Base.statement (Base.key "items" ∷ (Base.index 1 ∷ [])) (Base.jBool true)) ≡ "[34;1mjson[0;22m.[34;1mitems[0;22m[35m[[0m[31m1[0m[35m][0m = [36mtrue[0m;\n"
  coloredAssignment = refl

  coloredBracketAssignment : renderStatement assignments Base.ansi (Base.statement (Base.key "two words" ∷ []) (Base.jObject [])) ≡ "[34;1mjson[0;22m[35m[[0m[33m\"two words\"[0m[35m][0m = [35m{}[0m;\n"
  coloredBracketAssignment = refl

  coloredTuple : renderStatement tuples Base.ansi (Base.statement (Base.key "a b" ∷ (Base.index 0 ∷ [])) (Base.jBool true)) ≡ "[35m[[0m[35m[[0m[33m\"a b\"[0m,[31m0[0m[35m][0m,[36mtrue[0m[35m][0m\n"
  coloredTuple = refl

  prettyJSON : renderJSON Base.plain (Base.jObject (("a" , Base.jArray (Base.jObject (("k" , Base.jNumber "1") ∷ []) ∷ (Base.jNull ∷ (Base.jString "<&>" ∷ [])))) ∷ (("z z" , Base.jBool true) ∷ []))) ≡ "{\n  \"a\": [\n    {\n      \"k\": 1\n    },\n    null,\n    \"<>&\"\n  ],\n  \"z z\": true\n}\n"
  prettyJSON = refl

  coloredJSON : renderJSON Base.ansi (Base.jObject (("a" , Base.jNumber "9007199254740993") ∷ (("b" , Base.jNumber "1e+02") ∷ (("c" , Base.jNumber "-0") ∷ (("d" , Base.jString (fromList (primNatToChar 8232 ∷ (primNatToChar 8233 ∷ ('<' ∷ ('&' ∷ ('>' ∷ (primNatToChar 0 ∷ [])))))))) ∷ []))))) ≡ ("[35m{[0m[34;1m\"[0;22m[34;1ma[0;22m[34;1m\"[0;22m[1m:[22m[31m9007199254740993[0m[1m,[22m" ++ ("[34;1m\"[0;22m[34;1mb[0;22m[34;1m\"[0;22m[1m:[22m[31m1e+02[0m[1m,[22m" ++ ("[34;1m\"[0;22m[34;1mc[0;22m[34;1m\"[0;22m[1m:[22m[31m-0[0m[1m,[22m" ++ "[34;1m\"[0;22m[34;1md[0;22m[34;1m\"[0;22m[1m:[22m[32m\"[0m[33m\\u2028\\u2029<>&\\u0000[0m[32m\"[0m[35m}[0m\n")))
  coloredJSON = refl
