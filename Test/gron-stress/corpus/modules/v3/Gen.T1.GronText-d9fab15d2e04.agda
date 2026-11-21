module Gen.T1.GronText where

  open import Agda.Builtin.Nat using (div-helper)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _<ᵇ_)
  import Data.Nat.Show as Nat
  open import Agda.Builtin.Char using (Char; primCharToNat; primNatToChar)
  open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
  open import Data.List using (List; []; _∷_; length; take; reverse) renaming (_++_ to _++ˡ_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.String using (String; fromList; toList; _++_)
  open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; map)
  open import Data.Unit using (⊤; tt)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Context.Blueprint using (PortLift; portLift; keepPort; Commutes₁)
  import Gen.T0.Gron as Base
  open import Agda.Builtin.Char using (Char; primNatToChar)
  open import Data.Bool using (true)
  open import Data.List using (List; []; _∷_)
  open import Data.Product using (_,_)
  open import Data.String using (String; fromList; toList)
  open import Data.Unit using (⊤)
  open import Relation.Binary.PropositionalEquality using (_≡_)
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
  private
    digit : Char → Bool
    digit c = within 48 58 (primCharToNat c)
  private
    sameChar : Char → Char → Bool
    sameChar c d = primCharToNat c ≡ᵇ primCharToNat d
  private
    jsonSpace : Char → Bool
    jsonSpace c = let n = primCharToNat c in (n ≡ᵇ 32) ∨ ((n ≡ᵇ 9) ∨ ((n ≡ᵇ 13) ∨ (n ≡ᵇ 10)))
  private
    skipSpace : List Char → List Char
    skipSpace [] = []
    skipSpace (c ∷ cs) = if jsonSpace c then skipSpace cs else (c ∷ cs)
  private
    scanWhile : (Char → Bool) → List Char → List Char × List Char
    scanWhile p [] = [] , []
    scanWhile p (c ∷ cs) with p c
    scanWhile p (c ∷ cs) | false = [] , (c ∷ cs)
    scanWhile p (c ∷ cs) | true = let result = scanWhile p cs in (c ∷ proj₁ result) , proj₂ result
  private
    hexDigit : ℕ → Char
    hexDigit n = primNatToChar (if (n <ᵇ 10) then (48 + n) else (87 + n))
  private
    utf8Lead : ℕ → ℕ
    utf8Lead n = if (n <ᵇ 128) then n else (if (n <ᵇ 2048) then (192 + div-helper 0 63 n 63) else (if (n <ᵇ 65536) then (224 + div-helper 0 4095 n 4095) else (240 + div-helper 0 262143 n 262143)))
  private
    diagnosticChar : Char → String
    diagnosticChar c = let n = primCharToNat c; apostrophe = primNatToChar 39; high = div-helper 0 15 n 15 in if (n ≡ᵇ 39) then "'\\''" else (if (n ≡ᵇ 92) then "'\\\\'" else (if (n ≡ᵇ 7) then "'\\a'" else (if (n ≡ᵇ 8) then "'\\b'" else (if (n ≡ᵇ 9) then "'\\t'" else (if (n ≡ᵇ 10) then "'\\n'" else (if (n ≡ᵇ 11) then "'\\v'" else (if (n ≡ᵇ 12) then "'\\f'" else (if (n ≡ᵇ 13) then "'\\r'" else (if ((n <ᵇ 32) ∨ (n ≡ᵇ 127)) then fromList (apostrophe ∷ ('\\' ∷ ('x' ∷ (hexDigit high ∷ (hexDigit (n ∸ (16 * high)) ∷ (apostrophe ∷ [])))))) else fromList (apostrophe ∷ (primNatToChar (utf8Lead n) ∷ (apostrophe ∷ []))))))))))))
  private
    invalid : {A : Set} → String → List Char → String ⊎ A
    invalid context [] = inj₁ "unexpected EOF"
    invalid context (c ∷ _) = inj₁ ("invalid character " ++ (diagnosticChar c ++ (" " ++ context)))
  private
    Parsed : Set → Set
    Parsed A = String ⊎ (A × List Char)
  private
    chain : {A B : Set} → Parsed A → (A → List Char → Parsed B) → Parsed B
    chain (inj₁ reason) next = inj₁ reason
    chain (inj₂ (value , rest)) next = next value rest
  private
    hexValue : Char → Maybe ℕ
    hexValue c = let n = primCharToNat c in if within 48 58 n then just (n ∸ 48) else (if within 65 71 n then just (n ∸ 55) else (if within 97 103 n then just (n ∸ 87) else nothing))
  private
    readHex : ℕ → ℕ → List Char → Parsed ℕ
    readHex zero n cs = inj₂ (n , cs)
    readHex (suc count) n [] = inj₁ "unexpected EOF"
    readHex (suc count) n (c ∷ cs) with hexValue c
    readHex (suc count) n (c ∷ cs) | nothing = invalid "in \\u hexadecimal character escape" (c ∷ cs)
    readHex (suc count) n (c ∷ cs) | (just d) = readHex count ((16 * n) + d) cs
  private
    combineSurrogates : ℕ → List Char → Parsed Char
    combineSurrogates high (cs@('\\' ∷ ('u' ∷ digits))) with readHex 4 0 digits
    combineSurrogates high (cs@('\\' ∷ ('u' ∷ digits))) | (inj₁ _) = inj₂ ('�' , cs)
    combineSurrogates high (cs@('\\' ∷ ('u' ∷ digits))) | (inj₂ (low , rest)) = if within 56320 57344 low then inj₂ (primNatToChar ((65536 + ((high ∸ 55296) * 1024)) + (low ∸ 56320)) , rest) else inj₂ ('�' , cs)
    combineSurrogates high cs = inj₂ ('�' , cs)
  private
    decodeCodePoint : ℕ → List Char → Parsed Char
    decodeCodePoint n cs = if within 55296 56320 n then combineSurrogates n cs else (if within 56320 57344 n then inj₂ ('�' , cs) else inj₂ (primNatToChar n , cs))
  private
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
  private
    stringChars : ℕ → List Char → List Char → Parsed String
    stringChars zero rev cs = inj₁ "unexpected EOF"
    stringChars (suc fuel) rev [] = inj₁ "unexpected EOF"
    stringChars (suc fuel) rev ('\"' ∷ cs) = inj₂ (fromList (reverse rev) , cs)
    stringChars (suc fuel) rev ('\\' ∷ cs) = chain (decodeEscape cs) (λ c rest → stringChars fuel (c ∷ rev) rest)
    stringChars (suc fuel) rev (c ∷ cs) = if (primCharToNat c <ᵇ 32) then invalid "in string literal" (c ∷ cs) else stringChars fuel (c ∷ rev) cs
  private
    needDigits : String → List Char → Parsed (List Char)
    needDigits context [] = invalid context []
    needDigits context (cs@(c ∷ _)) = if digit c then inj₂ (scanWhile digit cs) else invalid context cs
  private
    prefixDigits : List Char → Parsed (List Char) → Parsed (List Char)
    prefixDigits prefix parsed = chain parsed (λ digits rest → inj₂ ((prefix ++ˡ digits) , rest))
  private
    integerPart : List Char → Parsed (List Char)
    integerPart ('0' ∷ cs) = inj₂ (('0' ∷ []) , cs)
    integerPart cs = needDigits "in numeric literal" cs
  private
    fractionPart : List Char → Parsed (List Char)
    fractionPart ('.' ∷ cs) = prefixDigits ('.' ∷ []) (needDigits "after decimal point in numeric literal" cs)
    fractionPart cs = inj₂ ([] , cs)
  private
    signedExponent : Char → List Char → Parsed (List Char)
    signedExponent marker ('+' ∷ cs) = prefixDigits (marker ∷ ('+' ∷ [])) (needDigits "in exponent of numeric literal" cs)
    signedExponent marker ('-' ∷ cs) = prefixDigits (marker ∷ ('-' ∷ [])) (needDigits "in exponent of numeric literal" cs)
    signedExponent marker cs = prefixDigits (marker ∷ []) (needDigits "in exponent of numeric literal" cs)
  private
    exponentPart : List Char → Parsed (List Char)
    exponentPart ('e' ∷ cs) = signedExponent 'e' cs
    exponentPart ('E' ∷ cs) = signedExponent 'E' cs
    exponentPart cs = inj₂ ([] , cs)
  private
    parseNumber : List Char → List Char → Parsed Base.JSON
    parseNumber sign cs = chain (integerPart cs) (λ integer afterInteger → chain (fractionPart afterInteger) (λ fraction afterFraction → chain (exponentPart afterFraction) (λ exponent rest → inj₂ (Base.jNumber (fromList (sign ++ˡ (integer ++ˡ (fraction ++ˡ exponent)))) , rest))))
  private
    readLiteral : String → List Char → List Char → Parsed ⊤
    readLiteral name [] cs = inj₂ (tt , cs)
    readLiteral name (expected ∷ chars) [] = inj₁ "unexpected EOF"
    readLiteral name (expected ∷ chars) (c ∷ cs) = if sameChar expected c then readLiteral name chars cs else invalid ("in literal " ++ (name ++ (" (expecting " ++ (diagnosticChar expected ++ ")")))) (c ∷ cs)
  private
    literalValue : String → String → Base.JSON → List Char → Parsed Base.JSON
    literalValue name suffix value cs = chain (readLiteral name (toList suffix) cs) (λ _ rest → inj₂ (value , rest))
  private
    arrayAfter : ℕ → List Base.JSON → List Char → Parsed Base.JSON
  private
    arrayItems : ℕ → List Base.JSON → List Char → Parsed Base.JSON
  private
    arrayStart : ℕ → List Char → Parsed Base.JSON
  private
    objectAfter : ℕ → List (String × Base.JSON) → List Char → Parsed Base.JSON
  private
    objectColon : ℕ → List (String × Base.JSON) → String → List Char → Parsed Base.JSON
  private
    objectItems : ℕ → List (String × Base.JSON) → List Char → Parsed Base.JSON
  private
    objectStart : ℕ → List Char → Parsed Base.JSON
  private
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
  readDocument text | (cs@(_ ∷ _)) = map (λ reason → reason) proj₁ (jsonValue (suc (length cs)) cs)
  private
    indexDigits : ℕ → List Char → Maybe ℕ
    indexDigits n [] = if (n <ᵇ 9223372036854775808) then just n else nothing
    indexDigits n (c ∷ cs) = if digit c then indexDigits ((10 * n) + (primCharToNat c ∸ 48)) cs else nothing
  private
    indexText : List Char → Maybe ℕ
    indexText [] = nothing
    indexText ('-' ∷ ('0' ∷ [])) = just zero
    indexText cs = indexDigits zero cs
  private
    tupleSegments : List Base.JSON → Maybe (List Base.Segment)
    tupleSegments [] = just []
    tupleSegments ((Base.jString name) ∷ rest) with tupleSegments rest
    tupleSegments ((Base.jString name) ∷ rest) | nothing = nothing
    tupleSegments ((Base.jString name) ∷ rest) | (just segments) = just (Base.key name ∷ segments)
    tupleSegments ((Base.jNumber spelling) ∷ rest) with indexText (toList spelling) | tupleSegments rest
    tupleSegments ((Base.jNumber spelling) ∷ rest) | (just n) | (just segments) = just (Base.index n ∷ segments)
    tupleSegments ((Base.jNumber spelling) ∷ rest) | _ | _ = nothing
    tupleSegments (_ ∷ _) = nothing
  private
    normalizeTupleValue : Base.JSON → Base.JSON
    normalizeTupleValue (Base.jString text) = Base.jString (if primStringEquality text "<>&" then "<&>" else text)
    normalizeTupleValue value = value
  private
    tupleLayout : Base.JSON → String ⊎ Base.Statement
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) with tupleSegments parts
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) | nothing = inj₁ "invalid JSON layout"
    tupleLayout (Base.jArray ((Base.jArray parts) ∷ (value ∷ []))) | (just path) = inj₂ (Base.statement path (normalizeTupleValue value))
    tupleLayout _ = inj₁ "invalid JSON layout"
  private
    finishTuple : Parsed Base.JSON → String ⊎ Base.Statement
    finishTuple (inj₁ reason) = inj₁ (if primStringEquality reason "unexpected EOF" then "unexpected end of JSON input" else reason)
    finishTuple (inj₂ (value , rest)) with skipSpace rest
    finishTuple (inj₂ (value , rest)) | [] = tupleLayout value
    finishTuple (inj₂ (value , rest)) | (cs@(_ ∷ _)) = invalid "after top-level value" cs
  readTuple : String → String ⊎ Base.Statement
  readTuple text = let cs = skipSpace (toList text) in finishTuple (jsonValue (suc (length cs)) cs)
  private
    isDotted : Base.KeyNotation → Bool
    isDotted Base.dotted = true
    isDotted Base.bracketed = false
  private
    pathWord : List Char → List Char × List Char
    pathWord [] = [] , []
    pathWord (cs@(c ∷ _)) = if isDotted (Base.keyNotation (fromList (c ∷ []))) then scanWhile (λ d → isDotted (Base.keyNotation (fromList ('_' ∷ (d ∷ []))))) cs else ([] , cs)
  private
    PathRead : Set
    PathRead = List Char ⊎ (List Base.Segment × List Char)
  private
    closePathBracket : ℕ → List Base.Segment → Base.Segment → List Char → PathRead
  private
    readPathBracket : ℕ → List Base.Segment → List Char → PathRead
  private
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
  private
    fragmentBefore : List Char → List Char → String
    fragmentBefore whole rest = fromList (take (length whole ∸ length rest) whole)
  private
    withoutValue : List Char → List Char → AssignmentRead
    withoutValue whole rest = rejected (fragmentBefore whole rest) "statement has no value"
  private
    assignmentEnd : List Char → List Base.Segment → Base.JSON → List Char → AssignmentRead
    assignmentEnd whole path value (';' ∷ _) = accepted (Base.statement path value)
    assignmentEnd whole path value rest = withoutValue whole rest
  private
    emptyValue : List Char → List Base.Segment → Base.JSON → Char → List Char → AssignmentRead
    emptyValue whole path value closer cs with skipSpace cs
    emptyValue whole path value closer cs | [] = withoutValue whole cs
    emptyValue whole path value closer cs | (c ∷ rest) = if sameChar closer c then assignmentEnd whole path value (skipSpace rest) else withoutValue whole cs
  private
    assignmentValue : List Char → List Base.Segment → List Char → AssignmentRead
    assignmentValue whole path ('{' ∷ cs) = emptyValue whole path (Base.jObject []) '}' cs
    assignmentValue whole path ('[' ∷ cs) = emptyValue whole path (Base.jArray []) ']' cs
    assignmentValue whole path [] = withoutValue whole []
    assignmentValue whole path (cs@(';' ∷ _)) = withoutValue whole cs
    assignmentValue whole path cs with jsonValue (suc (length cs)) cs
    assignmentValue whole path cs | (inj₁ reason) = rejected (fromList whole) reason
    assignmentValue whole path cs | (inj₂ (value , rest)) = assignmentEnd whole path value (skipSpace rest)
  private
    assignmentLine : List Char → List Char → AssignmentRead
    assignmentLine whole [] = skipped
    assignmentLine whole (cs@(_ ∷ _)) with readPathStart (suc (length cs)) cs
    assignmentLine whole (cs@(_ ∷ _)) | (inj₁ rest) = rejected (fragmentBefore whole rest) "invalid statement"
    assignmentLine whole (cs@(_ ∷ _)) | (inj₂ (path , rest)) = assignmentValue whole path (skipSpace rest)
  readAssignment : String → AssignmentRead
  readAssignment text = let cs = toList text in assignmentLine cs (skipSpace cs)
  private
    controlEscape : ℕ → List Char
    controlEscape n = '\\' ∷ ('u' ∷ ('0' ∷ ('0' ∷ ((if (n <ᵇ 16) then '0' else '1') ∷ (hexDigit (if (n <ᵇ 16) then n else (n ∸ 16)) ∷ [])))))
  private
    escapeCharacter : Bool → Char → List Char
    escapeCharacter _ '\"' = toList "\\\""
    escapeCharacter _ '\\' = toList "\\\\"
    escapeCharacter true '&' = toList "\\u0026"
    escapeCharacter true '<' = toList "\\u003c"
    escapeCharacter true '>' = toList "\\u003e"
    escapeCharacter _ c = let n = primCharToNat c in if (n ≡ᵇ 8) then toList "\\b" else (if (n ≡ᵇ 9) then toList "\\t" else (if (n ≡ᵇ 10) then toList "\\n" else (if (n ≡ᵇ 12) then toList "\\f" else (if (n ≡ᵇ 13) then toList "\\r" else (if (n ≡ᵇ 8232) then toList "\\u2028" else (if (n ≡ᵇ 8233) then toList "\\u2029" else (if (n <ᵇ 32) then controlEscape n else (c ∷ []))))))))
  private
    escapeChars : Bool → List Char → List Char
    escapeChars html [] = []
    escapeChars html (c ∷ cs) = escapeCharacter html c ++ˡ escapeChars html cs
  private
    quoteChars : Bool → String → List Char
    quoteChars html text = '\"' ∷ (escapeChars html (toList text) ++ˡ ('\"' ∷ []))
  private
    keyCharacters : Base.KeyNotation → String → List Char
    keyCharacters Base.dotted k = '.' ∷ toList k
    keyCharacters Base.bracketed k = '[' ∷ (quoteChars true k ++ˡ (']' ∷ []))
  renderKey : String → List Char
  renderKey k = keyCharacters (Base.keyNotation k) k
  private
    ansiPrefix : String
    ansiPrefix = fromList (primNatToChar 27 ∷ ('[' ∷ []))
  private
    paint : Base.Style → String → String → String → String
    paint Base.plain start stop text = text
    paint Base.ansi start stop text = ansiPrefix ++ (start ++ ("m" ++ (text ++ (ansiPrefix ++ (stop ++ "m")))))
  private
    punct : Base.Style → String → String
    punct style = paint style "35" "0"
  private
    identifier : Base.Style → String → String
    identifier style = paint style "34;1" "0;22"
  private
    escapeJSONValue : List Char → List Char
    escapeJSONValue [] = []
    escapeJSONValue ('<' ∷ ('&' ∷ ('>' ∷ cs))) = '<' ∷ ('>' ∷ ('&' ∷ escapeJSONValue cs))
    escapeJSONValue (c ∷ cs) = escapeCharacter false c ++ˡ escapeJSONValue cs
  private
    quotedValue : Base.Style → String → String
    quotedValue style text = paint style "32" "0" "\"" ++ (paint style "33" "0" (fromList (escapeJSONValue (toList text))) ++ paint style "32" "0" "\"")
  private
    objectKey : Base.Style → String → String
    objectKey style name = identifier style "\"" ++ (identifier style (fromList (escapeChars false (toList name))) ++ identifier style "\"")
  private
    linePrefix : Bool → String → String
    linePrefix true indent = "\n" ++ indent
    linePrefix false indent = ""
  private
    objectSeparator : Bool → Base.Style → String
    objectSeparator multiline style = paint style "1" "22" ":" ++ (if multiline then " " else "")
  private
    formatArray : Bool → Base.Style → String → String → List Base.JSON → String
  private
    formatObject : Bool → Base.Style → String → String → List (String × Base.JSON) → String
  private
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
  private
    assignmentKey : Base.Style → String → String
    assignmentKey Base.plain name = fromList (renderKey name)
    assignmentKey Base.ansi name with Base.keyNotation name
    assignmentKey Base.ansi name | Base.dotted = "." ++ identifier Base.ansi name
    assignmentKey Base.ansi name | Base.bracketed = punct Base.ansi "[" ++ (paint Base.ansi "33" "0" (fromList (quoteChars true name)) ++ punct Base.ansi "]")
  private
    formatAssignmentPath : Base.Style → List Base.Segment → String
    formatAssignmentPath style [] = ""
    formatAssignmentPath style ((Base.key name) ∷ rest) = assignmentKey style name ++ formatAssignmentPath style rest
    formatAssignmentPath style ((Base.index n) ∷ rest) = punct style "[" ++ (paint style "31" "0" (Nat.show n) ++ (punct style "]" ++ formatAssignmentPath style rest))
  private
    tupleSegment : Base.Style → Base.Segment → String
    tupleSegment style (Base.key name) = paint style "33" "0" (fromList (quoteChars false name))
    tupleSegment style (Base.index n) = paint style "31" "0" (Nat.show n)
  private
    formatTuplePath : Base.Style → String → List Base.Segment → String
    formatTuplePath style separator [] = ""
    formatTuplePath style separator (part ∷ rest) = separator ++ (tupleSegment style part ++ formatTuplePath style "," rest)
  renderStatement : StatementEncoding → Base.Style → Base.Statement → String
  renderStatement assignments style (Base.statement path value) = identifier style "json" ++ (formatAssignmentPath style path ++ (" = " ++ (statementValue style value ++ ";\n")))
  renderStatement tuples style (Base.statement path value) = punct style "[" ++ (punct style "[" ++ (formatTuplePath style "" path ++ (punct style "]" ++ ("," ++ (statementValue style value ++ (punct style "]" ++ "\n"))))))
  renderJSON : Base.Style → Base.JSON → String
  renderJSON Base.plain value = formatValue true Base.plain "" value ++ "\n"
  renderJSON Base.ansi value = formatValue false Base.ansi "" value ++ "\n"
  keySquare : Commutes₁ (keepPort String) keyPort (λ _ → ⊤) _≡_ Base.keyNotation renderKey
  keySquare k _ with Base.keyNotation k
  keySquare k _ | Base.dotted = refl
  keySquare k _ | Base.bracketed = refl
  dottedKeyText : (k : _) → (Base.keyNotation k ≡ Base.dotted) → renderKey k ≡ ('.' ∷ toList k)
  dottedKeyText k eq rewrite eq = refl
  reservedKeyText : fromList (renderKey "class") ≡ "[\"class\"]"
  reservedKeyText = refl
  bracketKeyText : fromList (renderKey "a\"b\\c\n") ≡ "[\"a\\\"b\\\\c\\n\"]"
  bracketKeyText = refl
  firstDocument : readDocument "1 2" ≡ inj₂ (Base.jNumber "1")
  firstDocument = refl
  numericSpellings : readDocument "[1.0,1e+02,-0,9007199254740993,1e-09,1e-7,1e20]" ≡ inj₂ (Base.jArray (Base.jNumber "1.0" ∷ (Base.jNumber "1e+02" ∷ (Base.jNumber "-0" ∷ (Base.jNumber "9007199254740993" ∷ (Base.jNumber "1e-09" ∷ (Base.jNumber "1e-7" ∷ (Base.jNumber "1e20" ∷ []))))))))
  numericSpellings = refl
  stringEscapes : map (λ reason → reason) (λ value → renderStatement assignments Base.plain (Base.statement [] value)) (readDocument "\"<>&\\u2028\\u2029\\ud800\"") ≡ inj₂ "json = \"<>&\\u2028\\u2029�\";\n"
  stringEscapes = refl
  duplicateDocument : map (λ reason → reason) (Base.flatten Base.sortPaths) (readDocument "{\"a\":{\"x\":1},\"a\":{\"y\":2},\"b\":1,\"b\":2}") ≡ inj₂ (Base.statement [] (Base.jObject []) ∷ (Base.statement (Base.key "a" ∷ []) (Base.jObject []) ∷ (Base.statement (Base.key "a" ∷ (Base.key "y" ∷ [])) (Base.jNumber "2") ∷ (Base.statement (Base.key "b" ∷ []) (Base.jNumber "2") ∷ []))))
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
  missingSemicolon : readAssignment "json.a = 1" ≡ rejected "json.a = 1" "statement has no value"
  missingSemicolon = refl
  leadingComment : readAssignment "// comment" ≡ rejected "" "invalid statement"
  leadingComment = refl
  singleQuotedKey : readAssignment "json['a'] = 2;" ≡ rejected "json[" "invalid statement"
  singleQuotedKey = refl
  inlineObject : readAssignment "json.a = {\"x\":2};" ≡ rejected "json.a = {" "statement has no value"
  inlineObject = refl
  tupleRoot : readTuple "[[],{}]" ≡ inj₂ (Base.statement [] (Base.jObject []))
  tupleRoot = refl
  tuplePath : readTuple "[[\"a\",2],\"<>&\"]" ≡ inj₂ (Base.statement (Base.key "a" ∷ (Base.index 2 ∷ [])) (Base.jString "<&>"))
  tuplePath = refl
  tuplePathType : readTuple "[[true],1]" ≡ inj₁ "invalid JSON layout"
  tuplePathType = refl
  tupleArity : readTuple "[[\"a\"],1,2]" ≡ inj₁ "invalid JSON layout"
  tupleArity = refl
  blankTuple : readTuple "" ≡ inj₁ "unexpected end of JSON input"
  blankTuple = refl
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
  coloredJSON : renderJSON Base.ansi (Base.jObject (("a" , Base.jNumber "9007199254740993") ∷ (("b" , Base.jNumber "1e+02") ∷ (("c" , Base.jNumber "-0") ∷ (("d" , Base.jString (fromList (primNatToChar 8232 ∷ (primNatToChar 8233 ∷ ('<' ∷ ('&' ∷ ('>' ∷ (primNatToChar 0 ∷ [])))))))) ∷ []))))) ≡ "[35m{[0m[34;1m\"[0;22m[34;1ma[0;22m[34;1m\"[0;22m[1m:[22m[31m9007199254740993[0m[1m,[22m[34;1m\"[0;22m[34;1mb[0;22m[34;1m\"[0;22m[1m:[22m[31m1e+02[0m[1m,[22m[34;1m\"[0;22m[34;1mc[0;22m[34;1m\"[0;22m[1m:[22m[31m-0[0m[1m,[22m[34;1m\"[0;22m[34;1md[0;22m[34;1m\"[0;22m[1m:[22m[32m\"[0m[33m\\u2028\\u2029<>&\\u0000[0m[32m\"[0m[35m}[0m\n"
  coloredJSON = refl
