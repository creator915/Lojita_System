module Gen.T1.JSON where

open import Agda.Builtin.Char using (Char; primCharEquality; primCharToNat; primNatToChar)
open import Agda.Builtin.Nat using () renaming (_<_ to _<ᵇ_)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; reverse; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Context.Blueprint using (PortLift; portLift)
import Gen.T0.Gron as G

data Atom : Set where
  null : Atom
  boolean : Bool → Atom
  number : String → Atom
  text : String → Atom

data JSON : Set where
  literal : Atom → JSON
  object : List (String × JSON) → JSON
  array : List JSON → JSON

data Result (A : Set) : Set where
  good : A → Result A
  bad : String → Result A

infixl 1 _>>=ʳ_

_>>=ʳ_ : {A B : Set} → Result A → (A → Result B) → Result B
good x >>=ʳ next = next x
bad err >>=ʳ _ = bad err

Chars : Set
Chars = List Char

Parsed : Set → Set
Parsed A = Result (A × Chars)

within : ℕ → ℕ → ℕ → Bool
within low high n = not (n <ᵇ low) ∧ not (high <ᵇ n)

asciiDigit : Char → Bool
asciiDigit c = within 48 57 (primCharToNat c)

skipJSONSpace : Chars → Chars
skipJSONSpace (' ' ∷ cs) = skipJSONSpace cs
skipJSONSpace ('\t' ∷ cs) = skipJSONSpace cs
skipJSONSpace ('\r' ∷ cs) = skipJSONSpace cs
skipJSONSpace ('\n' ∷ cs) = skipJSONSpace cs
skipJSONSpace cs = cs

hexDigit : ℕ → Char
hexDigit n = primNatToChar (if n <ᵇ 10 then 48 + n else 87 + n)

firstUTF8Byte : ℕ → ℕ
firstUTF8Byte n =
  if n <ᵇ 128 then n else
  if n <ᵇ 2048 then 192 + (n / 64) else
  if n <ᵇ 65536 then 224 + (n / 4096) else
  240 + (n / 262144)

diagnosticByte : ℕ → Chars
diagnosticByte 7 = toList "\\a"
diagnosticByte 8 = toList "\\b"
diagnosticByte 9 = toList "\\t"
diagnosticByte 10 = toList "\\n"
diagnosticByte 11 = toList "\\v"
diagnosticByte 12 = toList "\\f"
diagnosticByte 13 = toList "\\r"
diagnosticByte 39 = toList "\\'"
diagnosticByte 92 = toList "\\\\"
diagnosticByte n =
  if (n <ᵇ 32) ∨ within 127 160 n
  then '\\' ∷ 'x' ∷ hexDigit (n / 16) ∷ hexDigit (n % 16) ∷ []
  else primNatToChar n ∷ []

quoteBadChar : Char → String
quoteBadChar c =
  fromList (apostrophe ∷
    (diagnosticByte (firstUTF8Byte (primCharToNat c)) ++ (apostrophe ∷ [])))
  where
    apostrophe : Char
    apostrophe = primNatToChar 39

invalid : Char → String → String
invalid c context = "invalid character " ++ˢ quoteBadChar c ++ˢ " " ++ˢ context

escapeJSONChar : Char → Chars
escapeJSONChar '"' = toList "\\\""
escapeJSONChar '\\' = toList "\\\\"
escapeJSONChar '\n' = toList "\\n"
escapeJSONChar '\r' = toList "\\r"
escapeJSONChar '\t' = toList "\\t"
escapeJSONChar c with primCharToNat c
... | 8 = toList "\\b"
... | 12 = toList "\\f"
... | 8232 = toList "\\u2028"
... | 8233 = toList "\\u2029"
... | n =
  if n <ᵇ 32
  then '\\' ∷ 'u' ∷ '0' ∷ '0' ∷ hexDigit (n / 16) ∷ hexDigit (n % 16) ∷ []
  else c ∷ []

quoteJSON : String → String
quoteJSON s =
  fromList ('"' ∷ (concatMap escapeJSONChar (toList s) ++ ('"' ∷ [])))

atomJSON : Atom → String
atomJSON null = "null"
atomJSON (boolean true) = "true"
atomJSON (boolean false) = "false"
atomJSON (number spelling) = spelling
atomJSON (text s) = quoteJSON s

hexValue : Char → Maybe ℕ
hexValue c with primCharToNat c
... | n =
  if within 48 57 n then just (n ∸ 48) else
  if within 65 70 n then just (n ∸ 55) else
  if within 97 102 n then just (n ∸ 87) else nothing

readHex : ℕ → ℕ → Chars → Parsed ℕ
readHex zero n cs = good (n , cs)
readHex (suc k) n [] = bad "unexpected EOF"
readHex (suc k) n (c ∷ cs) with hexValue c
... | nothing = bad (invalid c "in \\u hexadecimal character escape")
... | just d = readHex k (16 * n + d) cs

replacement : Char
replacement = primNatToChar 65533

surrogateTail : ℕ → Chars → Char × Chars
surrogateTail high ('\\' ∷ 'u' ∷ cs) with readHex 4 0 cs
... | bad _ = replacement , ('\\' ∷ 'u' ∷ cs)
... | good (low , rest) =
  if within 56320 57343 low
  then primNatToChar (65536 + 1024 * (high ∸ 55296) + (low ∸ 56320)) , rest
  else replacement , ('\\' ∷ 'u' ∷ cs)
surrogateTail high cs = replacement , cs

unicodeChar : ℕ → Chars → Char × Chars
unicodeChar n cs =
  if within 55296 56319 n then surrogateTail n cs else
  if within 56320 57343 n then replacement , cs else
  primNatToChar n , cs

escapeRune : Chars → Parsed Char
escapeRune [] = bad "unexpected EOF"
escapeRune ('"' ∷ cs) = good ('"' , cs)
escapeRune ('\\' ∷ cs) = good ('\\' , cs)
escapeRune ('/' ∷ cs) = good ('/' , cs)
escapeRune ('b' ∷ cs) = good (primNatToChar 8 , cs)
escapeRune ('f' ∷ cs) = good (primNatToChar 12 , cs)
escapeRune ('t' ∷ cs) = good ('\t' , cs)
escapeRune ('r' ∷ cs) = good ('\r' , cs)
escapeRune ('n' ∷ cs) = good ('\n' , cs)
escapeRune ('u' ∷ cs) = readHex 4 0 cs >>=ʳ λ where
  (n , rest) → good (unicodeChar n rest)
escapeRune (c ∷ cs) = bad (invalid c "in string escape code")

stringChars : ℕ → Chars → Chars → Parsed String
stringChars zero acc cs = bad "unexpected EOF"
stringChars (suc fuel) acc [] = bad "unexpected EOF"
stringChars (suc fuel) acc ('"' ∷ cs) = good (fromList (reverse acc) , cs)
stringChars (suc fuel) acc ('\\' ∷ cs) = escapeRune cs >>=ʳ λ where
  (c , rest) → stringChars fuel (c ∷ acc) rest
stringChars (suc fuel) acc (c ∷ cs) =
  if primCharToNat c <ᵇ 32 then bad (invalid c "in string literal")
  else stringChars fuel (c ∷ acc) cs

afterQuote : Chars → Parsed String
afterQuote cs = stringChars (suc (length cs)) [] cs

takeDigits : Chars → Chars × Chars
takeDigits [] = [] , []
takeDigits (c ∷ cs) with asciiDigit c
... | false = [] , (c ∷ cs)
... | true with takeDigits cs
...   | digits , rest = (c ∷ digits) , rest

needDigits : String → Chars → Parsed Chars
needDigits context [] = bad "unexpected EOF"
needDigits context (c ∷ cs) =
  if asciiDigit c then good (takeDigits (c ∷ cs)) else bad (invalid c context)

finishExponent : Chars → Chars → Parsed String
finishExponent prefix cs = needDigits "in exponent of numeric literal" cs >>=ʳ λ where
  (digits , rest) → good (fromList (prefix ++ digits) , rest)

exponentSign : Chars → Chars → Parsed String
exponentSign prefix ('+' ∷ cs) = finishExponent (prefix ++ ('+' ∷ [])) cs
exponentSign prefix ('-' ∷ cs) = finishExponent (prefix ++ ('-' ∷ [])) cs
exponentSign prefix cs = finishExponent prefix cs

exponentTail : Chars → Chars → Parsed String
exponentTail prefix ('e' ∷ cs) = exponentSign (prefix ++ ('e' ∷ [])) cs
exponentTail prefix ('E' ∷ cs) = exponentSign (prefix ++ ('E' ∷ [])) cs
exponentTail prefix cs = good (fromList prefix , cs)

fractionTail : Chars → Chars → Parsed String
fractionTail prefix ('.' ∷ cs) =
  needDigits "after decimal point in numeric literal" cs >>=ʳ λ where
    (digits , rest) → exponentTail (prefix ++ ('.' ∷ digits)) rest
fractionTail prefix cs = exponentTail prefix cs

numberStart : Chars → Chars → Parsed String
numberStart sign ('0' ∷ cs) = fractionTail (sign ++ ('0' ∷ [])) cs
numberStart sign cs = needDigits "in numeric literal" cs >>=ʳ λ where
  (digits , rest) → fractionTail (sign ++ digits) rest

numberValue : Chars → Chars → Parsed JSON
numberValue sign cs = numberStart sign cs >>=ʳ λ where
  (spelling , rest) → good (literal (number spelling) , rest)

literalTail : String → Chars → Chars → Result Chars
literalTail name [] cs = good cs
literalTail name (wanted ∷ suffix) [] = bad "unexpected EOF"
literalTail name (wanted ∷ suffix) (c ∷ cs) =
  if primCharEquality c wanted then literalTail name suffix cs
  else bad (invalid c ("in literal " ++ˢ name ++ˢ
                     " (expecting " ++ˢ quoteBadChar wanted ++ˢ ")"))

keyword : String → Chars → Atom → Chars → Parsed JSON
keyword name suffix atom cs = literalTail name suffix cs >>=ʳ λ rest →
  good (literal atom , rest)

putField : {A : Set} → String → A → List (String × A) → List (String × A)
putField key val [] = (key , val) ∷ []
putField key val ((k , v) ∷ rest) =
  if primStringEquality key k then (key , val) ∷ rest
  else (k , v) ∷ putField key val rest

afterColon : Chars → Result Chars
afterColon [] = bad "unexpected EOF"
afterColon (':' ∷ cs) = good (skipJSONSpace cs)
afterColon (c ∷ cs) = bad (invalid c "after object key")

mutual
  parseAt : ℕ → Chars → Parsed JSON
  parseAt zero cs = bad "unexpected EOF"
  parseAt (suc fuel) [] = bad "unexpected EOF"
  parseAt (suc fuel) ('{' ∷ cs) = case skipJSONSpace cs of λ where
    ('}' ∷ rest) → good (object [] , rest)
    rest → objectAt fuel [] rest
  parseAt (suc fuel) ('[' ∷ cs) = case skipJSONSpace cs of λ where
    (']' ∷ rest) → good (array [] , rest)
    rest → arrayAt fuel [] rest
  parseAt (suc fuel) ('"' ∷ cs) = stringChars (suc fuel) [] cs >>=ʳ λ where
    (s , rest) → good (literal (text s) , rest)
  parseAt (suc fuel) ('n' ∷ cs) = keyword "null" (toList "ull") null cs
  parseAt (suc fuel) ('t' ∷ cs) = keyword "true" (toList "rue") (boolean true) cs
  parseAt (suc fuel) ('f' ∷ cs) = keyword "false" (toList "alse") (boolean false) cs
  parseAt (suc fuel) ('-' ∷ cs) = numberValue ('-' ∷ []) cs
  parseAt (suc fuel) (c ∷ cs) =
    if asciiDigit c then numberValue [] (c ∷ cs)
    else bad (invalid c "looking for beginning of value")

  objectAt : ℕ → List (String × JSON) → Chars → Parsed JSON
  objectAt zero fields cs = bad "unexpected EOF"
  objectAt (suc fuel) fields [] = bad "unexpected EOF"
  objectAt (suc fuel) fields ('"' ∷ cs) =
    stringChars (suc fuel) [] cs >>=ʳ λ where
      (key , rest) → afterColon (skipJSONSpace rest) >>=ʳ λ start →
        parseAt fuel start >>=ʳ λ where
          (value , tail) → case skipJSONSpace tail of λ where
            [] → bad "unexpected EOF"
            ('}' ∷ next) → good (object (putField key value fields) , next)
            (',' ∷ next) → objectAt fuel (putField key value fields) (skipJSONSpace next)
            (c ∷ next) → bad (invalid c "after object key:value pair")
  objectAt (suc fuel) fields (c ∷ cs) =
    bad (invalid c "looking for beginning of object key string")

  arrayAt : ℕ → List JSON → Chars → Parsed JSON
  arrayAt zero items cs = bad "unexpected EOF"
  arrayAt (suc fuel) items cs = parseAt fuel cs >>=ʳ λ where
    (value , tail) → case skipJSONSpace tail of λ where
      [] → bad "unexpected EOF"
      (']' ∷ next) → good (array (reverse (value ∷ items)) , next)
      (',' ∷ next) → arrayAt fuel (value ∷ items) (skipJSONSpace next)
      (c ∷ next) → bad (invalid c "after array element")

parsePrefix : String → Parsed JSON
parsePrefix s with skipJSONSpace (toList s)
... | [] = bad "EOF"
... | c ∷ cs = parseAt (suc (2 * length (c ∷ cs))) (c ∷ cs)

decodePrefix : String → Result JSON
decodePrefix s = parsePrefix s >>=ʳ λ where
  (value , rest) → good value

decodeWhole : String → Result JSON
decodeWhole s = parsePrefix s >>=ʳ λ where
  (value , rest) → case skipJSONSpace rest of λ where
    [] → good value
    (c ∷ cs) → bad (invalid c "after top-level value")

linesOf : String → List String
linesOf s = map fromList (split [] (toList s))
  where
    finishLine : Chars → Chars
    finishLine ('\r' ∷ cs) = reverse cs
    finishLine cs = reverse cs

    split : Chars → Chars → List Chars
    split [] [] = []
    split rev [] = finishLine rev ∷ []
    split rev ('\n' ∷ cs) = finishLine rev ∷ split [] cs
    split rev (c ∷ cs) = split (c ∷ rev) cs

mutual
  lower : (String → G.Key) → JSON → G.Tree Atom
  lower classify (literal a) = G.leaf a
  lower classify (object fields) = G.object (lowerFields classify fields)
  lower classify (array items) = G.array (lowerItems classify items)

  lowerFields : (String → G.Key) → List (String × JSON) → List (G.Key × G.Tree Atom)
  lowerFields classify [] = []
  lowerFields classify ((key , value) ∷ rest) =
    (classify key , lower classify value) ∷ lowerFields classify rest

  lowerItems : (String → G.Key) → List JSON → List (G.Tree Atom)
  lowerItems classify [] = []
  lowerItems classify (value ∷ rest) = lower classify value ∷ lowerItems classify rest

treePort : (String → G.Key) → PortLift (G.Tree Atom) JSON
treePort classify = portLift (lower classify)

postulate
  flattenWith : (String → G.Key) → G.SiblingOrder → G.Path → JSON → List (G.Statement Atom)

  flattenLaw : ∀ classify order path value →
    flattenWith classify order path value ≡ G.emitAt order path (lower classify value)

  preservesNumberSpellings :
    decodeWhole "[-0,1.0,1e+03,9007199254740993,1e400]" ≡
    good (array (literal (number "-0") ∷ literal (number "1.0") ∷
                 literal (number "1e+03") ∷ literal (number "9007199254740993") ∷
                 literal (number "1e400") ∷ []))

  lastDuplicateWins :
    decodeWhole "{\"z\":1,\"z\":3}" ≡
    good (object (("z" , literal (number "3")) ∷ []))

  surrogateReplacementAndPair :
    decodeWhole "\"\\ud800\\ud83d\\ude00\"" ≡ good (literal (text "�😀"))

  literalEscaping :
    quoteJSON (fromList ('<' ∷ '&' ∷ '>' ∷ primNatToChar 8232 ∷
                         primNatToChar 8233 ∷ primNatToChar 0 ∷ [])) ≡
    "\"<&>\\u2028\\u2029\\u0000\""

  prefixAcceptsTrailingBytes :
    decodePrefix "true trailing" ≡ good (literal (boolean true))

  wholeRejectsSecondRecord :
    decodeWhole "[[],{}][[],[]]" ≡ bad "invalid character '[' after top-level value"

  truncatedObject :
    decodePrefix "{\"x\":" ≡ bad "unexpected EOF"

  missingObjectComma :
    decodePrefix "{\"x\":1 \"y\":2}" ≡
    bad "invalid character '\"' after object key:value pair"

  lineBoundaries :
    linesOf "1\r\n\n2\n" ≡ ("1" ∷ "" ∷ "2" ∷ [])
