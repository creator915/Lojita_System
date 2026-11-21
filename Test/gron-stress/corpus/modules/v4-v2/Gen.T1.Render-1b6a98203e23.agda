module Gen.T1.Render where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Char using (Char; toℕ; fromℕ; isAlpha)
open import Data.List using (List; []; _∷_; _++_; all; any)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _<ᵇ_; _≤_; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Data.String.Properties using (_≟_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
import Gen.T0.Gron as Gron
open Gron using (Atom; null; truth; numeral; text; Cell; leaf; objectCell; arrayCell;
  Segment; key; index; Row; row; Value; scalar; object; array)

data Style : Set where
  plain ansi : Style

data Notation : Set where
  statements jsonRows : Notation

data StringForm : Set where
  rowForm documentForm : StringForm

data Tone : Set where
  purple red yellow cyan blue green bold : Tone

data LexOrder : Set where
  earlier equal later : LexOrder

colorBit : Style → Bool
colorBit plain = false
colorBit ansi = true

postulate
  terminalStyle : Bool → Bool → Bool → Style
  terminal-square : ∀ tty force mono →
    colorBit (terminalStyle tty force mono) ≡ Gron.useColor tty force mono

  paint : Style → Tone → List Char → List Char
  paint-plain : ∀ tone cs → paint plain tone cs ≡ cs
  paint-purple : ∀ cs → paint ansi purple cs ≡
    (fromℕ 27 ∷ toList "[35m") ++ cs ++ (fromℕ 27 ∷ toList "[0m")
  paint-red : ∀ cs → paint ansi red cs ≡
    (fromℕ 27 ∷ toList "[31m") ++ cs ++ (fromℕ 27 ∷ toList "[0m")
  paint-yellow : ∀ cs → paint ansi yellow cs ≡
    (fromℕ 27 ∷ toList "[33m") ++ cs ++ (fromℕ 27 ∷ toList "[0m")
  paint-cyan : ∀ cs → paint ansi cyan cs ≡
    (fromℕ 27 ∷ toList "[36m") ++ cs ++ (fromℕ 27 ∷ toList "[0m")
  paint-blue : ∀ cs → paint ansi blue cs ≡
    (fromℕ 27 ∷ toList "[34;1m") ++ cs ++ (fromℕ 27 ∷ toList "[0;22m")
  paint-green : ∀ cs → paint ansi green cs ≡
    (fromℕ 27 ∷ toList "[32m") ++ cs ++ (fromℕ 27 ∷ toList "[0m")
  paint-bold : ∀ cs → paint ansi bold cs ≡
    (fromℕ 27 ∷ toList "[1m") ++ cs ++ (fromℕ 27 ∷ toList "[22m")

  hexGlyph : StringForm → ℕ → Char
  unicodeEscape : StringForm → ℕ → List Char
  escapeGlyph : StringForm → Char → List Char
  stringBody : StringForm → List Char → List Char
  quotedString : StringForm → String → List Char

  hex-decimal : ∀ f n → n < 10 → hexGlyph f n ≡ fromℕ (48 + n)
  hex-uppercase : ∀ n → 10 ≤ n → n < 16 → hexGlyph rowForm n ≡ fromℕ (55 + n)
  hex-lowercase : ∀ n → 10 ≤ n → n < 16 → hexGlyph documentForm n ≡ fromℕ (87 + n)
  unicode-four : ∀ f n → n < 65536 →
    unicodeEscape f n ≡
      ('\\' ∷ 'u' ∷ hexGlyph f ((n / 4096) % 16) ∷ hexGlyph f ((n / 256) % 16) ∷
       hexGlyph f ((n / 16) % 16) ∷ hexGlyph f (n % 16) ∷ [])
  escape-quote : ∀ f → escapeGlyph f '"' ≡ toList "\\\""
  escape-slash : ∀ f → escapeGlyph f '\\' ≡ toList "\\\\"
  escape-backspace : ∀ f → escapeGlyph f (fromℕ 8) ≡ toList "\\b"
  escape-tab : ∀ f → escapeGlyph f (fromℕ 9) ≡ toList "\\t"
  escape-newline : ∀ f → escapeGlyph f (fromℕ 10) ≡ toList "\\n"
  escape-form-feed : ∀ f → escapeGlyph f (fromℕ 12) ≡ toList "\\f"
  escape-return : ∀ f → escapeGlyph f (fromℕ 13) ≡ toList "\\r"
  escape-control : ∀ f c → toℕ c < 32 →
    toℕ c ≢ 8 → toℕ c ≢ 9 → toℕ c ≢ 10 → toℕ c ≢ 12 → toℕ c ≢ 13 →
    escapeGlyph f c ≡ unicodeEscape f (toℕ c)
  escape-line-separator : ∀ f → escapeGlyph f (fromℕ 8232) ≡ unicodeEscape f 8232
  escape-paragraph-separator : ∀ f → escapeGlyph f (fromℕ 8233) ≡ unicodeEscape f 8233
  escape-row-control : ∀ c → 127 ≤ toℕ c → toℕ c ≤ 159 →
    escapeGlyph rowForm c ≡ unicodeEscape rowForm (toℕ c)
  escape-row-ascii : ∀ c → 32 ≤ toℕ c → toℕ c < 127 → toℕ c ≢ 34 → toℕ c ≢ 92 →
    escapeGlyph rowForm c ≡ (c ∷ [])
  escape-row-unicode : ∀ c → 159 < toℕ c → toℕ c ≢ 8232 → toℕ c ≢ 8233 →
    escapeGlyph rowForm c ≡ (c ∷ [])
  escape-document-normal : ∀ c → 32 ≤ toℕ c →
    toℕ c ≢ 34 → toℕ c ≢ 92 → toℕ c ≢ 8232 → toℕ c ≢ 8233 →
    escapeGlyph documentForm c ≡ (c ∷ [])
  string-empty : ∀ f → stringBody f [] ≡ []
  string-next : ∀ f c cs → stringBody f (c ∷ cs) ≡ escapeGlyph f c ++ stringBody f cs
  quoted : ∀ f s → quotedString f s ≡ ('"' ∷ stringBody f (toList s) ++ ('"' ∷ []))

  -- 首字符接受字母与字母数字，后续还接受非间距标记、间距标记、十进制数字和连接标点。
  nameStart : Char → Bool
  nameRest : Char → Bool
  identifier : List Char → Bool
  reserved : String → Bool
  dotted : String → Bool

  ascii-start : ∀ c → (toℕ c <ᵇ 128) ≡ true →
    nameStart c ≡ ((toℕ c ≡ᵇ 36) ∨ (toℕ c ≡ᵇ 95) ∨
      ((65 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 90)) ∨ ((97 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 122)))
  ascii-rest : ∀ c → (toℕ c <ᵇ 128) ≡ true →
    nameRest c ≡ (nameStart c ∨ ((48 ≤ᵇ toℕ c) ∧ (toℕ c ≤ᵇ 57)))
  letter-start : ∀ c → (toℕ c <ᵇ 128) ≡ false → isAlpha c ≡ true → nameStart c ≡ true
  start-is-rest : ∀ c → nameStart c ≡ true → nameRest c ≡ true
  observed-letter-number : nameStart (fromℕ 8551) ≡ true
  observed-non-bmp-letter : nameStart (fromℕ 66560) ≡ true
  observed-decimal-start : nameStart (fromℕ 1634) ≡ false
  observed-decimal-rest : nameRest (fromℕ 1634) ≡ true
  observed-nonspacing-mark : nameRest (fromℕ 769) ≡ true
  observed-spacing-mark : nameRest (fromℕ 2307) ≡ true
  observed-connector : nameRest (fromℕ 8255) ≡ true
  observed-enclosing-mark : nameRest (fromℕ 1160) ≡ false
  observed-other-number : nameRest (fromℕ 178) ≡ false
  observed-middle-dot : nameRest (fromℕ 183) ≡ false
  observed-joiner : nameRest (fromℕ 8205) ≡ false
  observed-non-joiner : nameRest (fromℕ 8204) ≡ false
  identifier-empty : identifier [] ≡ false
  identifier-next : ∀ c cs → identifier (c ∷ cs) ≡ (nameStart c ∧ all nameRest cs)
  reserved-rule : ∀ k → reserved k ≡ any (λ word → does (k ≟ word))
    ("break" ∷ "case" ∷ "catch" ∷ "class" ∷ "const" ∷ "continue" ∷ "debugger" ∷
     "default" ∷ "delete" ∷ "do" ∷ "else" ∷ "export" ∷ "extends" ∷ "false" ∷
     "finally" ∷ "for" ∷ "function" ∷ "if" ∷ "import" ∷ "in" ∷ "instanceof" ∷
     "new" ∷ "null" ∷ "return" ∷ "super" ∷ "switch" ∷ "this" ∷ "throw" ∷
     "true" ∷ "try" ∷ "typeof" ∷ "var" ∷ "void" ∷ "while" ∷ "with" ∷ "yield" ∷ [])
  dotted-rule : ∀ k → dotted k ≡ (identifier (toList k) ∧ not (reserved k))

  segmentText : Style → Segment → List Char
  pathText : Style → List Segment → List Char
  jsonSegmentText : Style → Segment → List Char
  jsonPathItems : Style → List Segment → List Char
  atomText : StringForm → Style → Atom → List Char
  cellText : Style → Cell → List Char
  rowText : Notation → Style → Row → List Char
  rowsText : Notation → Style → List Row → List Char

  segment-dotted : ∀ s k → dotted k ≡ true →
    segmentText s (key k) ≡ '.' ∷ paint s blue (toList k)
  segment-quoted : ∀ s k → dotted k ≡ false →
    segmentText s (key k) ≡
      paint s purple (toList "[") ++ paint s yellow (quotedString rowForm k) ++ paint s purple (toList "]")
  segment-index : ∀ s i → segmentText s (index i) ≡
    paint s purple (toList "[") ++ paint s red (toList (show i)) ++ paint s purple (toList "]")
  path-empty : ∀ s → pathText s [] ≡ []
  path-next : ∀ s x xs → pathText s (x ∷ xs) ≡ segmentText s x ++ pathText s xs
  json-segment-key : ∀ s k → jsonSegmentText s (key k) ≡ paint s yellow (quotedString rowForm k)
  json-segment-index : ∀ s i → jsonSegmentText s (index i) ≡ paint s red (toList (show i))
  json-path-empty : ∀ s → jsonPathItems s [] ≡ []
  json-path-single : ∀ s x → jsonPathItems s (x ∷ []) ≡ jsonSegmentText s x
  json-path-next : ∀ s x y xs → jsonPathItems s (x ∷ y ∷ xs) ≡
    jsonSegmentText s x ++ (',' ∷ jsonPathItems s (y ∷ xs))

  atom-null : ∀ f s → atomText f s null ≡ paint s cyan (toList "null")
  atom-true : ∀ f s → atomText f s (truth true) ≡ paint s cyan (toList "true")
  atom-false : ∀ f s → atomText f s (truth false) ≡ paint s cyan (toList "false")
  atom-number : ∀ f s n → atomText f s (numeral n) ≡ paint s red (toList n)
  atom-row-string : ∀ s v → atomText rowForm s (text v) ≡ paint s yellow (quotedString rowForm v)
  atom-doc-string : ∀ v → atomText documentForm plain (text v) ≡ quotedString documentForm v
  atom-doc-ansi-string : ∀ v → atomText documentForm ansi (text v) ≡
    paint ansi green ('"' ∷ []) ++ paint ansi yellow (stringBody documentForm (toList v)) ++
    paint ansi green ('"' ∷ [])
  cell-leaf : ∀ s a → cellText s (leaf a) ≡ atomText rowForm s a
  cell-object : ∀ s → cellText s objectCell ≡ paint s purple (toList "{}")
  cell-array : ∀ s → cellText s arrayCell ≡ paint s purple (toList "[]")
  row-statement : ∀ s p c → rowText statements s (row p c) ≡
    paint s blue (toList "json") ++ pathText s p ++ toList " = " ++ cellText s c ++ toList ";\n"
  row-json : ∀ s p c → rowText jsonRows s (row p c) ≡
    paint s purple (toList "[") ++ paint s purple (toList "[") ++ jsonPathItems s p ++
    paint s purple (toList "]") ++ toList "," ++ cellText s c ++ paint s purple (toList "]") ++ toList "\n"
  rows-empty : ∀ n s → rowsText n s [] ≡ []
  rows-next : ∀ n s r rs → rowsText n s (r ∷ rs) ≡ rowText n s r ++ rowsText n s rs

  numberOrder : ℕ → ℕ → LexOrder
  charsOrder : List Char → List Char → LexOrder
  segmentOrder : Segment → Segment → LexOrder
  pathOrder : List Segment → List Segment → LexOrder
  placeRow : Row → List Row → List Row
  sortedRows : List Row → List Row

  number-before : ∀ a b → a < b → numberOrder a b ≡ earlier
  number-equal : ∀ a → numberOrder a a ≡ equal
  number-after : ∀ a b → b < a → numberOrder a b ≡ later
  chars-equal-empty : charsOrder [] [] ≡ equal
  chars-empty-before : ∀ c cs → charsOrder [] (c ∷ cs) ≡ earlier
  chars-empty-after : ∀ c cs → charsOrder (c ∷ cs) [] ≡ later
  chars-head-before : ∀ a b cs ds → numberOrder (toℕ a) (toℕ b) ≡ earlier →
    charsOrder (a ∷ cs) (b ∷ ds) ≡ earlier
  chars-head-after : ∀ a b cs ds → numberOrder (toℕ a) (toℕ b) ≡ later →
    charsOrder (a ∷ cs) (b ∷ ds) ≡ later
  chars-head-equal : ∀ a b cs ds → numberOrder (toℕ a) (toℕ b) ≡ equal →
    charsOrder (a ∷ cs) (b ∷ ds) ≡ charsOrder cs ds
  keys-compare : ∀ a b → segmentOrder (key a) (key b) ≡
    charsOrder (segmentText plain (key a)) (segmentText plain (key b))
  indices-compare : ∀ a b → segmentOrder (index a) (index b) ≡ numberOrder a b
  path-equal-empty : pathOrder [] [] ≡ equal
  path-empty-before : ∀ a p → pathOrder [] (a ∷ p) ≡ earlier
  path-empty-after : ∀ a p → pathOrder (a ∷ p) [] ≡ later
  path-head-before : ∀ a b p q → segmentOrder a b ≡ earlier → pathOrder (a ∷ p) (b ∷ q) ≡ earlier
  path-head-after : ∀ a b p q → segmentOrder a b ≡ later → pathOrder (a ∷ p) (b ∷ q) ≡ later
  path-head-equal : ∀ a b p q → segmentOrder a b ≡ equal → pathOrder (a ∷ p) (b ∷ q) ≡ pathOrder p q
  place-row-empty : ∀ r → placeRow r [] ≡ (r ∷ [])
  place-row-before : ∀ p q c d rs → pathOrder p q ≢ later →
    placeRow (row p c) (row q d ∷ rs) ≡ (row p c ∷ row q d ∷ rs)
  place-row-after : ∀ p q c d rs → pathOrder p q ≡ later →
    placeRow (row p c) (row q d ∷ rs) ≡ (row q d ∷ placeRow (row p c) rs)
  sorted-rows-empty : sortedRows [] ≡ []
  sorted-rows-next : ∀ r rs → sortedRows (r ∷ rs) ≡ placeRow r (sortedRows rs)

  rawAtom : Atom → List Char
  valuesText : List Atom → List Char
  raw-text : ∀ s → rawAtom (text s) ≡ toList s
  raw-number : ∀ s → rawAtom (numeral s) ≡ toList s
  raw-null : rawAtom null ≡ toList "null"
  raw-true : rawAtom (truth true) ≡ toList "true"
  raw-false : rawAtom (truth false) ≡ toList "false"
  values-empty : valuesText [] ≡ []
  values-next : ∀ a as → valuesText (a ∷ as) ≡ rawAtom a ++ ('\n' ∷ valuesText as)

  placeField : String × List Char → List (String × List Char) → List (String × List Char)
  sortedFields : List (String × List Char) → List (String × List Char)
  place-field-empty : ∀ f → placeField f [] ≡ (f ∷ [])
  place-field-before : ∀ k l v w fs → charsOrder (toList k) (toList l) ≢ later →
    placeField (k , v) ((l , w) ∷ fs) ≡ ((k , v) ∷ (l , w) ∷ fs)
  place-field-after : ∀ k l v w fs → charsOrder (toList k) (toList l) ≡ later →
    placeField (k , v) ((l , w) ∷ fs) ≡ ((l , w) ∷ placeField (k , v) fs)
  sorted-fields-empty : sortedFields [] ≡ []
  sorted-fields-next : ∀ f fs → sortedFields (f ∷ fs) ≡ placeField f (sortedFields fs)

  indent : ℕ → List Char
  gap : Style → ℕ → List Char
  colon : Style → List Char
  fieldName : Style → String → List Char
  documentAt : Style → ℕ → Value → List Char
  documentFields : Style → ℕ → List (String × Value) → List (String × List Char)
  joinedFields : Style → ℕ → List (String × List Char) → List Char
  documentItems : Style → ℕ → List Value → List Char
  document : Style → Value → List Char

  indent-zero : indent zero ≡ []
  indent-next : ∀ d → indent (suc d) ≡ (' ' ∷ ' ' ∷ indent d)
  gap-plain : ∀ d → gap plain d ≡ ('\n' ∷ indent d)
  gap-ansi : ∀ d → gap ansi d ≡ []
  colon-plain : colon plain ≡ toList ": "
  colon-ansi : colon ansi ≡ paint ansi bold (toList ":")
  field-name-plain : ∀ k → fieldName plain k ≡ quotedString documentForm k
  field-name-ansi : ∀ k → fieldName ansi k ≡
    paint ansi blue ('"' ∷ []) ++ paint ansi blue (stringBody documentForm (toList k)) ++
    paint ansi blue ('"' ∷ [])
  document-scalar : ∀ s d a → documentAt s d (scalar a) ≡ atomText documentForm s a
  document-empty-object : ∀ s d → documentAt s d (object []) ≡
    paint s purple (toList "{") ++ paint s purple (toList "}")
  document-empty-array : ∀ s d → documentAt s d (array []) ≡
    paint s purple (toList "[") ++ paint s purple (toList "]")
  document-object : ∀ s d f fs → documentAt s d (object (f ∷ fs)) ≡
    paint s purple (toList "{") ++ gap s (suc d) ++
    joinedFields s (suc d) (sortedFields (documentFields s (suc d) (f ∷ fs))) ++
    gap s d ++ paint s purple (toList "}")
  document-array : ∀ s d v vs → documentAt s d (array (v ∷ vs)) ≡
    paint s purple (toList "[") ++ gap s (suc d) ++ documentItems s (suc d) (v ∷ vs) ++
    gap s d ++ paint s purple (toList "]")
  document-no-fields : ∀ s d → documentFields s d [] ≡ []
  document-field-next : ∀ s d k v fs → documentFields s d ((k , v) ∷ fs) ≡
    ((k , fieldName s k ++ colon s ++ documentAt s d v) ∷ documentFields s d fs)
  joined-fields-empty : ∀ s d → joinedFields s d [] ≡ []
  joined-fields-single : ∀ s d k cs → joinedFields s d ((k , cs) ∷ []) ≡ cs
  joined-fields-next : ∀ s d k cs f fs → joinedFields s d ((k , cs) ∷ f ∷ fs) ≡
    cs ++ paint s bold (toList ",") ++ gap s d ++ joinedFields s d (f ∷ fs)
  document-no-items : ∀ s d → documentItems s d [] ≡ []
  document-item-last : ∀ s d v → documentItems s d (v ∷ []) ≡ documentAt s d v
  document-item-next : ∀ s d v w ws → documentItems s d (v ∷ w ∷ ws) ≡
    documentAt s d v ++ paint s bold (toList ",") ++ gap s d ++ documentItems s d (w ∷ ws)
  document-line : ∀ s v → document s v ≡ documentAt s zero v ++ ('\n' ∷ [])

  observed-key : rowText statements plain (row (key "class" ∷ []) (leaf (numeral "18"))) ≡
    toList "json[\"class\"] = 18;\n"
  observed-unicode : rowText statements plain (row (key "λ" ∷ []) (leaf (numeral "15"))) ≡
    toList "json.λ = 15;\n"
  observed-path : rowText jsonRows plain (row (key "z" ∷ index 1 ∷ []) (leaf (text "<&>"))) ≡
    toList "[[\"z\",1],\"<&>\"]\n"
  observed-prefix-order : pathOrder (key "a" ∷ index 11 ∷ []) (key "a01" ∷ []) ≡ earlier
  observed-bracket-order : pathOrder (key "z" ∷ []) (key "a.b" ∷ []) ≡ earlier
  observed-quoted-prefix-order : pathOrder (key "a b!" ∷ []) (key "a b" ∷ []) ≡ earlier
  observed-row-c1 : escapeGlyph rowForm (fromℕ 127) ≡ toList "\\u007F"
  observed-row-control-hex : escapeGlyph rowForm (fromℕ 31) ≡ toList "\\u001F"
  observed-document-control-hex : escapeGlyph documentForm (fromℕ 31) ≡ toList "\\u001f"
  observed-text : valuesText (text "x\n" ∷ []) ≡ toList "x\n\n"
  observed-ansi-document : document ansi (object (("x" , scalar (numeral "1")) ∷ [])) ≡
    (fromℕ 27 ∷ toList "[35m{") ++ (fromℕ 27 ∷ toList "[0m") ++
    (fromℕ 27 ∷ toList "[34;1m\"") ++ (fromℕ 27 ∷ toList "[0;22m") ++
    (fromℕ 27 ∷ toList "[34;1mx") ++ (fromℕ 27 ∷ toList "[0;22m") ++
    (fromℕ 27 ∷ toList "[34;1m\"") ++ (fromℕ 27 ∷ toList "[0;22m") ++
    (fromℕ 27 ∷ toList "[1m:") ++ (fromℕ 27 ∷ toList "[22m") ++
    (fromℕ 27 ∷ toList "[31m1") ++ (fromℕ 27 ∷ toList "[0m") ++
    (fromℕ 27 ∷ toList "[35m}") ++ (fromℕ 27 ∷ toList "[0m\n")
