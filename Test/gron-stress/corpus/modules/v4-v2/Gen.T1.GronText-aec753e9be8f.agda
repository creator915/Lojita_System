module Gen.T1.GronText where

open import Context.Blueprint using (Commutes₂; keepPort; portLift)
open import Data.Bool using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; fromℕ; toℕ)
open import Data.List using (List; []; _∷_; _++_; all; any; map; concatMap)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Nat.Show using () renaming (show to showNat)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; fromList; toList) renaming (_++_ to _++ˢ_)
open import Data.String.Properties using (_≟_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (does)
open import Gen.T0.Gron using
  ( Atom; null; truth; numeral; text; Value; scalar; object; array
  ; Segment; key; index; Cell; leaf; objectCell; arrayCell; Row; row; rowsAt
  )

data Quoting : Set where
  rowQuoting documentQuoting : Quoting

data KeyForm : Set where
  dotted bracketed : KeyForm

data Ordering : Set where
  earlier tied later : Ordering

data FieldOrder : Set where
  pathOrder documentOrder : FieldOrder

data RowFormat : Set where
  assignments jsonRows : RowFormat

data Tone : Set where
  nameTone delimiterTone numberTone stringTone logicalTone quoteTone punctuationTone : Tone

record RowBatch : Set where
  constructor rowBatch
  field
    asGiven : List Row
    inPathOrder : List Row

postulate
  identifierStart identifierContinue : Char → Bool
  reservedWord : String → Bool
  keyForm : List Char → KeyForm

  identifier-start-ascii : ∀ c → (toℕ c <ᵇ 128) ≡ true →
    identifierStart c ≡
      ((toℕ c ≡ᵇ 36) ∨ (toℕ c ≡ᵇ 95) ∨
       ((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 91)) ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 123)))

  identifier-continue-ascii : ∀ c → (toℕ c <ᵇ 128) ≡ true →
    identifierContinue c ≡ (identifierStart c ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58)))

  identifier-start-continues : ∀ c → identifierStart c ≡ true → identifierContinue c ≡ true

  reserved-words : ∀ s →
    reservedWord s ≡ any (λ w → does (s ≟ w))
      ("break" ∷ "case" ∷ "catch" ∷ "class" ∷ "const" ∷ "continue" ∷ "debugger" ∷
       "default" ∷ "delete" ∷ "do" ∷ "else" ∷ "export" ∷ "extends" ∷ "false" ∷
       "finally" ∷ "for" ∷ "function" ∷ "if" ∷ "import" ∷ "in" ∷ "instanceof" ∷
       "new" ∷ "null" ∷ "return" ∷ "super" ∷ "switch" ∷ "this" ∷ "throw" ∷ "true" ∷
       "try" ∷ "typeof" ∷ "var" ∷ "void" ∷ "while" ∷ "with" ∷ "yield" ∷ [])

  empty-key : keyForm [] ≡ bracketed
  nonempty-key : ∀ c cs →
    keyForm (c ∷ cs) ≡
      (if identifierStart c ∧ all identifierContinue cs ∧ not (reservedWord (fromList (c ∷ cs)))
       then dotted else bracketed)

postulate
  hexDigit : Quoting → ℕ → Char
  unicodeEscape : Quoting → ℕ → String
  escapeChar : Quoting → Char → String
  quoteBody quoteText : Quoting → List Char → String

  hex-digit-decimal : ∀ q n → (n <ᵇ 10) ≡ true → hexDigit q n ≡ fromℕ (48 + n)
  hex-digit-row : ∀ n → (9 <ᵇ n) ≡ true → (n <ᵇ 16) ≡ true →
    hexDigit rowQuoting n ≡ fromℕ (55 + n)
  hex-digit-document : ∀ n → (9 <ᵇ n) ≡ true → (n <ᵇ 16) ≡ true →
    hexDigit documentQuoting n ≡ fromℕ (87 + n)
  unicode-escape-width : ∀ q n → (n <ᵇ 65536) ≡ true →
    unicodeEscape q n ≡
      fromList ('\\' ∷ 'u' ∷ hexDigit q ((n / 4096) % 16) ∷
        hexDigit q ((n / 256) % 16) ∷ hexDigit q ((n / 16) % 16) ∷ hexDigit q (n % 16) ∷ [])

  escape-double-quote : ∀ q → escapeChar q '"' ≡ "\\\""
  escape-backslash : ∀ q → escapeChar q '\\' ≡ "\\\\"
  escape-backspace : ∀ q → escapeChar q (fromℕ 8) ≡ "\\b"
  escape-tab : ∀ q → escapeChar q '\t' ≡ "\\t"
  escape-newline : ∀ q → escapeChar q '\n' ≡ "\\n"
  escape-form-feed : ∀ q → escapeChar q (fromℕ 12) ≡ "\\f"
  escape-return : ∀ q → escapeChar q '\r' ≡ "\\r"

  escape-control : ∀ q c → (toℕ c <ᵇ 32) ≡ true →
    ((toℕ c ≡ᵇ 8) ∨ (toℕ c ≡ᵇ 9) ∨ (toℕ c ≡ᵇ 10) ∨ (toℕ c ≡ᵇ 12) ∨ (toℕ c ≡ᵇ 13)) ≡ false →
    escapeChar q c ≡ unicodeEscape q (toℕ c)
  escape-row-control : ∀ c → (126 <ᵇ toℕ c) ≡ true → (toℕ c <ᵇ 160) ≡ true →
    escapeChar rowQuoting c ≡ unicodeEscape rowQuoting (toℕ c)
  escape-line-break : ∀ q c → ((toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233)) ≡ true →
    escapeChar q c ≡ unicodeEscape q (toℕ c)
  literal-row-char : ∀ c →
    ((31 <ᵇ toℕ c) ∧ ((toℕ c <ᵇ 127) ∨ (159 <ᵇ toℕ c))) ≡ true →
    ((toℕ c ≡ᵇ 34) ∨ (toℕ c ≡ᵇ 92) ∨ (toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233)) ≡ false →
    escapeChar rowQuoting c ≡ fromList (c ∷ [])
  literal-document-char : ∀ c → (31 <ᵇ toℕ c) ≡ true →
    ((toℕ c ≡ᵇ 34) ∨ (toℕ c ≡ᵇ 92) ∨ (toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233)) ≡ false →
    escapeChar documentQuoting c ≡ fromList (c ∷ [])

  quote-body-empty : ∀ q → quoteBody q [] ≡ ""
  quote-body-next : ∀ q c cs → quoteBody q (c ∷ cs) ≡ escapeChar q c ++ˢ quoteBody q cs
  quote-enclosed : ∀ q cs → quoteText q cs ≡ "\"" ++ˢ quoteBody q cs ++ˢ "\""

postulate
  lexOrder : List Char → List Char → Ordering
  compareFields : FieldOrder → String → String → Ordering

  lex-empty : lexOrder [] [] ≡ tied
  lex-shorter : ∀ c cs → lexOrder [] (c ∷ cs) ≡ earlier
  lex-longer : ∀ c cs → lexOrder (c ∷ cs) [] ≡ later
  lex-next : ∀ c d cs ds →
    lexOrder (c ∷ cs) (d ∷ ds) ≡
      (if toℕ c <ᵇ toℕ d then earlier else
       if toℕ d <ᵇ toℕ c then later else lexOrder cs ds)

  field-document-order : ∀ k l → compareFields documentOrder k l ≡ lexOrder (toList k) (toList l)
  field-dot-before-bracket : ∀ k l → keyForm (toList k) ≡ dotted → keyForm (toList l) ≡ bracketed →
    compareFields pathOrder k l ≡ earlier
  field-bracket-after-dot : ∀ k l → keyForm (toList k) ≡ bracketed → keyForm (toList l) ≡ dotted →
    compareFields pathOrder k l ≡ later
  field-dot-order : ∀ k l → keyForm (toList k) ≡ dotted → keyForm (toList l) ≡ dotted →
    compareFields pathOrder k l ≡ lexOrder (toList k) (toList l)
  field-bracket-order : ∀ k l → keyForm (toList k) ≡ bracketed → keyForm (toList l) ≡ bracketed →
    compareFields pathOrder k l ≡ lexOrder
      (toList (quoteText rowQuoting (toList k))) (toList (quoteText rowQuoting (toList l)))

data FieldsInOrder {A : Set} (order : FieldOrder) : List (String × A) → Set where
  no-fields : FieldsInOrder order []
  one-field : ∀ f → FieldsInOrder order (f ∷ [])
  more-fields : ∀ f g fs → compareFields order (proj₁ f) (proj₁ g) ≢ later →
    FieldsInOrder order (g ∷ fs) → FieldsInOrder order (f ∷ g ∷ fs)

postulate
  orderFields : {A : Set} → FieldOrder → List (String × A) → List (String × A)
  ordered-fields : ∀ {A : Set} order (fs : List (String × A)) →
    FieldsInOrder order (orderFields order fs)
  same-fields : ∀ {A : Set} order (fs : List (String × A)) →
    fs ↭ orderFields order fs

  rowsFor : List Segment → Value → RowBatch
  sortedItemsAt : List Segment → ℕ → List Value → List Row

  rows-commute : Commutes₂ (keepPort (List Segment)) (keepPort Value)
    (portLift RowBatch.asGiven) (λ _ _ → ⊤) _≡_ rowsAt rowsFor
  ordered-scalar-rows : ∀ p a →
    RowBatch.inPathOrder (rowsFor p (scalar a)) ≡ (row p (leaf a) ∷ [])
  ordered-object-rows : ∀ p fs →
    RowBatch.inPathOrder (rowsFor p (object fs)) ≡
      (row p objectCell ∷ concatMap proj₂
        (orderFields pathOrder (map
          (λ f → proj₁ f , RowBatch.inPathOrder (rowsFor (p ++ (key (proj₁ f) ∷ [])) (proj₂ f))) fs)))
  ordered-array-rows : ∀ p xs →
    RowBatch.inPathOrder (rowsFor p (array xs)) ≡ (row p arrayCell ∷ sortedItemsAt p zero xs)
  ordered-items-empty : ∀ p i → sortedItemsAt p i [] ≡ []
  ordered-items-next : ∀ p i x xs →
    sortedItemsAt p i (x ∷ xs) ≡
      RowBatch.inPathOrder (rowsFor (p ++ (index i ∷ [])) x) ++ sortedItemsAt p (suc i) xs

postulate
  sgr : String → String
  tint : Bool → Tone → String → String

  sgr-sequence : ∀ s → sgr s ≡ fromList (fromℕ 27 ∷ '[' ∷ []) ++ˢ s ++ˢ "m"
  tint-off : ∀ t s → tint false t s ≡ s
  tint-name : ∀ s → tint true nameTone s ≡ sgr "34;1" ++ˢ s ++ˢ sgr "0;22"
  tint-delimiter : ∀ s → tint true delimiterTone s ≡ sgr "35" ++ˢ s ++ˢ sgr "0"
  tint-number : ∀ s → tint true numberTone s ≡ sgr "31" ++ˢ s ++ˢ sgr "0"
  tint-string : ∀ s → tint true stringTone s ≡ sgr "33" ++ˢ s ++ˢ sgr "0"
  tint-logical : ∀ s → tint true logicalTone s ≡ sgr "36" ++ˢ s ++ˢ sgr "0"
  tint-quote : ∀ s → tint true quoteTone s ≡ sgr "32" ++ˢ s ++ˢ sgr "0"
  tint-punctuation : ∀ s → tint true punctuationTone s ≡ sgr "1" ++ˢ s ++ˢ sgr "22"

  rowAtom : Bool → Atom → String
  rowCell : Bool → Cell → String
  assignmentSegment jsonSegment : Bool → Segment → String
  assignmentPath jsonPath : Bool → List Segment → String
  renderRow : RowFormat → Bool → Row → String
  renderRows : RowFormat → Bool → List Row → String

  row-atom-null : ∀ b → rowAtom b null ≡ tint b logicalTone "null"
  row-atom-bool : ∀ b t → rowAtom b (truth t) ≡ tint b logicalTone (if t then "true" else "false")
  row-atom-number : ∀ b n → rowAtom b (numeral n) ≡ tint b numberTone n
  row-atom-text : ∀ b s →
    rowAtom b (text s) ≡ tint b stringTone (quoteText rowQuoting (toList s))

  row-cell-leaf : ∀ b a → rowCell b (leaf a) ≡ rowAtom b a
  row-cell-object : ∀ b → rowCell b objectCell ≡ tint b delimiterTone "{}"
  row-cell-array : ∀ b → rowCell b arrayCell ≡ tint b delimiterTone "[]"

  assignment-dot : ∀ b k → keyForm (toList k) ≡ dotted →
    assignmentSegment b (key k) ≡ "." ++ˢ tint b nameTone k
  assignment-bracket : ∀ b k → keyForm (toList k) ≡ bracketed →
    assignmentSegment b (key k) ≡
      tint b delimiterTone "[" ++ˢ tint b stringTone (quoteText rowQuoting (toList k)) ++ˢ tint b delimiterTone "]"
  assignment-index : ∀ b i → assignmentSegment b (index i) ≡
    tint b delimiterTone "[" ++ˢ tint b numberTone (showNat i) ++ˢ tint b delimiterTone "]"
  assignment-path-empty : ∀ b → assignmentPath b [] ≡ ""
  assignment-path-next : ∀ b s p → assignmentPath b (s ∷ p) ≡ assignmentSegment b s ++ˢ assignmentPath b p

  json-path-key : ∀ b k → jsonSegment b (key k) ≡ tint b stringTone (quoteText rowQuoting (toList k))
  json-path-index : ∀ b i → jsonSegment b (index i) ≡ tint b numberTone (showNat i)
  json-path-empty : ∀ b → jsonPath b [] ≡ ""
  json-path-single : ∀ b s → jsonPath b (s ∷ []) ≡ jsonSegment b s
  json-path-next : ∀ b s t p → jsonPath b (s ∷ t ∷ p) ≡ jsonSegment b s ++ˢ "," ++ˢ jsonPath b (t ∷ p)

  render-assignment : ∀ b p c → renderRow assignments b (row p c) ≡
    tint b nameTone "json" ++ˢ assignmentPath b p ++ˢ " = " ++ˢ rowCell b c ++ˢ ";"
  render-json-row : ∀ b p c → renderRow jsonRows b (row p c) ≡
    tint b delimiterTone "[" ++ˢ tint b delimiterTone "[" ++ˢ jsonPath b p ++ˢ
      tint b delimiterTone "]" ++ˢ "," ++ˢ rowCell b c ++ˢ tint b delimiterTone "]"

  render-rows-empty : ∀ f b → renderRows f b [] ≡ ""
  render-rows-next : ∀ f b r rs → renderRows f b (r ∷ rs) ≡ renderRow f b r ++ˢ "\n" ++ˢ renderRows f b rs

postulate
  documentAtom : Bool → Atom → String
  documentKey : Bool → String → String
  documentAt : Bool → ℕ → Value → String
  renderDocument : Bool → Value → String
  indentation : ℕ → String
  linePrefix : Bool → ℕ → String
  documentField : Bool → ℕ → String × String → String
  documentFields : Bool → ℕ → List (String × String) → String
  documentItems : Bool → ℕ → List String → String

  document-atom-null : ∀ b → documentAtom b null ≡ tint b logicalTone "null"
  document-atom-bool : ∀ b t → documentAtom b (truth t) ≡ tint b logicalTone (if t then "true" else "false")
  document-atom-number : ∀ b n → documentAtom b (numeral n) ≡ tint b numberTone n
  document-atom-text : ∀ b s → documentAtom b (text s) ≡
    tint b quoteTone "\"" ++ˢ tint b stringTone (quoteBody documentQuoting (toList s)) ++ˢ tint b quoteTone "\""
  document-key : ∀ b k → documentKey b k ≡
    tint b nameTone "\"" ++ˢ tint b nameTone (quoteBody documentQuoting (toList k)) ++ˢ tint b nameTone "\""

  indent-zero : indentation zero ≡ ""
  indent-next : ∀ d → indentation (suc d) ≡ "  " ++ˢ indentation d
  line-pretty : ∀ d → linePrefix false d ≡ "\n" ++ˢ indentation d
  line-compact : ∀ d → linePrefix true d ≡ ""

  document-scalar : ∀ b d a → documentAt b d (scalar a) ≡ documentAtom b a
  document-empty-object : ∀ b d → documentAt b d (object []) ≡
    tint b delimiterTone "{" ++ˢ tint b delimiterTone "}"
  document-empty-array : ∀ b d → documentAt b d (array []) ≡
    tint b delimiterTone "[" ++ˢ tint b delimiterTone "]"

  document-object : ∀ b d f fs → documentAt b d (object (f ∷ fs)) ≡
    tint b delimiterTone "{" ++ˢ
    documentFields b (suc d) (orderFields documentOrder
      (map (λ kv → proj₁ kv , documentAt b (suc d) (proj₂ kv)) (f ∷ fs))) ++ˢ
    linePrefix b d ++ˢ tint b delimiterTone "}"
  document-array : ∀ b d x xs → documentAt b d (array (x ∷ xs)) ≡
    tint b delimiterTone "[" ++ˢ documentItems b (suc d) (map (documentAt b (suc d)) (x ∷ xs)) ++ˢ
    linePrefix b d ++ˢ tint b delimiterTone "]"

  document-field : ∀ b d k s → documentField b d (k , s) ≡
    linePrefix b d ++ˢ documentKey b k ++ˢ (if b then tint b punctuationTone ":" else ": ") ++ˢ s
  document-fields-empty : ∀ b d → documentFields b d [] ≡ ""
  document-fields-single : ∀ b d f → documentFields b d (f ∷ []) ≡ documentField b d f
  document-fields-next : ∀ b d f g fs → documentFields b d (f ∷ g ∷ fs) ≡
    documentField b d f ++ˢ tint b punctuationTone "," ++ˢ documentFields b d (g ∷ fs)
  document-items-empty : ∀ b d → documentItems b d [] ≡ ""
  document-items-single : ∀ b d s → documentItems b d (s ∷ []) ≡ linePrefix b d ++ˢ s
  document-items-next : ∀ b d s t ss → documentItems b d (s ∷ t ∷ ss) ≡
    linePrefix b d ++ˢ s ++ˢ tint b punctuationTone "," ++ˢ documentItems b d (t ∷ ss)
  document-newline : ∀ b v → renderDocument b v ≡ documentAt b zero v ++ˢ "\n"

  valueText : Atom → String
  renderValues : List Atom → String
  value-text-raw : ∀ s → valueText (text s) ≡ s
  value-text-null : valueText null ≡ "null"
  value-text-bool : ∀ t → valueText (truth t) ≡ (if t then "true" else "false")
  value-text-number : ∀ n → valueText (numeral n) ≡ n
  render-values-empty : renderValues [] ≡ ""
  render-values-next : ∀ a as → renderValues (a ∷ as) ≡ valueText a ++ˢ "\n" ++ˢ renderValues as

postulate
  observed-identifier-forms :
    map (λ s → keyForm (toList s))
      ("$x" ∷ "_a" ∷ "á" ∷ "a٢" ∷ "a‿" ∷ "aⅧ" ∷ "λ" ∷ "Ⅷ" ∷ "漢" ∷ "𐐀" ∷ "enum" ∷ "await" ∷
       "a²" ∷ "a·" ∷ fromList ('a' ∷ fromℕ 8204 ∷ []) ∷ fromList ('a' ∷ fromℕ 8205 ∷ []) ∷
       "·" ∷ "͵" ∷ "٢a" ∷ "℘" ∷ "℮" ∷ "゛" ∷ "class" ∷ []) ≡
      (dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷ dotted ∷
       bracketed ∷ bracketed ∷ bracketed ∷ bracketed ∷ bracketed ∷ bracketed ∷ bracketed ∷ bracketed ∷
       bracketed ∷ bracketed ∷ bracketed ∷ [])

  observed-bracket-terminator : compareFields pathOrder "." ".!" ≡ later
  observed-bracket-escape : compareFields pathOrder ".a" (fromList ('.' ∷ fromℕ 1 ∷ [])) ≡ later
  observed-document-prefix : compareFields documentOrder "." ". " ≡ earlier
  observed-row-c1 : escapeChar rowQuoting (fromℕ 133) ≡ "\\u0085"
  observed-document-c1 : escapeChar documentQuoting (fromℕ 133) ≡ fromList (fromℕ 133 ∷ [])
  observed-row-hex : escapeChar rowQuoting (fromℕ 31) ≡ "\\u001F"
  observed-document-hex : escapeChar documentQuoting (fromℕ 31) ≡ "\\u001f"
  observed-colored-assignment : renderRow assignments true
      (row (key "a" ∷ index 2 ∷ []) (leaf (numeral "1"))) ≡
    sgr "34;1" ++ˢ "json" ++ˢ sgr "0;22" ++ˢ "." ++ˢ sgr "34;1" ++ˢ "a" ++ˢ sgr "0;22" ++ˢ
      sgr "35" ++ˢ "[" ++ˢ sgr "0" ++ˢ sgr "31" ++ˢ "2" ++ˢ sgr "0" ++ˢ
      sgr "35" ++ˢ "]" ++ˢ sgr "0" ++ˢ " = " ++ˢ sgr "31" ++ˢ "1" ++ˢ sgr "0" ++ˢ ";"
  observed-colored-row : renderRow jsonRows true (row (key "x" ∷ []) (leaf (numeral "1"))) ≡
    sgr "35" ++ˢ "[" ++ˢ sgr "0" ++ˢ sgr "35" ++ˢ "[" ++ˢ sgr "0" ++ˢ
      sgr "33" ++ˢ "\"x\"" ++ˢ sgr "0" ++ˢ sgr "35" ++ˢ "]" ++ˢ sgr "0" ++ˢ "," ++ˢ
      sgr "31" ++ˢ "1" ++ˢ sgr "0" ++ˢ sgr "35" ++ˢ "]" ++ˢ sgr "0"
  observed-empty-colored-text : renderDocument true (scalar (text "")) ≡
    sgr "32" ++ˢ "\"" ++ˢ sgr "0" ++ˢ sgr "33" ++ˢ sgr "0" ++ˢ sgr "32" ++ˢ "\"" ++ˢ sgr "0" ++ˢ "\n"
  observed-raw-values : renderValues (text "<&>λ" ∷ numeral "1" ∷ truth true ∷ []) ≡ "<&>λ\n1\ntrue\n"
