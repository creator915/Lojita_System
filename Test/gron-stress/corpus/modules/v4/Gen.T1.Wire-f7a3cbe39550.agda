module Gen.T1.Wire where

  open import Agda.Builtin.Char using (primCharEquality; primNatToChar)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (Bool; false; true; _∧_; _∨_; not; if_then_else_)
  open import Data.Char using (Char; toℕ)
  open import Data.List using (List; []; _∷_; [_]; any; map; replicate)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ; suc; _+_; _*_; _<ᵇ_; _≡ᵇ_)
  open import Data.Nat.DivMod using (_/_; _%_)
  open import Data.Nat.Show using (show)
  open import Data.Product using (_×_; _,_; proj₂)
  open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)
  open import Data.Unit using (⊤)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Context.Blueprint using (PortLift; portLift; keepPort; Commutes₂)
  import Gen.T0.Gron as B
  data Encoding : Set where
    assignments : Encoding
    pathPairs : Encoding
  data StringSyntax : Set where
    gronEscapes : StringSyntax
    jsonEscapes : StringSyntax
  record Style : Set where
    constructor styled
    field
      encoding : Encoding
      colour : Bool
  record ForwardOptions : Set where
    constructor forwardOptions
    field
      style : Style
      noSort : Bool
  record Emission : Set where
    constructor emission
    field
      bindings : List B.Binding
      body : String
  postulate
    hexDigit : StringSyntax → ℕ → Char
  postulate
    unicodeEscape : StringSyntax → ℕ → String
  postulate
    hexNumeral : (q : _) → (n : _) → ((n <ᵇ 10) ≡ true) → hexDigit q n ≡ primNatToChar (48 + n)
  postulate
    hexUpper : (n : _) → ((n <ᵇ 6) ≡ true) → hexDigit gronEscapes (10 + n) ≡ primNatToChar (65 + n)
  postulate
    hexLower : (n : _) → ((n <ᵇ 6) ≡ true) → hexDigit jsonEscapes (10 + n) ≡ primNatToChar (97 + n)
  postulate
    unicodeSpelling : (q : _) → (n : _) → unicodeEscape q n ≡ ("\\u" ++ˢ fromList (hexDigit q ((n / 4096) % 16) ∷ (hexDigit q ((n / 256) % 16) ∷ (hexDigit q ((n / 16) % 16) ∷ (hexDigit q (n % 16) ∷ [])))))
  postulate
    numericEscape : StringSyntax → Char → Bool
  postulate
    gronControl : (c : _) → numericEscape gronEscapes c ≡ ((toℕ c <ᵇ 32) ∨ (((126 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 160)) ∨ ((toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233))))
  postulate
    jsonControl : (c : _) → numericEscape jsonEscapes c ≡ ((toℕ c <ᵇ 32) ∨ ((toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233)))
  postulate
    shortEscape : Char → Maybe String
  postulate
    escapedQuote : shortEscape '\"' ≡ just "\\\""
  postulate
    escapedBackslash : shortEscape '\\' ≡ just "\\\\"
  postulate
    escapedBackspace : shortEscape (primNatToChar 8) ≡ just "\\b"
  postulate
    escapedFormfeed : shortEscape (primNatToChar 12) ≡ just "\\f"
  postulate
    escapedNewline : shortEscape (primNatToChar 10) ≡ just "\\n"
  postulate
    escapedReturn : shortEscape (primNatToChar 13) ≡ just "\\r"
  postulate
    escapedTab : shortEscape (primNatToChar 9) ≡ just "\\t"
  postulate
    noShortEscape : (c : _) → (any (primCharEquality c) ('\"' ∷ ('\\' ∷ (primNatToChar 8 ∷ (primNatToChar 12 ∷ (primNatToChar 10 ∷ (primNatToChar 13 ∷ (primNatToChar 9 ∷ []))))))) ≡ false) → shortEscape c ≡ nothing
  postulate
    escapedChar : StringSyntax → Char → String
  postulate
    escapedChars : StringSyntax → List Char → String
  postulate
    stringLiteral : StringSyntax → String → String
  postulate
    shortChar : (q : _) → (c : _) → (s : _) → (shortEscape c ≡ just s) → escapedChar q c ≡ s
  postulate
    numericChar : (q : _) → (c : _) → (shortEscape c ≡ nothing) → (numericEscape q c ≡ true) → escapedChar q c ≡ unicodeEscape q (toℕ c)
  postulate
    unchangedChar : (q : _) → (c : _) → (shortEscape c ≡ nothing) → (numericEscape q c ≡ false) → escapedChar q c ≡ fromList ([ c ])
  postulate
    noChars : (q : _) → escapedChars q [] ≡ ""
  postulate
    nextChar : (q : _) → (c : _) → (cs : _) → escapedChars q (c ∷ cs) ≡ (escapedChar q c ++ˢ escapedChars q cs)
  postulate
    stringQuotes : (q : _) → (s : _) → stringLiteral q s ≡ ("\"" ++ˢ (escapedChars q (toList s) ++ˢ "\""))
  postulate
    identifierHead : Char → Bool
  postulate
    identifierTail : Char → Bool
  postulate
    tailLetters : List Char → Bool
  postulate
    identifierLetters : List Char → Bool
  postulate
    reservedWords : List String
  postulate
    bareName : String → Bool
  postulate
    asciiHead : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → identifierHead c ≡ (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 91)) ∨ (((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 123)) ∨ ((toℕ c ≡ᵇ 36) ∨ (toℕ c ≡ᵇ 95))))
  postulate
    asciiTail : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → identifierTail c ≡ (identifierHead c ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58)))
  postulate
    emptyTail : tailLetters [] ≡ true
  postulate
    letterTail : (c : _) → (cs : _) → tailLetters (c ∷ cs) ≡ (identifierTail c ∧ tailLetters cs)
  postulate
    emptyName : identifierLetters [] ≡ false
  postulate
    nonemptyName : (c : _) → (cs : _) → identifierLetters (c ∷ cs) ≡ (identifierHead c ∧ tailLetters cs)
  postulate
    unreservedName : (s : _) → bareName s ≡ (identifierLetters (toList s) ∧ not (any (primStringEquality s) reservedWords))
  postulate
    keywordVocabulary : reservedWords ≡ ("break" ∷ ("case" ∷ ("catch" ∷ ("class" ∷ ("const" ∷ ("continue" ∷ ("debugger" ∷ ("default" ∷ ("delete" ∷ ("do" ∷ ("else" ∷ ("export" ∷ ("extends" ∷ ("false" ∷ ("finally" ∷ ("for" ∷ ("function" ∷ ("if" ∷ ("import" ∷ ("in" ∷ ("instanceof" ∷ ("new" ∷ ("null" ∷ ("return" ∷ ("super" ∷ ("switch" ∷ ("this" ∷ ("throw" ∷ ("true" ∷ ("try" ∷ ("typeof" ∷ ("var" ∷ ("void" ∷ ("while" ∷ ("with" ∷ ("yield" ∷ []))))))))))))))))))))))))))))))))))))
  postulate
    startFixture : map bareName ("Ǆ" ∷ ("ǅ" ∷ ("ǆ" ∷ ("ʰ" ∷ ("中" ∷ ("Ⅻ" ∷ ("²" ∷ ("٢" ∷ ("℘" ∷ []))))))))) ≡ (true ∷ (false ∷ (true ∷ (true ∷ (true ∷ (true ∷ (false ∷ (false ∷ (false ∷ [])))))))))
  postulate
    tailFixture : map bareName ("á" ∷ ("aः" ∷ ("a٢" ∷ ("a‿" ∷ ("a＿" ∷ ("a²" ∷ ("a҈" ∷ ("aǅ" ∷ ("a‍" ∷ []))))))))) ≡ (true ∷ (true ∷ (true ∷ (true ∷ (true ∷ (false ∷ (false ∷ (false ∷ (false ∷ [])))))))))
  postulate
    access : Bool → B.Step → String
  postulate
    accessSuffix : Bool → List B.Step → String
  postulate
    assignmentPath : Bool → List B.Step → String
  postulate
    pairComponent : Bool → B.Step → String
  postulate
    pairComponents : Bool → List B.Step → String
  postulate
    bindingValueText : Bool → B.BindingValue → String
  postulate
    renderBinding : Style → B.Binding → String
  postulate
    renderBindings : Style → List B.Binding → String
  postulate
    fieldAccess : (c : _) → (k : _) → access c (B.fieldName k) ≡ (if bareName k then ("." ++ˢ B.tint c B.identifier k) else (B.tint c B.delimiter "[" ++ˢ (B.tint c B.stringToken (stringLiteral gronEscapes k) ++ˢ B.tint c B.delimiter "]")))
  postulate
    indexAccess : (c : _) → (n : _) → access c (B.index n) ≡ (B.tint c B.delimiter "[" ++ˢ (B.tint c B.numberToken (show n) ++ˢ B.tint c B.delimiter "]"))
  postulate
    emptySuffix : (c : _) → accessSuffix c [] ≡ ""
  postulate
    extendSuffix : (c : _) → (x : _) → (xs : _) → accessSuffix c (x ∷ xs) ≡ (access c x ++ˢ accessSuffix c xs)
  postulate
    assignmentRoot : (c : _) → (xs : _) → assignmentPath c xs ≡ (B.tint c B.identifier "json" ++ˢ accessSuffix c xs)
  postulate
    pairField : (c : _) → (k : _) → pairComponent c (B.fieldName k) ≡ B.tint c B.stringToken (stringLiteral gronEscapes k)
  postulate
    pairIndex : (c : _) → (n : _) → pairComponent c (B.index n) ≡ B.tint c B.numberToken (show n)
  postulate
    emptyPairPath : (c : _) → pairComponents c [] ≡ ""
  postulate
    onePairStep : (c : _) → (x : _) → pairComponents c ([ x ]) ≡ pairComponent c x
  postulate
    addPairStep : (c : _) → (x : _) → (y : _) → (ys : _) → pairComponents c (x ∷ (y ∷ ys)) ≡ (pairComponent c x ++ˢ ("," ++ˢ pairComponents c (y ∷ ys)))
  postulate
    objectText : (c : _) → bindingValueText c B.objectMarker ≡ B.tint c B.delimiter "{}"
  postulate
    arrayText : (c : _) → bindingValueText c B.arrayMarker ≡ B.tint c B.delimiter "[]"
  postulate
    nullText : (c : _) → bindingValueText c (B.literal B.null) ≡ B.tint c B.keyword "null"
  postulate
    trueText : (c : _) → bindingValueText c (B.literal (B.boolean true)) ≡ B.tint c B.keyword "true"
  postulate
    falseText : (c : _) → bindingValueText c (B.literal (B.boolean false)) ≡ B.tint c B.keyword "false"
  postulate
    numericText : (c : _) → (s : _) → bindingValueText c (B.literal (B.number s)) ≡ B.tint c B.numberToken s
  postulate
    quotedText : (c : _) → (s : _) → bindingValueText c (B.literal (B.text s)) ≡ B.tint c B.stringToken (stringLiteral gronEscapes s)
  postulate
    assignmentLine : (c : _) → (p : _) → (v : _) → renderBinding (styled assignments c) (B.binding p v) ≡ (assignmentPath c p ++ˢ (" = " ++ˢ (bindingValueText c v ++ˢ ";\n")))
  postulate
    pairLine : (c : _) → (p : _) → (v : _) → renderBinding (styled pathPairs c) (B.binding p v) ≡ (B.tint c B.delimiter "[" ++ˢ (B.tint c B.delimiter "[" ++ˢ (pairComponents c p ++ˢ (B.tint c B.delimiter "]" ++ˢ ("," ++ˢ (bindingValueText c v ++ˢ (B.tint c B.delimiter "]" ++ˢ "\n")))))))
  postulate
    noLines : (s : _) → renderBindings s [] ≡ ""
  postulate
    nextLine : (s : _) → (x : _) → (xs : _) → renderBindings s (x ∷ xs) ≡ (renderBinding s x ++ˢ renderBindings s xs)
  postulate
    traversal : Bool → B.Traversal
  postulate
    unsorted : traversal true ≡ B.enumerated
  postulate
    sorted : traversal false ≡ B.byAccess (λ k → access false (B.fieldName k))
  projectTraversal : ForwardOptions → B.Traversal
  projectTraversal opts = traversal (ForwardOptions.noSort opts)
  projectEmission : B.Reply Emission → B.Reply (List B.Binding)
  projectEmission (B.reply n (emission bs _) err) = B.reply n bs err
  optionsPort : PortLift B.Traversal ForwardOptions
  optionsPort = portLift projectTraversal
  emissionPort : PortLift (B.Reply (List B.Binding)) (B.Reply Emission)
  emissionPort = portLift projectEmission
  postulate
    renderReply : Style → B.Reply (List B.Binding) → B.Reply Emission
  postulate
    endingForward : (s : _) → (n : _) → (bs : _) → (err : _) → renderReply s (B.reply n bs err) ≡ B.reply n (emission bs (renderBindings s bs)) err
  postulate
    forwardWire : ForwardOptions → B.Parsed B.Value → B.Reply Emission
  postulate
    streamWire : ForwardOptions → List B.Value → Maybe String → B.Reply Emission
  postulate
    forwardWireLaw : (o : _) → (d : _) → forwardWire o d ≡ renderReply (ForwardOptions.style o) (B.forward (projectTraversal o) d)
  postulate
    streamWireLaw : (o : _) → (ds : _) → (e : _) → streamWire o ds e ≡ renderReply (ForwardOptions.style o) (B.forwardStream (projectTraversal o) ds e)
  postulate
    forwardSquare : Commutes₂ optionsPort (keepPort (B.Parsed B.Value)) emissionPort (λ _ _ → ⊤) _≡_ B.forward forwardWire
  postulate
    indentation : ℕ → String
  postulate
    leadJSON : Bool → ℕ → String
  postulate
    joinJSON : Bool → List String → String
  postulate
    surroundJSON : Bool → ℕ → String → String → List String → String
  postulate
    jsonKey : Bool → String → String
  postulate
    jsonAtom : Bool → B.Atom → String
  postulate
    memberColon : Bool → String
  postulate
    valueQuote : String
  postulate
    renderJSONAt : Bool → ℕ → B.Value → String
  postulate
    renderJSONItems : Bool → ℕ → List B.Value → List String
  postulate
    renderJSONMembers : Bool → ℕ → List (String × B.Value) → List (String × String)
  postulate
    reverseWire : Bool → B.Reply (Maybe B.Value) → B.Reply String
  postulate
    twoSpaceIndent : (n : _) → indentation n ≡ fromList (replicate (2 * n) ' ')
  postulate
    plainLead : (n : _) → leadJSON false n ≡ indentation n
  postulate
    colourLead : (n : _) → leadJSON true n ≡ ""
  postulate
    noJSONRows : (c : _) → joinJSON c [] ≡ ""
  postulate
    oneJSONRow : (c : _) → (x : _) → joinJSON c ([ x ]) ≡ x
  postulate
    plainJSONRows : (x : _) → (y : _) → (ys : _) → joinJSON false (x ∷ (y ∷ ys)) ≡ (x ++ˢ (",\n" ++ˢ joinJSON false (y ∷ ys)))
  postulate
    colourJSONRows : (x : _) → (y : _) → (ys : _) → joinJSON true (x ∷ (y ∷ ys)) ≡ (x ++ˢ (B.tint true B.colon "," ++ˢ joinJSON true (y ∷ ys)))
  postulate
    plainEmptyJSON : (n : _) → (left : _) → (right : _) → surroundJSON false n left right [] ≡ (left ++ˢ right)
  postulate
    plainNestedJSON : (n : _) → (left : _) → (right : _) → (x : _) → (xs : _) → surroundJSON false n left right (x ∷ xs) ≡ (left ++ˢ ("\n" ++ˢ (joinJSON false (x ∷ xs) ++ˢ ("\n" ++ˢ (indentation n ++ˢ right)))))
  postulate
    colourSurroundJSON : (n : _) → (left : _) → (right : _) → (xs : _) → surroundJSON true n left right xs ≡ (B.tint true B.delimiter left ++ˢ (joinJSON true xs ++ˢ B.tint true B.delimiter right))
  postulate
    plainKey : (k : _) → jsonKey false k ≡ stringLiteral jsonEscapes k
  postulate
    colourKey : (k : _) → jsonKey true k ≡ (B.tint true B.identifier "\"" ++ˢ (B.tint true B.identifier (escapedChars jsonEscapes (toList k)) ++ˢ B.tint true B.identifier "\""))
  postulate
    plainMemberColon : memberColon false ≡ ": "
  postulate
    colourMemberColon : memberColon true ≡ B.tint true B.colon ":"
  postulate
    greenQuote : valueQuote ≡ (B.ansiEscape ++ˢ ("[32m\"" ++ˢ (B.ansiEscape ++ˢ "[0m")))
  postulate
    plainJSONString : (s : _) → jsonAtom false (B.text s) ≡ stringLiteral jsonEscapes s
  postulate
    colourJSONString : (s : _) → jsonAtom true (B.text s) ≡ (valueQuote ++ˢ (B.tint true B.stringToken (escapedChars jsonEscapes (toList s)) ++ˢ valueQuote))
  postulate
    jsonNull : (c : _) → jsonAtom c B.null ≡ B.tint c B.keyword "null"
  postulate
    jsonTrue : (c : _) → jsonAtom c (B.boolean true) ≡ B.tint c B.keyword "true"
  postulate
    jsonFalse : (c : _) → jsonAtom c (B.boolean false) ≡ B.tint c B.keyword "false"
  postulate
    jsonNumber : (c : _) → (s : _) → jsonAtom c (B.number s) ≡ B.tint c B.numberToken s
  postulate
    scalarJSON : (c : _) → (n : _) → (a : _) → renderJSONAt c n (B.scalar a) ≡ jsonAtom c a
  postulate
    arrayJSON : (c : _) → (n : _) → (vs : _) → renderJSONAt c n (B.array vs) ≡ surroundJSON c n "[" "]" (renderJSONItems c (suc n) vs)
  postulate
    objectJSON : (c : _) → (n : _) → (fs : _) → renderJSONAt c n (B.object fs) ≡ surroundJSON c n "{" "}" (map proj₂ (B.orderMembers (B.byAccess (λ k → k)) (renderJSONMembers c (suc n) fs)))
  postulate
    noJSONItems : (c : _) → (n : _) → renderJSONItems c n [] ≡ []
  postulate
    nextJSONItem : (c : _) → (n : _) → (v : _) → (vs : _) → renderJSONItems c n (v ∷ vs) ≡ ((leadJSON c n ++ˢ renderJSONAt c n v) ∷ renderJSONItems c n vs)
  postulate
    noJSONMembers : (c : _) → (n : _) → renderJSONMembers c n [] ≡ []
  postulate
    nextJSONMember : (c : _) → (n : _) → (k : _) → (v : _) → (fs : _) → renderJSONMembers c n ((k , v) ∷ fs) ≡ ((k , (leadJSON c n ++ˢ (jsonKey c k ++ˢ (memberColon c ++ˢ renderJSONAt c n v)))) ∷ renderJSONMembers c n fs)
  postulate
    reverseBody : (c : _) → (n : _) → (v : _) → (e : _) → reverseWire c (B.reply n (just v) e) ≡ B.reply n (renderJSONAt c 0 v ++ˢ "\n") e
  postulate
    reverseNoBody : (c : _) → (n : _) → (e : _) → reverseWire c (B.reply n nothing e) ≡ B.reply n "" e
  postulate
    forwardControlFixture : stringLiteral gronEscapes (fromList (primNatToChar 31 ∷ [])) ≡ "\"\\u001F\""
  postulate
    reverseControlFixture : stringLiteral jsonEscapes (fromList (primNatToChar 11 ∷ [])) ≡ "\"\\u000b\""
  postulate
    reverseC1Fixture : stringLiteral jsonEscapes (fromList (primNatToChar 133 ∷ [])) ≡ fromList ('\"' ∷ (primNatToChar 133 ∷ ('\"' ∷ [])))
  postulate
    escapedKeyOrderFixture : B.earlier (toList (access false (B.fieldName " "))) (toList (access false (B.fieldName (fromList (primNatToChar 11 ∷ []))))) ≡ true
  postulate
    assignmentBracketFixture : renderBinding (styled assignments false) (B.binding (B.fieldName "a-" ∷ []) B.arrayMarker) ≡ "json[\"a-\"] = [];\n"
  postulate
    pairBracketFixture : renderBinding (styled pathPairs false) (B.binding (B.fieldName "a-" ∷ []) B.arrayMarker) ≡ "[[\"a-\"],[]]\n"
  postulate
    partialOutputFixture : streamWire (forwardOptions (styled assignments false) false) (B.scalar (B.number "1") ∷ []) (just "unexpected EOF") ≡ B.reply 3 (emission (B.binding [] B.arrayMarker ∷ (B.binding (B.index 0 ∷ []) (B.literal (B.number "1")) ∷ [])) "json = [];\njson[0] = 1;\n") "failed to form statements: unexpected EOF\n"
  postulate
    sparseJSONFixture : reverseWire false (B.reply 0 (just (B.object (("a" , B.array (B.scalar B.null ∷ (B.scalar B.null ∷ (B.scalar (B.number "3") ∷ [])))) ∷ []))) "") ≡ B.reply 0 "{\n  \"a\": [\n    null,\n    null,\n    3\n  ]\n}\n" ""
  postulate
    colouredEmptyFixture : reverseWire true (B.reply 0 (just (B.scalar (B.text ""))) "") ≡ B.reply 0 (B.ansiEscape ++ˢ ("[32m\"" ++ˢ (B.ansiEscape ++ˢ ("[0m" ++ˢ (B.ansiEscape ++ˢ ("[33m" ++ˢ (B.ansiEscape ++ˢ ("[0m" ++ˢ (B.ansiEscape ++ˢ ("[32m\"" ++ˢ (B.ansiEscape ++ˢ "[0m\n"))))))))))) ""
