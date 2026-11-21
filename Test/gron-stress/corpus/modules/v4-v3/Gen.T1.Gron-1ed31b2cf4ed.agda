module Gen.T1.Gron where

  open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
  open import Data.Char using (Char; toℕ; fromℕ)
  open import Data.List using (List; []; _∷_; _++_; all; map; foldr)
  open import Data.Empty using (⊥)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ; suc; _<ᵇ_; _≡ᵇ_)
  import Data.Nat.Show as Nat
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  import Gen.T0.Gron as B
  data Notation : Set where
    assignments : Notation
    pairs : Notation
  data Ordering : Set where
    before : Ordering
    equal : Ordering
    after : Ordering
  data SortMode : Set where
    sorted : SortMode
    given : SortMode
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
  record Display : Set where
    constructor display
    field
      notation : Notation
      color : Bool
      tree : B.Value
  record Row : Set where
    constructor row
    field
      statement : B.Statement
      output : String
  record Config : Set where
    constructor config
    field
      notation : Notation
      color : Bool
      sorting : SortMode
  record Report : Set where
    constructor report
    field
      output : String
      issue : Maybe String
  postulate
    decodePrefix : List Char → String ⊎ Parsed B.Value
  postulate
    decodeNumber : List Char → String ⊎ Parsed String
  postulate
    decodeQuoted : List Char → String ⊎ Parsed String
  postulate
    decodeElements : List Char → String ⊎ Parsed (List B.Value)
  postulate
    decodeMembers : List Char → String ⊎ Parsed (List (String × B.Value))
  postulate
    endOfInput : decodePrefix [] ≡ inj₁ "EOF"
  postulate
    leadingSpace : (xs : _) → decodePrefix (' ' ∷ xs) ≡ decodePrefix xs
  postulate
    leadingTab : (xs : _) → decodePrefix ('	' ∷ xs) ≡ decodePrefix xs
  postulate
    leadingCR : (xs : _) → decodePrefix ('\r' ∷ xs) ≡ decodePrefix xs
  postulate
    leadingLF : (xs : _) → decodePrefix ('\n' ∷ xs) ≡ decodePrefix xs
  postulate
    truePrefix : (xs : _) → decodePrefix ('t' ∷ ('r' ∷ ('u' ∷ ('e' ∷ xs)))) ≡ inj₂ (parsed (B.scalar (B.boolean true)) xs)
  postulate
    falsePrefix : (xs : _) → decodePrefix ('f' ∷ ('a' ∷ ('l' ∷ ('s' ∷ ('e' ∷ xs))))) ≡ inj₂ (parsed (B.scalar (B.boolean false)) xs)
  postulate
    nullPrefix : (xs : _) → decodePrefix ('n' ∷ ('u' ∷ ('l' ∷ ('l' ∷ xs)))) ≡ inj₂ (parsed (B.scalar B.null) xs)
  postulate
    closeQuote : (xs : _) → decodeQuoted ('\"' ∷ xs) ≡ inj₂ (parsed "" xs)
  postulate
    closeArray : (xs : _) → decodeElements (']' ∷ xs) ≡ inj₂ (parsed [] xs)
  postulate
    closeObject : (xs : _) → decodeMembers ('}' ∷ xs) ≡ inj₂ (parsed [] xs)
  postulate
    quotedPrefix : (xs : _) → (s : _) → (rest : _) → (decodeQuoted xs ≡ inj₂ (parsed s rest)) → decodePrefix ('\"' ∷ xs) ≡ inj₂ (parsed (B.scalar (B.text s)) rest)
  postulate
    quotedError : (xs : _) → (e : _) → (decodeQuoted xs ≡ inj₁ e) → decodePrefix ('\"' ∷ xs) ≡ inj₁ e
  postulate
    numericPrefix : (c : _) → (xs : _) → (s : _) → (rest : _) → (((toℕ c ≡ᵇ 45) ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))) ≡ true) → (decodeNumber (c ∷ xs) ≡ inj₂ (parsed s rest)) → decodePrefix (c ∷ xs) ≡ inj₂ (parsed (B.scalar (B.number s)) rest)
  postulate
    numericError : (c : _) → (xs : _) → (e : _) → (((toℕ c ≡ᵇ 45) ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58))) ≡ true) → (decodeNumber (c ∷ xs) ≡ inj₁ e) → decodePrefix (c ∷ xs) ≡ inj₁ e
  postulate
    arrayPrefix : (xs : _) → (vs : _) → (rest : _) → (decodeElements xs ≡ inj₂ (parsed vs rest)) → decodePrefix ('[' ∷ xs) ≡ inj₂ (parsed (B.array vs) rest)
  postulate
    arrayError : (xs : _) → (e : _) → (decodeElements xs ≡ inj₁ e) → decodePrefix ('[' ∷ xs) ≡ inj₁ e
  postulate
    hasKey : String → List (String × B.Value) → Bool
  postulate
    keepLatest : List (String × B.Value) → List (String × B.Value)
  postulate
    hasKeyEmpty : (k : _) → hasKey k [] ≡ false
  postulate
    hasKeySame : (k : _) → (v : _) → (xs : _) → hasKey k ((k , v) ∷ xs) ≡ true
  postulate
    hasKeyOther : (k : _) → (j : _) → (v : _) → (xs : _) → (k ≢ j) → hasKey k ((j , v) ∷ xs) ≡ hasKey k xs
  postulate
    keepLatestEmpty : keepLatest [] ≡ []
  postulate
    keepLatestNext : (k : _) → (v : _) → (xs : _) → keepLatest ((k , v) ∷ xs) ≡ (if hasKey k (keepLatest xs) then keepLatest xs else ((k , v) ∷ keepLatest xs))
  postulate
    objectPrefix : (xs : _) → (kvs : _) → (rest : _) → (decodeMembers xs ≡ inj₂ (parsed kvs rest)) → decodePrefix ('{' ∷ xs) ≡ inj₂ (parsed (B.object (keepLatest kvs)) rest)
  postulate
    objectError : (xs : _) → (e : _) → (decodeMembers xs ≡ inj₁ e) → decodePrefix ('{' ∷ xs) ≡ inj₁ e
  postulate
    canStart : Char → Bool
  postulate
    canContinue : Char → Bool
  postulate
    reservedWords : List (List Char)
  postulate
    reserved : List Char → Bool
  postulate
    identifier : List Char → Bool
  postulate
    asciiStart : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → canStart c ≡ ((toℕ c ≡ᵇ 36) ∨ ((toℕ c ≡ᵇ 95) ∨ (((64 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 91)) ∨ ((96 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 123)))))
  postulate
    asciiContinue : (c : _) → ((toℕ c <ᵇ 128) ≡ true) → canContinue c ≡ (canStart c ∨ ((47 <ᵇ toℕ c) ∧ (toℕ c <ᵇ 58)))
  postulate
    reservedIncluded : (w : _) → Listed w reservedWords → reserved w ≡ true
  postulate
    reservedExcluded : (w : _) → (Listed w reservedWords → ⊥) → reserved w ≡ false
  postulate
    emptyIdentifier : identifier [] ≡ false
  postulate
    identifierForm : (c : _) → (cs : _) → identifier (c ∷ cs) ≡ (canStart c ∧ (all canContinue cs ∧ not (reserved (c ∷ cs))))
  postulate
    observedReservedWords : reservedWords ≡ map toList ("break" ∷ ("case" ∷ ("catch" ∷ ("class" ∷ ("const" ∷ ("continue" ∷ ("debugger" ∷ ("default" ∷ ("delete" ∷ ("do" ∷ ("else" ∷ ("export" ∷ ("extends" ∷ ("false" ∷ ("finally" ∷ ("for" ∷ ("function" ∷ ("if" ∷ ("import" ∷ ("in" ∷ ("instanceof" ∷ ("new" ∷ ("null" ∷ ("return" ∷ ("super" ∷ ("switch" ∷ ("this" ∷ ("throw" ∷ ("true" ∷ ("try" ∷ ("typeof" ∷ ("var" ∷ ("void" ∷ ("while" ∷ ("with" ∷ ("yield" ∷ []))))))))))))))))))))))))))))))))))))
  postulate
    escapeChar : Char → List Char
  postulate
    escapeBody : List Char → List Char
  postulate
    quoteForward : String → String
  postulate
    escapeBodyEmpty : escapeBody [] ≡ []
  postulate
    escapeBodyNext : (c : _) → (cs : _) → escapeBody (c ∷ cs) ≡ (escapeChar c ++ escapeBody cs)
  postulate
    literalChar : (c : _) → ((31 <ᵇ toℕ c) ≡ true) → (((toℕ c <ᵇ 127) ∨ (159 <ᵇ toℕ c)) ≡ true) → (((toℕ c ≡ᵇ 34) ∨ ((toℕ c ≡ᵇ 92) ∨ ((toℕ c ≡ᵇ 8232) ∨ (toℕ c ≡ᵇ 8233)))) ≡ false) → escapeChar c ≡ (c ∷ [])
  postulate
    quoteShape : (s : _) → quoteForward s ≡ fromList ('\"' ∷ (escapeBody (toList s) ++ ('\"' ∷ [])))
  postulate
    csi : String
  postulate
    csiPrefix : csi ≡ fromList (fromℕ 27 ∷ ('[' ∷ []))
  postulate
    paint : Bool → Shade → String → String
  postulate
    paintPlain : (hue : _) → (s : _) → paint false hue s ≡ s
  postulate
    paintName : (s : _) → paint true Shade.name s ≡ (csi ++ˢ ("34;1m" ++ˢ (s ++ˢ (csi ++ˢ "0;22m"))))
  postulate
    paintContainer : (s : _) → paint true Shade.container s ≡ (csi ++ˢ ("35m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  postulate
    paintNumeral : (s : _) → paint true Shade.numeral s ≡ (csi ++ˢ ("31m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  postulate
    paintQuoted : (s : _) → paint true Shade.quoted s ≡ (csi ++ˢ ("33m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  postulate
    paintConstant : (s : _) → paint true Shade.constant s ≡ (csi ++ˢ ("36m" ++ˢ (s ++ˢ (csi ++ˢ "0m"))))
  postulate
    renderPayload : Bool → B.Payload → String
  postulate
    payloadNull : (c : _) → renderPayload c (B.atom B.null) ≡ paint c Shade.constant "null"
  postulate
    payloadTrue : (c : _) → renderPayload c (B.atom (B.boolean true)) ≡ paint c Shade.constant "true"
  postulate
    payloadFalse : (c : _) → renderPayload c (B.atom (B.boolean false)) ≡ paint c Shade.constant "false"
  postulate
    payloadNumber : (c : _) → (n : _) → renderPayload c (B.atom (B.number n)) ≡ paint c Shade.numeral n
  postulate
    payloadText : (c : _) → (s : _) → renderPayload c (B.atom (B.text s)) ≡ paint c Shade.quoted (quoteForward s)
  postulate
    payloadArray : (c : _) → renderPayload c B.arrayMark ≡ paint c Shade.container "[]"
  postulate
    payloadObject : (c : _) → renderPayload c B.objectMark ≡ paint c Shade.container "{}"
  postulate
    assignmentPart : Bool → B.Segment → String
  postulate
    assignmentSuffix : Bool → List B.Segment → String
  postulate
    assignmentDotted : (c : _) → (k : _) → (identifier (toList k) ≡ true) → assignmentPart c (B.property k) ≡ ("." ++ˢ paint c Shade.name k)
  postulate
    assignmentBracketed : (c : _) → (k : _) → (identifier (toList k) ≡ false) → assignmentPart c (B.property k) ≡ (paint c Shade.container "[" ++ˢ (paint c Shade.quoted (quoteForward k) ++ˢ paint c Shade.container "]"))
  postulate
    assignmentIndex : (c : _) → (i : _) → assignmentPart c (B.index i) ≡ (paint c Shade.container "[" ++ˢ (paint c Shade.numeral (Nat.show i) ++ˢ paint c Shade.container "]"))
  postulate
    assignmentSuffixEmpty : (c : _) → assignmentSuffix c [] ≡ ""
  postulate
    assignmentSuffixNext : (c : _) → (p : _) → (ps : _) → assignmentSuffix c (p ∷ ps) ≡ (assignmentPart c p ++ˢ assignmentSuffix c ps)
  postulate
    pairPart : Bool → B.Segment → String
  postulate
    pairParts : Bool → List B.Segment → String
  postulate
    pairProperty : (c : _) → (k : _) → pairPart c (B.property k) ≡ paint c Shade.quoted (quoteForward k)
  postulate
    pairIndex : (c : _) → (i : _) → pairPart c (B.index i) ≡ paint c Shade.numeral (Nat.show i)
  postulate
    pairPartsEmpty : (c : _) → pairParts c [] ≡ ""
  postulate
    pairPartsSingle : (c : _) → (p : _) → pairParts c (p ∷ []) ≡ pairPart c p
  postulate
    pairPartsNext : (c : _) → (p : _) → (q : _) → (ps : _) → pairParts c (p ∷ (q ∷ ps)) ≡ (pairPart c p ++ˢ ("," ++ˢ pairParts c (q ∷ ps)))
  postulate
    renderLine : Notation → Bool → B.Statement → String
  postulate
    renderAssignment : (c : _) → (ps : _) → (r : _) → renderLine Notation.assignments c (B.assignment ps r) ≡ (paint c Shade.name "json" ++ˢ (assignmentSuffix c ps ++ˢ (" = " ++ˢ (renderPayload c r ++ˢ ";\n"))))
  postulate
    renderPair : (c : _) → (ps : _) → (r : _) → renderLine Notation.pairs c (B.assignment ps r) ≡ (paint c Shade.container "[" ++ˢ (paint c Shade.container "[" ++ˢ (pairParts c ps ++ˢ (paint c Shade.container "]" ++ˢ ("," ++ˢ (renderPayload c r ++ˢ (paint c Shade.container "]" ++ˢ "\n")))))))
  postulate
    compareText : List Char → List Char → Ordering
  postulate
    compareEmpty : compareText [] [] ≡ Ordering.equal
  postulate
    compareLeftEmpty : (c : _) → (cs : _) → compareText [] (c ∷ cs) ≡ Ordering.before
  postulate
    compareRightEmpty : (c : _) → (cs : _) → compareText (c ∷ cs) [] ≡ Ordering.after
  postulate
    compareNext : (c : _) → (cs : _) → (d : _) → (ds : _) → compareText (c ∷ cs) (d ∷ ds) ≡ (if (toℕ c <ᵇ toℕ d) then Ordering.before else (if (toℕ d <ᵇ toℕ c) then Ordering.after else compareText cs ds))
  postulate
    insertKey : (String → List Char) → (String × B.Value) → List (String × B.Value) → List (String × B.Value)
  postulate
    orderKeys : (String → List Char) → List (String × B.Value) → List (String × B.Value)
  postulate
    insertEmpty : (rank : _) → (kv : _) → insertKey rank kv [] ≡ (kv ∷ [])
  postulate
    insertBefore : (rank : _) → (k : _) → (v : _) → (j : _) → (w : _) → (xs : _) → (compareText (rank k) (rank j) ≡ Ordering.before) → insertKey rank (k , v) ((j , w) ∷ xs) ≡ ((k , v) ∷ ((j , w) ∷ xs))
  postulate
    insertEqual : (rank : _) → (k : _) → (v : _) → (j : _) → (w : _) → (xs : _) → (compareText (rank k) (rank j) ≡ Ordering.equal) → insertKey rank (k , v) ((j , w) ∷ xs) ≡ ((k , v) ∷ ((j , w) ∷ xs))
  postulate
    insertAfter : (rank : _) → (k : _) → (v : _) → (j : _) → (w : _) → (xs : _) → (compareText (rank k) (rank j) ≡ Ordering.after) → insertKey rank (k , v) ((j , w) ∷ xs) ≡ ((j , w) ∷ insertKey rank (k , v) xs)
  postulate
    orderKeysEmpty : (rank : _) → orderKeys rank [] ≡ []
  postulate
    orderKeysNext : (rank : _) → (kv : _) → (xs : _) → orderKeys rank (kv ∷ xs) ≡ insertKey rank kv (orderKeys rank xs)
  postulate
    arrange : SortMode → B.Value → B.Value
  postulate
    givenOrder : (v : _) → arrange SortMode.given v ≡ v
  postulate
    arrangedScalar : (a : _) → arrange SortMode.sorted (B.scalar a) ≡ B.scalar a
  postulate
    arrangedArray : (vs : _) → arrange SortMode.sorted (B.array vs) ≡ B.array (map (arrange SortMode.sorted) vs)
  postulate
    arrangedObject : (kvs : _) → arrange SortMode.sorted (B.object kvs) ≡ B.object (orderKeys (λ k → toList (assignmentPart false (B.property k))) (map (λ kv → proj₁ kv , arrange SortMode.sorted (proj₂ kv)) kvs))
  postulate
    draw : List B.Segment → Display → List Row
  postulate
    drawLines : (p : _) → (n : _) → (c : _) → (v : _) → draw p (display n c v) ≡ map (λ s → row s (renderLine n c s)) (map Row.statement (draw p (display n c v)))
  postulate
    drawSquare : (p : _) → (d : _) → map Row.statement (draw p d) ≡ B.flatten p (Display.tree d)
  postulate
    renderTree : Config → List B.Segment → B.Value → String
  postulate
    renderTreeLaw : (cfg : _) → (p : _) → (v : _) → renderTree cfg p v ≡ foldr _++ˢ_ "" (map Row.output (draw p (display (Config.notation cfg) (Config.color cfg) (arrange (Config.sorting cfg) v))))
  postulate
    forward : Config → List Char → Report
  postulate
    streamFrom : Config → ℕ → List (List Char) → Report
  postulate
    forwardStream : Config → List (List Char) → Report
  postulate
    forwardGood : (cfg : _) → (xs : _) → (v : _) → (rest : _) → (decodePrefix xs ≡ inj₂ (parsed v rest)) → forward cfg xs ≡ report (renderTree cfg [] v) nothing
  postulate
    forwardBad : (cfg : _) → (xs : _) → (e : _) → (decodePrefix xs ≡ inj₁ e) → forward cfg xs ≡ report "" (just e)
  postulate
    streamDone : (cfg : _) → (i : _) → streamFrom cfg i [] ≡ report "" nothing
  postulate
    streamBad : (cfg : _) → (i : _) → (xs : _) → (xss : _) → (e : _) → (decodePrefix xs ≡ inj₁ e) → streamFrom cfg i (xs ∷ xss) ≡ report "" (just e)
  postulate
    streamNext : (cfg : _) → (i : _) → (xs : _) → (xss : _) → (v : _) → (rest : _) → (out : _) → (issue : _) → (decodePrefix xs ≡ inj₂ (parsed v rest)) → (streamFrom cfg (suc i) xss ≡ report out issue) → streamFrom cfg i (xs ∷ xss) ≡ report (renderTree cfg (B.index i ∷ []) v ++ˢ out) issue
  postulate
    streamRoot : (cfg : _) → (xss : _) → (out : _) → (issue : _) → (streamFrom cfg 0 xss ≡ report out issue) → forwardStream cfg xss ≡ report (renderLine (Config.notation cfg) (Config.color cfg) (B.assignment [] B.arrayMark) ++ˢ out) issue
  postulate
    observedSorted : forward (config Notation.assignments false SortMode.sorted) (toList "{\"-?\":4,\"- \":2,\"-!\":3,\"-\":1,\"a$\":5,\"a\":{\"-?\":6},\"A\":7}") ≡ report "json = {};\njson.A = 7;\njson.a = {};\njson.a[\"-?\"] = 6;\njson.a$ = 5;\njson[\"- \"] = 2;\njson[\"-!\"] = 3;\njson[\"-\"] = 1;\njson[\"-?\"] = 4;\n" nothing
  postulate
    observedEscaping : forward (config Notation.pairs false SortMode.sorted) (toList "{\"x\\u000b\\u2028\\u0085\":\"\\u000b\\u001f\\u007f\\u0085\\u2028\\u2029<&>/\"}") ≡ report "[[],{}]\n[[\"x\\u000B\\u2028\\u0085\"],\"\\u000B\\u001F\\u007F\\u0085\\u2028\\u2029<&>/\"]\n" nothing
  postulate
    observedDuplicate : forward (config Notation.assignments false SortMode.sorted) (toList "{\"a\":1,\"\\u0061\":{\"z\":3},\"b\":2}") ≡ report "json = {};\njson.a = {};\njson.a.z = 3;\njson.b = 2;\n" nothing
  postulate
    observedMalformedDuplicate : forward (config Notation.assignments false SortMode.sorted) (toList "{\"a\":1,\"\\u0061\":nulx}") ≡ report "" (just "invalid character 'x' in literal null (expecting 'l')")
  postulate
    observedSeed : forward (config Notation.assignments false SortMode.sorted) (toList "[\"λ<&>\\u2028\",{}]") ≡ report "json = [];\njson[0] = \"λ<&>\\u2028\";\njson[1] = {};\n" nothing
  postulate
    observedNumber : forward (config Notation.assignments false SortMode.sorted) (toList "-94.00e+2") ≡ report "json = -94.00e+2;\n" nothing
  postulate
    observedStreamPrefix : forwardStream (config Notation.pairs false SortMode.sorted) (toList " 12xyz" ∷ (toList "true false" ∷ [])) ≡ report "[[],[]]\n[[0],12]\n[[1],true]\n" nothing
  postulate
    observedStreamBlank : forwardStream (config Notation.assignments false SortMode.sorted) (toList "true" ∷ ([] ∷ (toList "false" ∷ []))) ≡ report "json = [];\njson[0] = true;\n" (just "EOF")
  postulate
    observedColor : renderLine Notation.pairs true (B.assignment [] (B.atom (B.boolean true))) ≡ (csi ++ˢ ("35m[" ++ˢ (csi ++ˢ ("0m" ++ˢ (csi ++ˢ ("35m[" ++ˢ (csi ++ˢ ("0m" ++ˢ (csi ++ˢ ("35m]" ++ˢ (csi ++ˢ ("0m," ++ˢ (csi ++ˢ ("36mtrue" ++ˢ (csi ++ˢ ("0m" ++ˢ (csi ++ˢ ("35m]" ++ˢ (csi ++ˢ "0m\n")))))))))))))))))))
