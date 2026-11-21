module Gen.T1.Render where

  open import Agda.Builtin.Nat using (div-helper; mod-helper)
  open import Agda.Builtin.String using (primShowNat)
  open import Data.Bool using (Bool; false; true)
  open import Data.Char using (Char; fromℕ; toℕ)
  open import Data.List using (List; []; _∷_; [_]; _++_; any; map)
  open import Data.Maybe using (Maybe)
  open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_)
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.String using (String; fromList; toList)
  open import Data.String.Properties using (_≟_)
  open import Data.Sum using (_⊎_)
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
  open import Relation.Nullary.Decidable using (isYes)
  import Gen.T0.Gron as Base
  data Style : Set where
    plain : Style
    ansi : Style
  styleBit : Style → Bool
  styleBit Style.plain = false
  styleBit Style.ansi = true
  data Tone : Set where
    violet : Tone
    red : Tone
    yellow : Tone
    cyan : Tone
    blueBold : Tone
    bold : Tone
    green : Tone
  data Quoting : Set where
    forwardQuote : Quoting
    reverseQuote : Quoting
  data KeyForm : Set where
    dotted : KeyForm
    bracketed : KeyForm
  data Comparison : Set where
    before : Comparison
    equal : Comparison
    after : Comparison
  data Permutation {A : Set} : List A → List A → Set where
    permutation-refl : {xs : _} → Permutation xs xs
    permutation-keep : {x xs ys : _} → Permutation xs ys → Permutation (x ∷ xs) (x ∷ ys)
    permutation-swap : {x y xs : _} → Permutation (x ∷ (y ∷ xs)) (y ∷ (x ∷ xs))
    permutation-trans : {xs ys zs : _} → Permutation xs ys → Permutation ys zs → Permutation xs zs
  data Ordered {A : Set} (compare : A → A → Comparison) : List A → Set where
    ordered-empty : Ordered compare []
    ordered-single : (x : _) → Ordered compare (x ∷ [])
    ordered-next : {x y ys : _} → (compare x y ≢ Comparison.after) → Ordered compare (y ∷ ys) → Ordered compare (x ∷ (y ∷ ys))
  data RowFormat : Set where
    assignments : RowFormat
    jsonRows : RowFormat
  postulate
    resolveStyle : Bool → Bool → Bool → Style
  postulate
    style-square : (tty : _) → (forced : _) → (mono : _) → styleBit (resolveStyle tty forced mono) ≡ Base.useColor tty forced mono
  postulate
    paint : Style → Tone → List Char → List Char
  postulate
    paint-plain : (tone : _) → (body : _) → paint Style.plain tone body ≡ body
  postulate
    paint-violet : (body : _) → paint Style.ansi Tone.violet body ≡ ((fromℕ 27 ∷ toList "[35m") ++ (body ++ (fromℕ 27 ∷ toList "[0m")))
  postulate
    paint-red : (body : _) → paint Style.ansi Tone.red body ≡ ((fromℕ 27 ∷ toList "[31m") ++ (body ++ (fromℕ 27 ∷ toList "[0m")))
  postulate
    paint-yellow : (body : _) → paint Style.ansi Tone.yellow body ≡ ((fromℕ 27 ∷ toList "[33m") ++ (body ++ (fromℕ 27 ∷ toList "[0m")))
  postulate
    paint-cyan : (body : _) → paint Style.ansi Tone.cyan body ≡ ((fromℕ 27 ∷ toList "[36m") ++ (body ++ (fromℕ 27 ∷ toList "[0m")))
  postulate
    paint-blue : (body : _) → paint Style.ansi Tone.blueBold body ≡ ((fromℕ 27 ∷ toList "[34;1m") ++ (body ++ (fromℕ 27 ∷ toList "[0;22m")))
  postulate
    paint-bold : (body : _) → paint Style.ansi Tone.bold body ≡ ((fromℕ 27 ∷ toList "[1m") ++ (body ++ (fromℕ 27 ∷ toList "[22m")))
  postulate
    paint-green : (body : _) → paint Style.ansi Tone.green body ≡ ((fromℕ 27 ∷ toList "[32m") ++ (body ++ (fromℕ 27 ∷ toList "[0m")))
  postulate
    hexDigit : Quoting → ℕ → Char
  postulate
    escapeCode : Quoting → ℕ → List Char
  postulate
    escapeChar : Quoting → Char → List Char
  postulate
    escapeBody : Quoting → List Char → List Char
  postulate
    quoted : Quoting → List Char → List Char
  postulate
    digit-decimal : (q : _) → (n : _) → (n < 10) → toℕ (hexDigit q n) ≡ (n + 48)
  postulate
    digit-uppercase : (n : _) → (10 ≤ n) → (n < 16) → toℕ (hexDigit Quoting.forwardQuote n) ≡ (n + 55)
  postulate
    digit-lowercase : (n : _) → (10 ≤ n) → (n < 16) → toℕ (hexDigit Quoting.reverseQuote n) ≡ (n + 87)
  postulate
    unicode-escape : (q : _) → (n : _) → (n < 65536) → escapeCode q n ≡ ('\\' ∷ ('u' ∷ (hexDigit q (div-helper 0 4095 n 4095) ∷ (hexDigit q (mod-helper 0 15 (div-helper 0 255 n 255) 15) ∷ (hexDigit q (mod-helper 0 15 (div-helper 0 15 n 15) 15) ∷ (hexDigit q (mod-helper 0 15 n 15) ∷ []))))))
  postulate
    escape-quote : (q : _) → escapeChar q '\"' ≡ toList "\\\""
  postulate
    escape-backslash : (q : _) → escapeChar q '\\' ≡ toList "\\\\"
  postulate
    escape-backspace : (q : _) → escapeChar q (fromℕ 8) ≡ toList "\\b"
  postulate
    escape-tab : (q : _) → escapeChar q (fromℕ 9) ≡ toList "\\t"
  postulate
    escape-newline : (q : _) → escapeChar q '\n' ≡ toList "\\n"
  postulate
    escape-formfeed : (q : _) → escapeChar q (fromℕ 12) ≡ toList "\\f"
  postulate
    escape-return : (q : _) → escapeChar q (fromℕ 13) ≡ toList "\\r"
  postulate
    escape-c0 : (q : _) → (c : _) → (toℕ c < 32) → (toℕ c ≢ 8) → (toℕ c ≢ 9) → (toℕ c ≢ 10) → (toℕ c ≢ 12) → (toℕ c ≢ 13) → escapeChar q c ≡ escapeCode q (toℕ c)
  postulate
    escape-forward-c1 : (c : _) → (127 ≤ toℕ c) → (toℕ c < 160) → escapeChar Quoting.forwardQuote c ≡ escapeCode Quoting.forwardQuote (toℕ c)
  postulate
    escape-line-separator : (q : _) → (c : _) → (toℕ c ≡ 8232) → escapeChar q c ≡ escapeCode q (toℕ c)
  postulate
    escape-paragraph-separator : (q : _) → (c : _) → (toℕ c ≡ 8233) → escapeChar q c ≡ escapeCode q (toℕ c)
  postulate
    escape-forward-ascii : (c : _) → (32 ≤ toℕ c) → (toℕ c < 127) → (toℕ c ≢ 34) → (toℕ c ≢ 92) → escapeChar Quoting.forwardQuote c ≡ ([ c ])
  postulate
    escape-forward-unicode : (c : _) → (160 ≤ toℕ c) → (toℕ c ≢ 8232) → (toℕ c ≢ 8233) → escapeChar Quoting.forwardQuote c ≡ ([ c ])
  postulate
    escape-reverse-literal : (c : _) → (32 ≤ toℕ c) → (toℕ c ≢ 34) → (toℕ c ≢ 92) → (toℕ c ≢ 8232) → (toℕ c ≢ 8233) → escapeChar Quoting.reverseQuote c ≡ ([ c ])
  postulate
    escape-empty : (q : _) → escapeBody q [] ≡ []
  postulate
    escape-cons : (q : _) → (c : _) → (cs : _) → escapeBody q (c ∷ cs) ≡ (escapeChar q c ++ escapeBody q cs)
  postulate
    quote-body : (q : _) → (cs : _) → quoted q cs ≡ ('\"' ∷ (escapeBody q cs ++ ([ '\"' ])))
  postulate
    identifierStart : Char → Bool
  postulate
    identifierRest : Char → Bool
  postulate
    identifierTail : List Char → Bool
  postulate
    identifier : List Char → Bool
  postulate
    reserved : String → Bool
  postulate
    keyForm : String → KeyForm
  postulate
    start-dollar : identifierStart '$' ≡ true
  postulate
    start-underscore : identifierStart '_' ≡ true
  postulate
    start-uppercase : (c : _) → (65 ≤ toℕ c) → (toℕ c < 91) → identifierStart c ≡ true
  postulate
    start-lowercase : (c : _) → (97 ≤ toℕ c) → (toℕ c < 123) → identifierStart c ≡ true
  postulate
    start-ascii-other : (c : _) → (toℕ c < 128) → ((toℕ c < 65) ⊎ (90 < toℕ c)) → ((toℕ c < 97) ⊎ (122 < toℕ c)) → (toℕ c ≢ 36) → (toℕ c ≢ 95) → identifierStart c ≡ false
  postulate
    rest-start : (c : _) → (identifierStart c ≡ true) → identifierRest c ≡ true
  postulate
    rest-digit : (c : _) → (48 ≤ toℕ c) → (toℕ c < 58) → identifierRest c ≡ true
  postulate
    rest-ascii-other : (c : _) → (toℕ c < 128) → (identifierStart c ≡ false) → ((toℕ c < 48) ⊎ (57 < toℕ c)) → identifierRest c ≡ false
  postulate
    tail-empty : identifierTail [] ≡ true
  postulate
    tail-reject : (c : _) → (cs : _) → (identifierRest c ≡ false) → identifierTail (c ∷ cs) ≡ false
  postulate
    tail-accept : (c : _) → (cs : _) → (identifierRest c ≡ true) → identifierTail (c ∷ cs) ≡ identifierTail cs
  postulate
    identifier-empty : identifier [] ≡ false
  postulate
    identifier-reject : (c : _) → (cs : _) → (identifierStart c ≡ false) → identifier (c ∷ cs) ≡ false
  postulate
    identifier-accept : (c : _) → (cs : _) → (identifierStart c ≡ true) → identifier (c ∷ cs) ≡ identifierTail cs
  postulate
    reserved-words : (s : _) → reserved s ≡ any (λ word → isYes (s ≟ word)) ("break" ∷ ("case" ∷ ("catch" ∷ ("class" ∷ ("const" ∷ ("continue" ∷ ("debugger" ∷ ("default" ∷ ("delete" ∷ ("do" ∷ ("else" ∷ ("export" ∷ ("extends" ∷ ("false" ∷ ("finally" ∷ ("for" ∷ ("function" ∷ ("if" ∷ ("import" ∷ ("in" ∷ ("instanceof" ∷ ("new" ∷ ("null" ∷ ("return" ∷ ("super" ∷ ("switch" ∷ ("this" ∷ ("throw" ∷ ("true" ∷ ("try" ∷ ("typeof" ∷ ("var" ∷ ("void" ∷ ("while" ∷ ("with" ∷ ("yield" ∷ []))))))))))))))))))))))))))))))))))))
  postulate
    dotted-key : (k : _) → (identifier (toList k) ≡ true) → (reserved k ≡ false) → keyForm k ≡ KeyForm.dotted
  postulate
    invalid-key : (k : _) → (identifier (toList k) ≡ false) → keyForm k ≡ KeyForm.bracketed
  postulate
    reserved-key : (k : _) → (reserved k ≡ true) → keyForm k ≡ KeyForm.bracketed
  postulate
    observed-non-ascii-letters : map keyForm ("α" ∷ ("漢" ∷ ("𐐀" ∷ ("Ⅷ" ∷ [])))) ≡ (KeyForm.dotted ∷ (KeyForm.dotted ∷ (KeyForm.dotted ∷ (KeyForm.dotted ∷ []))))
  postulate
    observed-non-ascii-tail : map keyForm ("á" ∷ ("a٢" ∷ ("a‿" ∷ ("aⅧ" ∷ [])))) ≡ (KeyForm.dotted ∷ (KeyForm.dotted ∷ (KeyForm.dotted ∷ (KeyForm.dotted ∷ []))))
  postulate
    observed-non-ascii-exclusions : map keyForm ("a²" ∷ ("a·" ∷ ("a‌" ∷ ("a‍" ∷ ("℘" ∷ ("℮" ∷ ("゛" ∷ ("٢a" ∷ ("😀" ∷ []))))))))) ≡ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ (KeyForm.bracketed ∷ [])))))))))
  postulate
    compareText : List Char → List Char → Comparison
  postulate
    compareSegment : Base.Segment → Base.Segment → Comparison
  postulate
    comparePath : List Base.Segment → List Base.Segment → Comparison
  postulate
    text-empty : compareText [] [] ≡ Comparison.equal
  postulate
    text-prefix : (c : _) → (cs : _) → compareText [] (c ∷ cs) ≡ Comparison.before
  postulate
    text-extension : (c : _) → (cs : _) → compareText (c ∷ cs) [] ≡ Comparison.after
  postulate
    text-before : (c : _) → (d : _) → (cs : _) → (ds : _) → (toℕ c < toℕ d) → compareText (c ∷ cs) (d ∷ ds) ≡ Comparison.before
  postulate
    text-after : (c : _) → (d : _) → (cs : _) → (ds : _) → (toℕ d < toℕ c) → compareText (c ∷ cs) (d ∷ ds) ≡ Comparison.after
  postulate
    text-equal-head : (c : _) → (d : _) → (cs : _) → (ds : _) → (toℕ c ≡ toℕ d) → compareText (c ∷ cs) (d ∷ ds) ≡ compareText cs ds
  postulate
    segment-index-before : (i : _) → (j : _) → (i < j) → compareSegment (Base.index i) (Base.index j) ≡ Comparison.before
  postulate
    segment-index-after : (i : _) → (j : _) → (j < i) → compareSegment (Base.index i) (Base.index j) ≡ Comparison.after
  postulate
    segment-index-equal : (i : _) → compareSegment (Base.index i) (Base.index i) ≡ Comparison.equal
  postulate
    segment-dotted-before : (k : _) → (l : _) → (keyForm k ≡ KeyForm.dotted) → (keyForm l ≡ KeyForm.bracketed) → compareSegment (Base.key k) (Base.key l) ≡ Comparison.before
  postulate
    segment-dotted-after : (k : _) → (l : _) → (keyForm k ≡ KeyForm.bracketed) → (keyForm l ≡ KeyForm.dotted) → compareSegment (Base.key k) (Base.key l) ≡ Comparison.after
  postulate
    segment-dotted-pair : (k : _) → (l : _) → (keyForm k ≡ KeyForm.dotted) → (keyForm l ≡ KeyForm.dotted) → compareSegment (Base.key k) (Base.key l) ≡ compareText (toList k) (toList l)
  postulate
    segment-bracket-pair : (k : _) → (l : _) → (keyForm k ≡ KeyForm.bracketed) → (keyForm l ≡ KeyForm.bracketed) → compareSegment (Base.key k) (Base.key l) ≡ compareText (quoted Quoting.forwardQuote (toList k)) (quoted Quoting.forwardQuote (toList l))
  postulate
    path-empty : comparePath [] [] ≡ Comparison.equal
  postulate
    path-prefix : (seg : _) → (path : _) → comparePath [] (seg ∷ path) ≡ Comparison.before
  postulate
    path-extension : (seg : _) → (path : _) → comparePath (seg ∷ path) [] ≡ Comparison.after
  postulate
    path-head-before : (x : _) → (y : _) → (xs : _) → (ys : _) → (compareSegment x y ≡ Comparison.before) → comparePath (x ∷ xs) (y ∷ ys) ≡ Comparison.before
  postulate
    path-head-after : (x : _) → (y : _) → (xs : _) → (ys : _) → (compareSegment x y ≡ Comparison.after) → comparePath (x ∷ xs) (y ∷ ys) ≡ Comparison.after
  postulate
    path-head-equal : (x : _) → (y : _) → (xs : _) → (ys : _) → (compareSegment x y ≡ Comparison.equal) → comparePath (x ∷ xs) (y ∷ ys) ≡ comparePath xs ys
  postulate
    compareRow : Base.Row → Base.Row → Comparison
  postulate
    row-order : (p : _) → (q : _) → (c : _) → (d : _) → compareRow (Base.row p c) (Base.row q d) ≡ comparePath p q
  postulate
    orderRows : List Base.Row → List Base.Row
  postulate
    orderMembers : List (String × List Char) → List (String × List Char)
  postulate
    rows-preserved : (rs : _) → Permutation rs (orderRows rs)
  postulate
    rows-ordered : (rs : _) → Ordered compareRow (orderRows rs)
  postulate
    members-preserved : (fs : _) → Permutation fs (orderMembers fs)
  postulate
    members-ordered : (fs : _) → Ordered (λ f g → compareText (toList (proj₁ f)) (toList (proj₁ g))) (orderMembers fs)
  postulate
    join : List Char → List (List Char) → List Char
  postulate
    join-empty : (sep : _) → join sep [] ≡ []
  postulate
    join-single : (sep : _) → (x : _) → join sep (x ∷ []) ≡ x
  postulate
    join-next : (sep : _) → (x : _) → (y : _) → (ys : _) → join sep (x ∷ (y ∷ ys)) ≡ (x ++ (sep ++ join sep (y ∷ ys)))
  postulate
    assignmentStep : Style → Base.Segment → List Char
  postulate
    assignmentSuffix : Style → List Base.Segment → List Char
  postulate
    jsonPathPart : Style → Base.Segment → List Char
  postulate
    forwardCell : Style → Base.Cell → List Char
  postulate
    forwardLine : Style → RowFormat → Base.Row → List Char
  postulate
    forwardOutput : Style → RowFormat → Bool → List Base.Row → String
  postulate
    assignment-key-dot : (s : _) → (k : _) → (keyForm k ≡ KeyForm.dotted) → assignmentStep s (Base.key k) ≡ ('.' ∷ paint s Tone.blueBold (toList k))
  postulate
    assignment-key-bracket : (s : _) → (k : _) → (keyForm k ≡ KeyForm.bracketed) → assignmentStep s (Base.key k) ≡ (paint s Tone.violet ([ '[' ]) ++ (paint s Tone.yellow (quoted Quoting.forwardQuote (toList k)) ++ paint s Tone.violet ([ ']' ])))
  postulate
    assignment-index : (s : _) → (i : _) → assignmentStep s (Base.index i) ≡ (paint s Tone.violet ([ '[' ]) ++ (paint s Tone.red (toList (primShowNat i)) ++ paint s Tone.violet ([ ']' ])))
  postulate
    suffix-empty : (s : _) → assignmentSuffix s [] ≡ []
  postulate
    suffix-cons : (s : _) → (x : _) → (xs : _) → assignmentSuffix s (x ∷ xs) ≡ (assignmentStep s x ++ assignmentSuffix s xs)
  postulate
    row-key-part : (s : _) → (k : _) → jsonPathPart s (Base.key k) ≡ paint s Tone.yellow (quoted Quoting.forwardQuote (toList k))
  postulate
    row-index-part : (s : _) → (i : _) → jsonPathPart s (Base.index i) ≡ paint s Tone.red (toList (primShowNat i))
  postulate
    forward-object-cell : (s : _) → forwardCell s Base.objectCell ≡ paint s Tone.violet (toList "{}")
  postulate
    forward-array-cell : (s : _) → forwardCell s Base.arrayCell ≡ paint s Tone.violet (toList "[]")
  postulate
    forward-null : (s : _) → forwardCell s (Base.leaf Base.null) ≡ paint s Tone.cyan (toList "null")
  postulate
    forward-true : (s : _) → forwardCell s (Base.leaf (Base.truth true)) ≡ paint s Tone.cyan (toList "true")
  postulate
    forward-false : (s : _) → forwardCell s (Base.leaf (Base.truth false)) ≡ paint s Tone.cyan (toList "false")
  postulate
    forward-number : (s : _) → (n : _) → forwardCell s (Base.leaf (Base.numeral n)) ≡ paint s Tone.red (toList n)
  postulate
    forward-text : (s : _) → (t : _) → forwardCell s (Base.leaf (Base.text t)) ≡ paint s Tone.yellow (quoted Quoting.forwardQuote (toList t))
  postulate
    assignment-line : (s : _) → (p : _) → (c : _) → forwardLine s RowFormat.assignments (Base.row p c) ≡ (paint s Tone.blueBold (toList "json") ++ (assignmentSuffix s p ++ (toList " = " ++ (forwardCell s c ++ toList ";\n"))))
  postulate
    json-row-line : (s : _) → (p : _) → (c : _) → forwardLine s RowFormat.jsonRows (Base.row p c) ≡ (paint s Tone.violet ([ '[' ]) ++ (paint s Tone.violet ([ '[' ]) ++ (join ([ ',' ]) (map (jsonPathPart s) p) ++ (paint s Tone.violet ([ ']' ]) ++ (([ ',' ]) ++ (forwardCell s c ++ (paint s Tone.violet ([ ']' ]) ++ ([ '\n' ]))))))))
  postulate
    output-unsorted : (s : _) → (f : _) → (rs : _) → forwardOutput s f false rs ≡ fromList (join [] (map (forwardLine s f) rs))
  postulate
    output-sorted : (s : _) → (f : _) → (rs : _) → forwardOutput s f true rs ≡ fromList (join [] (map (forwardLine s f) (orderRows rs)))
  postulate
    indent : ℕ → List Char
  postulate
    reverseEntry : Style → String → List Char → List Char
  postulate
    reverseGroup : Style → ℕ → Char → Char → List (List Char) → List Char
  postulate
    reverseValue : Style → ℕ → Base.Value → List Char
  postulate
    reverseOutput : Style → Base.Value → String
  postulate
    mergeDiagnostic : Base.MergeFault → String
  postulate
    indent-root : indent zero ≡ []
  postulate
    indent-next : (depth : _) → indent (suc depth) ≡ (' ' ∷ (' ' ∷ indent depth))
  postulate
    reverse-empty-group : (depth : _) → (l : _) → (r : _) → reverseGroup Style.plain depth l r [] ≡ (l ∷ (r ∷ []))
  postulate
    reverse-pretty-group : (depth : _) → (l : _) → (r : _) → (v : _) → (vs : _) → reverseGroup Style.plain depth l r (v ∷ vs) ≡ ((l ∷ ('\n' ∷ indent (suc depth))) ++ (join (',' ∷ ('\n' ∷ indent (suc depth))) (v ∷ vs) ++ (('\n' ∷ indent depth) ++ ([ r ]))))
  postulate
    reverse-ansi-group : (depth : _) → (l : _) → (r : _) → (vs : _) → reverseGroup Style.ansi depth l r vs ≡ (paint Style.ansi Tone.violet ([ l ]) ++ (join (paint Style.ansi Tone.bold ([ ',' ])) vs ++ paint Style.ansi Tone.violet ([ r ])))
  postulate
    reverse-plain-entry : (k : _) → (v : _) → reverseEntry Style.plain k v ≡ (quoted Quoting.reverseQuote (toList k) ++ (toList ": " ++ v))
  postulate
    reverse-ansi-entry : (k : _) → (v : _) → reverseEntry Style.ansi k v ≡ (paint Style.ansi Tone.blueBold ([ '\"' ]) ++ (paint Style.ansi Tone.blueBold (escapeBody Quoting.reverseQuote (toList k)) ++ (paint Style.ansi Tone.blueBold ([ '\"' ]) ++ (paint Style.ansi Tone.bold ([ ':' ]) ++ v))))
  postulate
    reverse-null : (s : _) → (depth : _) → reverseValue s depth (Base.scalar Base.null) ≡ paint s Tone.cyan (toList "null")
  postulate
    reverse-true : (s : _) → (depth : _) → reverseValue s depth (Base.scalar (Base.truth true)) ≡ paint s Tone.cyan (toList "true")
  postulate
    reverse-false : (s : _) → (depth : _) → reverseValue s depth (Base.scalar (Base.truth false)) ≡ paint s Tone.cyan (toList "false")
  postulate
    reverse-number : (s : _) → (depth : _) → (n : _) → reverseValue s depth (Base.scalar (Base.numeral n)) ≡ paint s Tone.red (toList n)
  postulate
    reverse-plain-text : (depth : _) → (t : _) → reverseValue Style.plain depth (Base.scalar (Base.text t)) ≡ quoted Quoting.reverseQuote (toList t)
  postulate
    reverse-ansi-text : (depth : _) → (t : _) → reverseValue Style.ansi depth (Base.scalar (Base.text t)) ≡ (paint Style.ansi Tone.green ([ '\"' ]) ++ (paint Style.ansi Tone.yellow (escapeBody Quoting.reverseQuote (toList t)) ++ paint Style.ansi Tone.green ([ '\"' ])))
  postulate
    reverse-array : (s : _) → (depth : _) → (xs : _) → reverseValue s depth (Base.array xs) ≡ reverseGroup s depth '[' ']' (map (reverseValue s (suc depth)) xs)
  postulate
    reverse-object : (s : _) → (depth : _) → (fs : _) → reverseValue s depth (Base.object fs) ≡ reverseGroup s depth '{' '}' (map (λ f → reverseEntry s (proj₁ f) (proj₂ f)) (orderMembers (map (λ f → proj₁ f , reverseValue s (suc depth) (proj₂ f)) fs)))
  postulate
    reverse-newline : (s : _) → (v : _) → reverseOutput s v ≡ fromList (reverseValue s zero v ++ ([ '\n' ]))
  postulate
    object-conflict : mergeDiagnostic Base.objectConflict ≡ "failed to merge statements: cannot merge object with non-object\n"
  postulate
    array-conflict : mergeDiagnostic Base.arrayConflict ≡ "failed to merge statements: cannot merge array with non-array\n"
  postulate
    valueText : Base.Atom → List Char
  postulate
    valuesOutput : List (Maybe Base.Row) → String
  postulate
    values-null : valueText Base.null ≡ toList "null"
  postulate
    values-true : valueText (Base.truth true) ≡ toList "true"
  postulate
    values-false : valueText (Base.truth false) ≡ toList "false"
  postulate
    values-number : (n : _) → valueText (Base.numeral n) ≡ toList n
  postulate
    values-text : (t : _) → valueText (Base.text t) ≡ toList t
  postulate
    output-values : (rs : _) → valuesOutput rs ≡ fromList (join [] (map (λ a → valueText a ++ ([ '\n' ])) (Base.valuesOf rs)))
  postulate
    observed-forward-paths : forwardOutput Style.plain RowFormat.jsonRows true (Base.row [] Base.objectCell ∷ (Base.row (Base.key "a.b" ∷ []) (Base.leaf Base.null) ∷ (Base.row (Base.key "z" ∷ []) Base.arrayCell ∷ (Base.row (Base.key "z" ∷ (Base.index 0 ∷ [])) (Base.leaf (Base.numeral "1")) ∷ (Base.row (Base.key "z" ∷ (Base.index 1 ∷ [])) (Base.leaf (Base.text "<&>")) ∷ []))))) ≡ "[[],{}]\n[[\"z\"],[]]\n[[\"z\",0],1]\n[[\"z\",1],\"<&>\"]\n[[\"a.b\"],null]\n"
  postulate
    observed-reverse-members : reverseOutput Style.plain (Base.object (("a" , Base.scalar (Base.numeral "1000000000")) ∷ (("A" , Base.scalar (Base.truth false)) ∷ (("<&>" , Base.scalar (Base.text (fromList ('x' ∷ (fromℕ 8232 ∷ ('y' ∷ (fromℕ 8233 ∷ ('z' ∷ (fromℕ 1 ∷ []))))))))) ∷ [])))) ≡ "{\n  \"<&>\": \"x\\u2028y\\u2029z\\u0001\",\n  \"A\": false,\n  \"a\": 1000000000\n}\n"
  postulate
    observed-quoted-order : compareSegment (Base.key ". ") (Base.key ".") ≡ Comparison.before
  postulate
    observed-forward-quote : fromList (quoted Quoting.forwardQuote (toList "<>&" ++ (fromℕ 127 ∷ (fromℕ 8233 ∷ (fromℕ 31 ∷ toList "/\"\\😀"))))) ≡ "\"<>&\\u007F\\u2029\\u001F/\\\"\\\\😀\""
  postulate
    observed-reverse-quote : quoted Quoting.reverseQuote (fromℕ 11 ∷ (fromℕ 31 ∷ (fromℕ 127 ∷ (fromℕ 133 ∷ (fromℕ 8232 ∷ (fromℕ 8233 ∷ toList "<>&")))))) ≡ (toList "\"\\u000b\\u001f" ++ (fromℕ 127 ∷ (fromℕ 133 ∷ toList "\\u2028\\u2029<>&\"")))
  postulate
    observed-json-color : forwardLine Style.ansi RowFormat.jsonRows (Base.row (Base.key "x" ∷ []) (Base.leaf (Base.numeral "1"))) ≡ ((fromℕ 27 ∷ toList "[35m[") ++ ((fromℕ 27 ∷ toList "[0m") ++ ((fromℕ 27 ∷ toList "[35m[") ++ ((fromℕ 27 ∷ toList "[0m") ++ ((fromℕ 27 ∷ toList "[33m\"x\"") ++ ((fromℕ 27 ∷ toList "[0m") ++ ((fromℕ 27 ∷ toList "[35m]") ++ ((fromℕ 27 ∷ toList "[0m,") ++ ((fromℕ 27 ∷ toList "[31m1") ++ ((fromℕ 27 ∷ toList "[0m") ++ ((fromℕ 27 ∷ toList "[35m]") ++ (fromℕ 27 ∷ toList "[0m\n"))))))))))))
  postulate
    observed-empty-color : reverseOutput Style.ansi (Base.scalar (Base.text "")) ≡ fromList ((fromℕ 27 ∷ toList "[32m\"") ++ ((fromℕ 27 ∷ toList "[0m") ++ ((fromℕ 27 ∷ toList "[33m") ++ ((fromℕ 27 ∷ toList "[0m") ++ ((fromℕ 27 ∷ toList "[32m\"") ++ (fromℕ 27 ∷ toList "[0m\n"))))))
