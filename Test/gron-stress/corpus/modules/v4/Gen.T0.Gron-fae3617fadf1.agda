module Gen.T0.Gron where

open import Agda.Builtin.Char using (primNatToChar)
open import Data.Bool using (Bool; false; true; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; _++_; concatMap; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<ᵇ_; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String; toList; fromList; _≟_) renaming (_++_ to _++ˢ_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

data Atom : Set where
  null : Atom
  boolean : Bool → Atom
  number : String → Atom
  text : String → Atom

data Value : Set where
  scalar : Atom → Value
  object : List (String × Value) → Value
  array : List Value → Value

data Step : Set where
  fieldName : String → Step
  index : ℕ → Step

data BindingValue : Set where
  literal : Atom → BindingValue
  objectMarker : BindingValue
  arrayMarker : BindingValue

record Binding : Set where
  constructor binding
  field
    path : List Step
    rhs : BindingValue

data Parsed (A : Set) : Set where
  parsed : A → Parsed A
  rejected : String → Parsed A

record Reply (A : Set) : Set where
  constructor reply
  field
    status : ℕ
    output : A
    diagnostic : String

data Operation : Set where
  transform : Operation
  extract : Operation
  reconstruct : Operation

data Shortcut : Set where
  requestHelp : Shortcut
  requestVersion : Shortcut
  invalidOption : String → Shortcut
  openError : String → Shortcut

data Failure : Set where
  cannotOpen : Failure
  cannotRead : Failure
  cannotForm : Failure
  cannotFetch : Failure
  cannotParse : Failure
  cannotEncode : Failure

data Traversal : Set where
  enumerated : Traversal
  byAccess : (String → String) → Traversal

data Capture : Set where
  skipped : Capture
  captured : BindingValue → Capture
  rawValue : String → Capture

data Tint : Set where
  identifier : Tint
  delimiter : Tint
  numberToken : Tint
  keyword : Tint
  stringToken : Tint
  colon : Tint
  plain : Tint

operation : Bool → Bool → Operation
operation true  _     = reconstruct
operation false true  = extract
operation false false = transform

chooseReconstruct : (values : _) → operation true values ≡ reconstruct
chooseReconstruct values = refl

chooseExtract : operation false true ≡ extract
chooseExtract = refl

chooseTransform : operation false false ≡ transform
chooseTransform = refl

useColour : Bool → Bool → Bool → Bool
useColour true  _     _        = true
useColour false true  _        = false
useColour false false eligible = eligible

forcedColour : (mono : _) → (eligible : _) → useColour true mono eligible ≡ true
forcedColour mono eligible = refl

forceMonochrome : (eligible : _) → useColour false true eligible ≡ false
forceMonochrome eligible = refl

automaticColour : (eligible : _) → useColour false false eligible ≡ eligible
automaticColour eligible = refl

code : Failure → ℕ
code cannotOpen   = 1
code cannotRead   = 2
code cannotForm   = 3
code cannotFetch  = 4
code cannotParse  = 5
code cannotEncode = 6

openCode : code cannotOpen ≡ 1
openCode = refl

readCode : code cannotRead ≡ 2
readCode = refl

formCode : code cannotForm ≡ 3
formCode = refl

fetchCode : code cannotFetch ≡ 4
fetchCode = refl

parseCode : code cannotParse ≡ 5
parseCode = refl

encodeCode : code cannotEncode ≡ 6
encodeCode = refl

helpText : String
helpText =
  "Transform JSON (from a file, URL, or stdin) into discrete assignments to make it greppable\n\n" ++ˢ
  ("Usage:\n  gron [OPTIONS] [FILE|URL|-]\n\n" ++ˢ
  ("Options:\n" ++ˢ
  ("  -u, --ungron     Reverse the operation (turn assignments back into JSON)\n" ++ˢ
  ("  -v, --values     Print just the values of provided assignments\n" ++ˢ
  ("  -c, --colorize   Colorize output (default on tty)\n" ++ˢ
  ("  -m, --monochrome Monochrome (don't colorize output)\n" ++ˢ
  ("  -s, --stream     Treat each line of input as a separate JSON object\n" ++ˢ
  ("  -k, --insecure   Disable certificate validation\n" ++ˢ
  ("  -x, --proxy      Set proxy configuration\n" ++ˢ
  ("      --noproxy    Comma-separated list of hosts for which not to use a proxy, if one is specified.\n" ++ˢ
  ("  -j, --json       Represent gron data as JSON stream\n" ++ˢ
  ("      --no-sort    Don't sort output (faster)\n" ++ˢ
  ("      --version    Print version information\n\n" ++ˢ
  ("Exit Codes:\n" ++ˢ
  ("  0\tOK\n" ++ˢ
  ("  1\tFailed to open file\n" ++ˢ
  ("  2\tFailed to read input\n" ++ˢ
  ("  3\tFailed to form statements\n" ++ˢ
  ("  4\tFailed to fetch URL\n" ++ˢ
  ("  5\tFailed to parse statements\n" ++ˢ
  ("  6\tFailed to encode JSON\n\n" ++ˢ
  ("Examples:\n" ++ˢ
  ("  gron /tmp/apiresponse.json\n" ++ˢ
  ("  gron http://jsonplaceholder.typicode.com/users/1 \n" ++ˢ
  ("  curl -s http://jsonplaceholder.typicode.com/users/1 | gron\n" ++ˢ "  gron http://jsonplaceholder.typicode.com/users/1 | grep company | gron --ungron\n")))))))))))))))))))))))))

shortcut : Shortcut → Reply String
shortcut requestHelp         = reply 0 "" helpText
shortcut requestVersion      = reply 0 "gron version dev\n" ""
shortcut (invalidOption msg) = reply 2 "" (msg ++ˢ ("\n" ++ˢ helpText))
shortcut (openError msg)     = reply (code cannotOpen) "" (msg ++ˢ "\n")

helpReply : shortcut requestHelp ≡ reply 0 "" helpText
helpReply = refl

versionReply : shortcut requestVersion ≡ reply 0 "gron version dev\n" ""
versionReply = refl

flagReply : (msg : _) → shortcut (invalidOption msg) ≡ reply 2 "" (msg ++ˢ ("\n" ++ˢ helpText))
flagReply msg = refl

openReply : (msg : _) → shortcut (openError msg) ≡ reply (code cannotOpen) "" (msg ++ˢ "\n")
openReply msg = refl

helpFixture : helpText ≡
  "Transform JSON (from a file, URL, or stdin) into discrete assignments to make it greppable\n\n" ++ˢ
  ("Usage:\n  gron [OPTIONS] [FILE|URL|-]\n\n" ++ˢ
  ("Options:\n" ++ˢ
  ("  -u, --ungron     Reverse the operation (turn assignments back into JSON)\n" ++ˢ
  ("  -v, --values     Print just the values of provided assignments\n" ++ˢ
  ("  -c, --colorize   Colorize output (default on tty)\n" ++ˢ
  ("  -m, --monochrome Monochrome (don't colorize output)\n" ++ˢ
  ("  -s, --stream     Treat each line of input as a separate JSON object\n" ++ˢ
  ("  -k, --insecure   Disable certificate validation\n" ++ˢ
  ("  -x, --proxy      Set proxy configuration\n" ++ˢ
  ("      --noproxy    Comma-separated list of hosts for which not to use a proxy, if one is specified.\n" ++ˢ
  ("  -j, --json       Represent gron data as JSON stream\n" ++ˢ
  ("      --no-sort    Don't sort output (faster)\n" ++ˢ
  ("      --version    Print version information\n\n" ++ˢ
  ("Exit Codes:\n" ++ˢ
  ("  0\tOK\n" ++ˢ
  ("  1\tFailed to open file\n" ++ˢ
  ("  2\tFailed to read input\n" ++ˢ
  ("  3\tFailed to form statements\n" ++ˢ
  ("  4\tFailed to fetch URL\n" ++ˢ
  ("  5\tFailed to parse statements\n" ++ˢ
  ("  6\tFailed to encode JSON\n\n" ++ˢ
  ("Examples:\n" ++ˢ
  ("  gron /tmp/apiresponse.json\n" ++ˢ
  ("  gron http://jsonplaceholder.typicode.com/users/1 \n" ++ˢ
  ("  curl -s http://jsonplaceholder.typicode.com/users/1 | gron\n" ++ˢ "  gron http://jsonplaceholder.typicode.com/users/1 | grep company | gron --ungron\n")))))))))))))))))))))))))
helpFixture = refl

earlier : List Char → List Char → Bool
earlier []       []       = false
earlier []       (_ ∷ _)  = true
earlier (_ ∷ _)  []       = false
earlier (c ∷ cs) (d ∷ ds) =
  if (toℕ c ≡ᵇ toℕ d) then earlier cs ds else (toℕ c <ᵇ toℕ d)

earlierEmpty : earlier [] [] ≡ false
earlierEmpty = refl

earlierPrefix : (d : _) → (ds : _) → earlier [] (d ∷ ds) ≡ true
earlierPrefix d ds = refl

earlierNonempty : (c : _) → (cs : _) → earlier (c ∷ cs) [] ≡ false
earlierNonempty c cs = refl

earlierChars : (c : _) → (d : _) → (cs : _) → (ds : _) →
  earlier (c ∷ cs) (d ∷ ds) ≡ (if (toℕ c ≡ᵇ toℕ d) then earlier cs ds else (toℕ c <ᵇ toℕ d))
earlierChars c d cs ds = refl

placeMember : {A : Set} → (String → String) → (String × A) → List (String × A) → List (String × A)
placeMember spell entry [] = entry ∷ []
placeMember spell (k , v) ((l , w) ∷ rest) =
  if earlier (toList (spell l)) (toList (spell k))
    then ((l , w) ∷ placeMember spell (k , v) rest)
    else ((k , v) ∷ (l , w) ∷ rest)

orderMembers : {A : Set} → Traversal → List (String × A) → List (String × A)
orderMembers enumerated       entries        = entries
orderMembers (byAccess spell) []             = []
orderMembers (byAccess spell) (entry ∷ rest) =
  placeMember spell entry (orderMembers (byAccess spell) rest)

keepEnumeration : {A : Set} → (entries : List (String × A)) → orderMembers enumerated entries ≡ entries
keepEnumeration [] = refl
keepEnumeration (entry ∷ rest) = refl

orderEmpty : {A : Set} → (spell : _) → orderMembers {A} (byAccess spell) [] ≡ []
orderEmpty spell = refl

orderMore : {A : Set} → (spell : _) → (entry : String × A) → (rest : _) →
  orderMembers (byAccess spell) (entry ∷ rest) ≡ placeMember spell entry (orderMembers (byAccess spell) rest)
orderMore spell entry rest = refl

placeFirst : {A : Set} → (spell : _) → (entry : String × A) →
  placeMember spell entry [] ≡ (entry ∷ [])
placeFirst spell entry = refl

placeAmong : {A : Set} → (spell : _) → (k : _) → (v : A) →
  (l : _) → (w : _) → (rest : _) →
  placeMember spell (k , v) ((l , w) ∷ rest) ≡
  (if earlier (toList (spell l)) (toList (spell k))
    then ((l , w) ∷ placeMember spell (k , v) rest)
    else ((k , v) ∷ (l , w) ∷ rest))
placeAmong spell k v l w rest = refl

identifierOrderFixture : earlier (toList ".a10") (toList ".a2") ≡ true
identifierOrderFixture = refl

bracketOrderFixture : earlier (toList "[\" \"]") (toList "[\"\"]") ≡ true
bracketOrderFixture = refl


mutual
  statementsAt : Traversal → List Step → Value → List Binding
  statementsAt t path (scalar a) = binding path (literal a) ∷ []
  statementsAt t path (object entries) =
    binding path objectMarker ∷ concatMap proj₂ (orderMembers t (memberStatements t path entries))
  statementsAt t path (array entries) =
    binding path arrayMarker ∷ indexStatements t path 0 entries

  memberStatements : Traversal → List Step → List (String × Value) → List (String × List Binding)
  memberStatements t path [] = []
  memberStatements t path ((k , v) ∷ rest) =
    (k , statementsAt t (path ++ (fieldName k ∷ [])) v) ∷ memberStatements t path rest

  indexStatements : Traversal → List Step → ℕ → List Value → List Binding
  indexStatements t path i [] = []
  indexStatements t path i (v ∷ rest) =
    statementsAt t (path ++ (index i ∷ [])) v ++ indexStatements t path (suc i) rest

scalarStatement : (t : _) → (path : _) → (a : _) →
  statementsAt t path (scalar a) ≡ (binding path (literal a) ∷ [])
scalarStatement t path a = refl

objectStatement : (t : _) → (path : _) → (entries : _) →
  statementsAt t path (object entries) ≡
  (binding path objectMarker ∷ concatMap proj₂ (orderMembers t (memberStatements t path entries)))
objectStatement t path entries = refl

arrayStatement : (t : _) → (path : _) → (entries : _) →
  statementsAt t path (array entries) ≡
  (binding path arrayMarker ∷ indexStatements t path 0 entries)
arrayStatement t path entries = refl

noMembers : (t : _) → (path : _) → memberStatements t path [] ≡ []
noMembers t path = refl

nextMember : (t : _) → (path : _) → (k : _) → (v : _) →
  (rest : _) → memberStatements t path ((k , v) ∷ rest) ≡
  ((k , statementsAt t (path ++ (fieldName k ∷ [])) v) ∷ memberStatements t path rest)
nextMember t path k v rest = refl

noIndices : (t : _) → (path : _) → (i : _) → indexStatements t path i [] ≡ []
noIndices t path i = refl

nextIndex : (t : _) → (path : _) → (i : _) → (v : _) → (rest : _) →
  indexStatements t path i (v ∷ rest) ≡
  (statementsAt t (path ++ (index i ∷ [])) v ++ indexStatements t path (suc i) rest)
nextIndex t path i v rest = refl

forward : Traversal → Parsed Value → Reply (List Binding)
forward t (parsed doc) = reply 0 (statementsAt t [] doc) ""
forward t (rejected msg) = reply (code cannotForm) [] ("failed to form statements: " ++ˢ (msg ++ˢ "\n"))

forwardStream : Traversal → List Value → Maybe String → Reply (List Binding)
forwardStream t docs nothing = reply 0 (statementsAt t [] (array docs)) ""
forwardStream t docs (just msg) =
  reply (code cannotForm) (statementsAt t [] (array docs)) ("failed to form statements: " ++ˢ (msg ++ˢ "\n"))

forwardDecoded : (t : _) → (doc : _) →
  forward t (parsed doc) ≡ reply 0 (statementsAt t [] doc) ""
forwardDecoded t doc = refl

forwardRejected : (t : _) → (msg : _) →
  forward t (rejected msg) ≡ reply (code cannotForm) [] ("failed to form statements: " ++ˢ (msg ++ˢ "\n"))
forwardRejected t msg = refl

streamComplete : (t : _) → (docs : _) →
  forwardStream t docs nothing ≡ reply 0 (binding [] arrayMarker ∷ indexStatements t [] 0 docs) ""
streamComplete t docs = refl

streamInterrupted : (t : _) → (docs : _) → (msg : _) →
  forwardStream t docs (just msg) ≡
  reply (code cannotForm) (binding [] arrayMarker ∷ indexStatements t [] 0 docs)
    ("failed to form statements: " ++ˢ (msg ++ˢ "\n"))
streamInterrupted t docs msg = refl

adjacentDocumentsFixture : (t : _) →
  forwardStream t (scalar (boolean true) ∷ scalar null ∷ []) nothing ≡
  reply 0 (binding [] arrayMarker ∷ binding (index 0 ∷ []) (literal (boolean true)) ∷
           binding (index 1 ∷ []) (literal null) ∷ []) ""
adjacentDocumentsFixture t
  rewrite streamComplete t (scalar (boolean true) ∷ scalar null ∷ [])
        | nextIndex t [] 0 (scalar (boolean true)) (scalar null ∷ [])
        | scalarStatement t (index 0 ∷ []) (boolean true)
        | nextIndex t [] 1 (scalar null) []
        | scalarStatement t (index 1 ∷ []) null
        | noIndices t [] 2
  = refl

partialStreamFixture : (t : _) →
  forwardStream t (scalar (number "1") ∷ []) (just "EOF") ≡
  reply 3 (binding [] arrayMarker ∷ binding (index 0 ∷ []) (literal (number "1")) ∷ [])
    "failed to form statements: EOF\n"
partialStreamFixture t
  rewrite streamInterrupted t (scalar (number "1") ∷ []) "EOF"
        | nextIndex t [] 0 (scalar (number "1")) []
        | scalarStatement t (index 0 ∷ []) (number "1")
        | noIndices t [] 1
  = refl


valuesOf : List Capture → String
valuesOf [] = ""
valuesOf (skipped ∷ rest) = valuesOf rest
valuesOf (captured objectMarker ∷ rest) = valuesOf rest
valuesOf (captured arrayMarker ∷ rest) = valuesOf rest
valuesOf (rawValue s ∷ rest) = s ++ˢ ("\n" ++ˢ valuesOf rest)
valuesOf (captured (literal (text s)) ∷ rest) = s ++ˢ ("\n" ++ˢ valuesOf rest)
valuesOf (captured (literal (number s)) ∷ rest) = s ++ˢ ("\n" ++ˢ valuesOf rest)
valuesOf (captured (literal null) ∷ rest) = "null\n" ++ˢ valuesOf rest
valuesOf (captured (literal (boolean true)) ∷ rest) = "true\n" ++ˢ valuesOf rest
valuesOf (captured (literal (boolean false)) ∷ rest) = "false\n" ++ˢ valuesOf rest

noValues : valuesOf [] ≡ ""
noValues = refl

skipValue : (rest : _) → valuesOf (skipped ∷ rest) ≡ valuesOf rest
skipValue rest = refl

skipObjectMarker : (rest : _) → valuesOf (captured objectMarker ∷ rest) ≡ valuesOf rest
skipObjectMarker rest = refl

skipArrayMarker : (rest : _) → valuesOf (captured arrayMarker ∷ rest) ≡ valuesOf rest
skipArrayMarker rest = refl

readRawValue : (s : _) → (rest : _) →
  valuesOf (rawValue s ∷ rest) ≡ (s ++ˢ ("\n" ++ˢ valuesOf rest))
readRawValue s rest = refl

readTextValue : (s : _) → (rest : _) →
  valuesOf (captured (literal (text s)) ∷ rest) ≡ (s ++ˢ ("\n" ++ˢ valuesOf rest))
readTextValue s rest = refl

readNumberValue : (s : _) → (rest : _) →
  valuesOf (captured (literal (number s)) ∷ rest) ≡ (s ++ˢ ("\n" ++ˢ valuesOf rest))
readNumberValue s rest = refl

readNullValue : (rest : _) →
  valuesOf (captured (literal null) ∷ rest) ≡ ("null\n" ++ˢ valuesOf rest)
readNullValue rest = refl

readTrueValue : (rest : _) →
  valuesOf (captured (literal (boolean true)) ∷ rest) ≡ ("true\n" ++ˢ valuesOf rest)
readTrueValue rest = refl

readFalseValue : (rest : _) →
  valuesOf (captured (literal (boolean false)) ∷ rest) ≡ ("false\n" ++ˢ valuesOf rest)
readFalseValue rest = refl

extractFixture :
  valuesOf (captured objectMarker ∷ captured arrayMarker ∷ captured (literal null) ∷
    captured (literal (number "1.2300")) ∷ captured (literal (text "line\n2")) ∷
    captured (literal (text "a\"b")) ∷ []) ≡ "null\n1.2300\nline\n2\na\"b\n"
extractFixture = refl

bindingDatum : BindingValue → Value
bindingDatum (literal a) = scalar a
bindingDatum objectMarker = object []
bindingDatum arrayMarker = array []

literalDatum : (a : _) → bindingDatum (literal a) ≡ scalar a
literalDatum a = refl

objectDatum : bindingDatum objectMarker ≡ object []
objectDatum = refl

arrayDatum : bindingDatum arrayMarker ≡ array []
arrayDatum = refl

placeAt : List Step → Value → Value
placeAt [] v = v
placeAt (fieldName k ∷ p) v = object ((k , placeAt p v) ∷ [])
placeAt (index n ∷ p) v = array (replicate n (scalar null) ++ (placeAt p v ∷ []))

placeRoot : (v : _) → placeAt [] v ≡ v
placeRoot v = refl

placeField : (k : _) → (p : _) → (v : _) →
  placeAt (fieldName k ∷ p) v ≡ object ((k , placeAt p v) ∷ [])
placeField k p v = refl

placeIndex : (n : _) → (p : _) → (v : _) →
  placeAt (index n ∷ p) v ≡ array (replicate n (scalar null) ++ (placeAt p v ∷ []))
placeIndex n p v = refl

private
  mapParsed : {A B : Set} → (A → B) → Parsed A → Parsed B
  mapParsed f (parsed a) = parsed (f a)
  mapParsed f (rejected msg) = rejected msg

mutual
  overlay : Value → Value → Parsed Value
  overlay (scalar _) newer = parsed newer
  overlay (object fields) (object newer) = mapParsed object (mergeFields fields newer)
  overlay (object _) (scalar _) = rejected "cannot merge object with non-object"
  overlay (object _) (array _) = rejected "cannot merge object with non-object"
  overlay (array entries) (array newer) = mapParsed array (mergeEntries entries newer)
  overlay (array _) (object _) = rejected "cannot merge array with non-array"
  overlay (array _) (scalar _) = rejected "cannot merge array with non-array"

  overlayFields : List (String × Value) → String → Value → Parsed (List (String × Value))
  overlayFields [] k v = parsed ((k , v) ∷ [])
  overlayFields ((k , old) ∷ rest) l new with k ≟ l
  ... | yes _ = mapParsed (λ v → (k , v) ∷ rest) (overlay old new)
  ... | no _  = mapParsed (λ vs → (k , old) ∷ vs) (overlayFields rest l new)

  private
    mergeFields : List (String × Value) → List (String × Value) → Parsed (List (String × Value))
    mergeFields fields [] = parsed fields
    mergeFields fields ((k , new) ∷ rest) with overlayFields fields k new
    ... | parsed updated = mergeFields updated rest
    ... | rejected msg   = rejected msg

    mergeEntries : List Value → List Value → Parsed (List Value)
    mergeEntries [] newer = parsed newer
    mergeEntries (old ∷ rest) [] = parsed (old ∷ rest)
    mergeEntries (old ∷ rest) (scalar null ∷ newer) =
      mapParsed (λ vs → old ∷ vs) (mergeEntries rest newer)
    mergeEntries (old ∷ rest) (new ∷ newer) with overlay old new
    ... | parsed merged = mapParsed (λ vs → merged ∷ vs) (mergeEntries rest newer)
    ... | rejected msg  = rejected msg

overwriteScalar : (a : _) → (newer : _) → overlay (scalar a) newer ≡ parsed newer
overwriteScalar a newer = refl

keepObject : (fields : _) →
  overlay (object fields) (object []) ≡ parsed (object fields)
keepObject fields = refl

keepArray : (entries : _) → overlay (array entries) (array []) ≡ parsed (array entries)
keepArray [] = refl
keepArray (entry ∷ rest) = refl

fillArray : (entries : _) → overlay (array []) (array entries) ≡ parsed (array entries)
fillArray entries = refl

conflictObjectNumber : (fields : _) → (n : _) →
  overlay (object fields) (scalar (number n)) ≡ rejected "cannot merge object with non-object"
conflictObjectNumber fields n = refl

conflictObjectArray : (fields : _) → (entries : _) →
  overlay (object fields) (array entries) ≡ rejected "cannot merge object with non-object"
conflictObjectArray fields entries = refl

conflictArrayObject : (entries : _) → (fields : _) →
  overlay (array entries) (object fields) ≡ rejected "cannot merge array with non-array"
conflictArrayObject entries fields = refl

overlayFieldMissing : (k : _) → (v : _) → overlayFields [] k v ≡ parsed ((k , v) ∷ [])
overlayFieldMissing k v = refl

overlayFieldFound : (k : _) → (old : _) → (new : _) →
  (rest : _) → (merged : _) → overlay old new ≡ parsed merged →
  overlayFields ((k , old) ∷ rest) k new ≡ parsed ((k , merged) ∷ rest)
overlayFieldFound k old new rest merged eq with k ≟ k
... | yes _ rewrite eq = refl
... | no unequal = ⊥-elim (unequal refl)

overlayFieldConflict : (k : _) → (old : _) → (new : _) →
  (rest : _) → (msg : _) → overlay old new ≡ rejected msg →
  overlayFields ((k , old) ∷ rest) k new ≡ rejected msg
overlayFieldConflict k old new rest msg eq with k ≟ k
... | yes _ rewrite eq = refl
... | no unequal = ⊥-elim (unequal refl)

overlayFieldPass : (k : _) → (v : _) → (l : _) → (w : _) →
  (rest : _) → (merged : _) → k ≢ l → overlayFields rest l w ≡ parsed merged →
  overlayFields ((k , v) ∷ rest) l w ≡ parsed ((k , v) ∷ merged)
overlayFieldPass k v l w rest merged different eq with k ≟ l
... | yes equal = ⊥-elim (different equal)
... | no _ rewrite eq = refl

overlayFieldPassConflict : (k : _) → (v : _) → (l : _) → (w : _) →
  (rest : _) → (msg : _) → k ≢ l → overlayFields rest l w ≡ rejected msg →
  overlayFields ((k , v) ∷ rest) l w ≡ rejected msg
overlayFieldPassConflict k v l w rest msg different eq with k ≟ l
... | yes equal = ⊥-elim (different equal)
... | no _ rewrite eq = refl

overlayOneField : (fields : _) → (k : _) → (new : _) →
  (merged : _) → overlayFields fields k new ≡ parsed merged →
  overlay (object fields) (object ((k , new) ∷ [])) ≡ parsed (object merged)
overlayOneField fields k new merged eq rewrite eq = refl

overlayOneFieldConflict : (fields : _) → (k : _) → (new : _) →
  (msg : _) → overlayFields fields k new ≡ rejected msg →
  overlay (object fields) (object ((k , new) ∷ [])) ≡ rejected msg
overlayOneFieldConflict fields k new msg eq rewrite eq = refl

overlayArrayHole : (entry : _) → (xs : _) → (ys : _) → (merged : _) →
  overlay (array xs) (array ys) ≡ parsed (array merged) →
  overlay (array (entry ∷ xs)) (array (scalar null ∷ ys)) ≡ parsed (array (entry ∷ merged))
overlayArrayHole entry xs ys merged eq with mergeEntries xs ys | eq
... | parsed _ | refl = refl
... | rejected _ | ()

rebuildAfter : Value → List Binding → Parsed Value
rebuildAfter v [] = parsed v
rebuildAfter current (binding path rhs ∷ rest) with overlay current (placeAt path (bindingDatum rhs))
... | parsed merged = rebuildAfter merged rest
... | rejected msg  = rejected ("failed to merge statements: " ++ˢ msg)

rebuild : List Binding → Parsed Value
rebuild [] = rejected "no statements were parsed"
rebuild (binding path rhs ∷ rest) = rebuildAfter (placeAt path (bindingDatum rhs)) rest

noReverseStatements : rebuild [] ≡ rejected "no statements were parsed"
noReverseStatements = refl

firstReverseStatement : (path : _) → (rhs : _) → (rest : _) →
  rebuild (binding path rhs ∷ rest) ≡ rebuildAfter (placeAt path (bindingDatum rhs)) rest
firstReverseStatement path rhs rest = refl

lastReverseValue : (v : _) → rebuildAfter v [] ≡ parsed v
lastReverseValue v = refl

acceptReverseStatement : (current : _) → (path : _) → (rhs : _) →
  (rest : _) → (merged : _) → overlay current (placeAt path (bindingDatum rhs)) ≡ parsed merged →
  rebuildAfter current (binding path rhs ∷ rest) ≡ rebuildAfter merged rest
acceptReverseStatement current path rhs rest merged eq rewrite eq = refl

rejectReverseStatement : (current : _) → (path : _) → (rhs : _) →
  (rest : _) → (msg : _) → overlay current (placeAt path (bindingDatum rhs)) ≡ rejected msg →
  rebuildAfter current (binding path rhs ∷ rest) ≡ rejected ("failed to merge statements: " ++ˢ msg)
rejectReverseStatement current path rhs rest msg eq rewrite eq = refl

arrayNullFixture :
  rebuild (binding (fieldName "a" ∷ index 1 ∷ []) (literal (number "1")) ∷
           binding (fieldName "a" ∷ index 1 ∷ []) (literal null) ∷ []) ≡
  parsed (object (("a" , array (scalar null ∷ scalar (number "1") ∷ [])) ∷ []))
arrayNullFixture = refl

reverseConflictFixture :
  rebuild (binding (fieldName "a" ∷ fieldName "b" ∷ []) (literal (number "2")) ∷
           binding (fieldName "a" ∷ []) (literal (number "1")) ∷ []) ≡
  rejected "failed to merge statements: cannot merge object with non-object"
reverseConflictFixture = refl

reverseReply : Parsed Value → Reply (Maybe Value)
reverseReply (parsed v) = reply 0 (just v) ""
reverseReply (rejected msg) = reply (code cannotParse) nothing (msg ++ˢ "\n")

reverseDecoded : (v : _) → reverseReply (parsed v) ≡ reply 0 (just v) ""
reverseDecoded v = refl

reverseRejected : (msg : _) → reverseReply (rejected msg) ≡ reply (code cannotParse) nothing (msg ++ˢ "\n")
reverseRejected msg = refl

ansiEscape : String
ansiEscape = fromList (primNatToChar 27 ∷ [])

escapeByte : ansiEscape ≡ fromList (primNatToChar 27 ∷ [])
escapeByte = refl

private
  shade : String → String → String → String
  shade start end s = ansiEscape ++ˢ (start ++ˢ (s ++ˢ (ansiEscape ++ˢ end)))

tint : Bool → Tint → String → String
tint false _           s = s
tint true  plain       s = s
tint true  identifier  s = shade "[34;1m" "[0;22m" s
tint true  delimiter   s = shade "[35m" "[0m" s
tint true  numberToken s = shade "[31m" "[0m" s
tint true  keyword     s = shade "[36m" "[0m" s
tint true  stringToken s = shade "[33m" "[0m" s
tint true  colon       s = shade "[1m" "[22m" s

monochromeToken : (role : _) → (s : _) → tint false role s ≡ s
monochromeToken role s = refl

plainToken : (s : _) → tint true plain s ≡ s
plainToken s = refl

identifierToken : (s : _) →
  tint true identifier s ≡ (ansiEscape ++ˢ ("[34;1m" ++ˢ (s ++ˢ (ansiEscape ++ˢ "[0;22m"))))
identifierToken s = refl

delimiterToken : (s : _) →
  tint true delimiter s ≡ (ansiEscape ++ˢ ("[35m" ++ˢ (s ++ˢ (ansiEscape ++ˢ "[0m"))))
delimiterToken s = refl

numericToken : (s : _) →
  tint true numberToken s ≡ (ansiEscape ++ˢ ("[31m" ++ˢ (s ++ˢ (ansiEscape ++ˢ "[0m"))))
numericToken s = refl

keywordToken : (s : _) →
  tint true keyword s ≡ (ansiEscape ++ˢ ("[36m" ++ˢ (s ++ˢ (ansiEscape ++ˢ "[0m"))))
keywordToken s = refl

quotedToken : (s : _) →
  tint true stringToken s ≡ (ansiEscape ++ˢ ("[33m" ++ˢ (s ++ˢ (ansiEscape ++ˢ "[0m"))))
quotedToken s = refl

boldColon : (s : _) →
  tint true colon s ≡ (ansiEscape ++ˢ ("[1m" ++ˢ (s ++ˢ (ansiEscape ++ˢ "[22m"))))
boldColon s = refl
