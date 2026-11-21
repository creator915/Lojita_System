{-# OPTIONS --guardedness #-}
module Test.EndToEndPolyTransport where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; length; tails; reverse; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; unlines; lines; toList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO.Primitive using (IO; return; _>>=_)
open import IO.Primitive.Finite using (putStrLn; readFile; writeFile)
open import OwnershipIO using (RunningIO)
open import OwnershipIO.FFI
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp; catchIO)
open import Code using (QName; mkQ; _==ˢ_; eqList; elemᵇ; allᵇ; anyᵇ; filterᵇ; unit; ⊥)
open import Code.Transport using (Proarrow; _⇝_)
open import Code.Protocol
open import Code.NodeTransport using (moduleQName)
import Code.PolyTransport as P
open import Code.Lift using (liftSpec; liftSpecTree; mkChildLift; endpointLift)
open import Code.Encode using (encodeLift)
open import Code.SExpr
open import Code.SessionProtocol
open import Code.SessionWorkspace using (withOpenIncludes)
open import Code.SessionRunner using (SessionConfig; sessionConfig; ActionResult; accepted; rejected; finished; executeAction)
open import Code.AI using (ServiceBackend; ScriptedBackend)
open import Test.HarnessPure using (submission)
import Store.CAS as CAS
open import Store.Verify using (verifyCommitDAG)

_ : parseSessionAction "(session-action (kind drive-tree) (treeName \"T\") (why \"r\") (specSrc \"s\") (baseTrees) (maybeLiftSrc nothing) (maybeTransportSrc nothing))"
    ≡ just (drive-tree "T" "r" "s" [] nothing)
_ = refl

_ : parseSessionAction "(session-action (kind drive-tree) (treeName \"T\") (why \"r\") (specSrc \"s\") (baseTrees) (maybeLiftSrc nothing) (maybeTransportSrc (just 3)))" ≡ nothing
_ = refl

data Stage : Set where B0 U0 B1 U1 : Stage

epoch : Stage → String
epoch B0 = "B0"
epoch U0 = "U0"
epoch B1 = "B1"
epoch U1 = "U1"

upper split : Stage → Bool
upper B0 = false
upper B1 = false
upper _ = true
split B1 = true
split U1 = true
split _ = false

previous blueprint : Stage → Stage
previous s = if upper s then U0 else B0
blueprint s = if split s then B1 else B0

root parser engine : Stage → String
root s = "Gen." ++ˢ epoch s ++ˢ ".Root"
parser s = root s ++ˢ ".Parser"
engine s = root s ++ˢ ".Engine"

-- B1 uses the original blueprint module name. U1 gives the same immutable
-- upper implementation a freshly qualified export at its new slot.
engineSlot : Stage → String
engineSlot B1 = engine B0
engineSlot s = engine s

carrier emptyValue : Stage → String
carrier s = if upper s then "String" else "Bool"
emptyValue s = if upper s then "\"\"" else "false"

header : String → String
header name = "module " ++ˢ name ++ˢ " where\n"

common : String
common = unlines ("open import Data.Bool using (Bool; true; false; not; if_then_else_)"
  ∷ "open import Data.String using (String)" ∷ "open import Data.Product using (_×_; _,_; proj₁; proj₂)"
  ∷ "open import Data.Unit using (⊤)" ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)" ∷ "" ∷ [])

pp : String
pp = "open import Context.PolyTransport using (TransportsPoly; graphPort; idPort)\n"

useAs : String → String → String
useAs m a = "import " ++ˢ m ++ˢ " as " ++ˢ a ++ˢ "\n"

-- Each child declares its own record, including its constructor. Parent glue
-- explicitly unpacks/repackages values; neither sibling imports the other.
port : Stage → String
port s = "record Port : Set where\n  constructor box\n  field value : " ++ˢ carrier s ++ˢ "\n"

decl : Bool → String → String → String
decl spec sig body = if spec then "postulate\n  " ++ˢ sig ++ˢ "\n" else sig ++ˢ "\n" ++ˢ body ++ˢ "\n"

engineSource : Stage → Bool → String
engineSource s spec = header (engine s) ++ˢ common ++ˢ port s
  ++ˢ decl spec ("run : Port → " ++ˢ carrier s) "run x = Port.value x"
  ++ˢ decl spec ("law : (x : " ++ˢ carrier s ++ˢ ") → run (box x) ≡ x") "law x = refl"

  ++ˢ (if upper s ∧ not spec then
    useAs (engine B0) "Base" ++ˢ "open import Context.Blueprint using (Commutes₁; portLift)\nopen import Agda.Builtin.String using (primStringEquality)\n"
    ++ˢ "observe : String → Bool\nobserve x = not (primStringEquality x \"\")\n"
    ++ˢ "vertical : Commutes₁ (portLift (λ x → Base.box (observe (Port.value x)))) (portLift observe) (λ _ → ⊤) _≡_ Base.run run\nvertical x d = refl\n"
    else "")

parserSource : Stage → Bool → Bool → String
parserSource s spec includeSquare = header (parser s) ++ˢ common ++ˢ port s ++ˢ operations
  where
    a = carrier s
    operations : String
    operations = if split s then
        decl spec ("decode : Port → " ++ˢ a) "decode x = Port.value x"
      ++ˢ decl spec ("gate : Bool → " ++ˢ a ++ˢ " → " ++ˢ a)
                    ("gate b x = if b then " ++ˢ emptyValue s ++ˢ " else x")
      ++ˢ decl spec ("law : (b : Bool) (x : " ++ˢ a ++ˢ ") → gate b (decode (box x)) ≡ (if b then "
                       ++ˢ emptyValue s ++ˢ " else x)") "law b x = refl"
      ++ˢ (if spec Data.Bool.∨ not includeSquare then "" else pp ++ˢ useAs (parser (previous s)) "Old"
        ++ˢ "square : TransportsPoly (graphPort (λ x → false , box (Old.Port.value x))) (idPort " ++ˢ a
        ++ˢ ") (λ _ → ⊤) Old.parse (λ z → gate (proj₁ z) (decode (proj₂ z)))\nsquare x y d refl = refl\n")
      else decl spec ("parse : Port → " ++ˢ a) "parse x = Port.value x"
        ++ˢ decl spec ("law : (x : " ++ˢ a ++ˢ ") → parse (box x) ≡ x") "law x = refl"

rootSource : Stage → Bool → Bool → String
rootSource s spec includeSquare = header (root s) ++ˢ common ++ˢ children ++ˢ operations ++ˢ horizontal ++ˢ vertical
  where
    a = carrier s
    input = if split s then "Bool × " ++ˢ a else a
    children = if spec then "" else useAs (parser s) "P" ++ˢ useAs (engineSlot s) "E"
    parsed = if split s then "P.gate (proj₁ x) (P.decode (P.box (proj₂ x)))" else "P.parse (P.box x)"
    expected = if split s then "(if proj₁ x then " ++ˢ emptyValue s ++ˢ " else proj₂ x)" else "x"
    pLaw = if split s then "P.law (proj₁ x) (proj₂ x)" else "P.law x"
    operations = decl spec ("run : " ++ˢ input ++ˢ " → " ++ˢ a) ("run x = E.run (E.box (" ++ˢ parsed ++ˢ "))")
      ++ˢ decl spec ("correct : (x : " ++ˢ input ++ˢ ") → run x ≡ " ++ˢ expected)
        ("correct x = trans (E.law (" ++ˢ parsed ++ˢ ")) (" ++ˢ pLaw ++ˢ ")")
    horizontal = if not spec ∧ split s ∧ includeSquare then
      pp ++ˢ useAs (root (previous s)) "Old"
      ++ˢ "square : TransportsPoly (graphPort (λ x → false , x)) (idPort " ++ˢ a
      ++ˢ ") (λ _ → ⊤) Old.run run\nsquare x y d refl = trans (Old.correct x) (sym (correct (false , x)))\n"
      else ""
    vertical = if not spec ∧ upper s then
      "open import Context.Blueprint using (Commutes₁; portLift)\nopen import Agda.Builtin.String using (primStringEquality)\n"
      ++ˢ useAs (root (blueprint s)) "Base"
      ++ˢ "observe : String → Bool\nobserve x = not (primStringEquality x \"\")\n"
      ++ˢ "vertical : Commutes₁ (portLift " ++ˢ (if split s then "(λ z → proj₁ z , observe (proj₂ z))" else "observe")
      ++ˢ ") (portLift observe) (λ _ → ⊤) _≡_ Base.run run\n"
      ++ˢ (if split s then
        "vertical (false , x) d = trans (cong observe (correct (false , x))) (sym (Base.correct (false , observe x)))\nvertical (true , x) d = trans (cong observe (correct (true , x))) (sym (Base.correct (true , observe x)))\n"
        else "vertical x d = trans (cong observe (correct x)) (sym (Base.correct (observe x)))\n")
      ++ˢ (if epoch s ==ˢ "U1" then
        "open import Context.World using (CliApp; CliCaps; here; there; readStdinAllW; writeStdoutStrW; decodeUtf8Lossy; pure; _>>=w_; _>>w_)\n"
        ++ˢ "app : CliApp CliCaps\n"
        ++ˢ "app = readStdinAllW (there here) >>=w λ bs → writeStdoutStrW (there (there here)) (run (primStringEquality (decodeUtf8Lossy bs) \"--drop\\n\" , decodeUtf8Lossy bs)) >>w pure 0\n"
        else "")
      else ""

member : String → String → QName
member m n = moduleQName (m ++ˢ "." ++ˢ n)

newUnits : String → List String → List Proarrow
newUnits m = map (λ n → ⊥ ⇝ unit (member m n))

rootPlan : Stage → Bool → String
rootPlan s square = submission "compose the two independent ports" (rootSource s false square)
  ((parser s , parserSource s true false) ∷ (if split s then [] else [ engine s , engineSource s true ]))
  (newUnits (root s) ((if split s ∧ square then [ "square" ] else [])
    ++ (if upper s then "observe" ∷ "vertical" ∷ [] else [])
    ++ (if epoch s ==ˢ "U1" then [ "app" ] else [])))

parserPlan : Stage → Bool → String
parserPlan s square = submission "implement the Parser boundary" (parserSource s false square) []
  (newUnits (parser s) (if split s ∧ square then [ "square" ] else []))

transport : Stage → P.TransportSpec
transport s = P.transportSpecTree (moduleQName old) (moduleQName new)
  (P.keepChild (moduleQName e) (moduleQName (engineSlot s)) ∷ P.moveChildren [ moduleQName p ] [ moduleQName q ] [ sub ] ∷ [])
  [ P.polySquare [ member old "run" ] [ member new "run" ] (member new "square") ]
  where
    old = root (previous s)
    new = root s
    p = parser (previous s)
    q = parser s
    e = engine (previous s)
    sub = P.transportSpecTree (moduleQName p) (moduleQName q) []
      [ P.polySquare [ member p "parse" ] (member q "decode" ∷ member q "gate" ∷ []) (member q "square") ]

lifting : Stage → String
lifting s = showSExpr (encodeLift (liftSpecTree (moduleQName (root b)) (moduleQName (root s))
  (mkChildLift (moduleQName (parser b)) (moduleQName (parser s)) nothing
   ∷ mkChildLift (moduleQName (engine B0)) (moduleQName (engineSlot s)) (just engineLift) ∷ [])
  [ endpointLift (member (root b) "run") (member (root s) "run") (member (root s) "vertical") ]))
  where
    b = blueprint s
    engineLift = liftSpec (moduleQName (engine B0)) (moduleQName (engineSlot s)) []
      [ endpointLift (member (engine B0) "run") (member (engineSlot s) "run") (member (engineSlot s) "vertical") ]

bases : Stage → List String
bases B0 = []
bases U0 = [ "B0" ]
bases B1 = [ "B0" ]
bases U1 = "U0" ∷ "B1" ∷ []

wire : Stage → String
wire s = showSExpr (list (sym "session-action" ∷ list (sym "kind" ∷ sym "drive-tree" ∷ [])
  ∷ field′ "treeName" (str (epoch s)) ∷ field′ "why" (str ("seal " ++ˢ epoch s)) ∷ field′ "specSrc" (str (rootSource s true true))
  ∷ list (sym "baseTrees" ∷ map str (bases s)) ∷ field′ "maybeLiftSrc" (if upper s then some (lifting s) else sym "nothing")
  ∷ (if split s then [ field′ "maybeTransportSrc" (some (showSExpr (P.encodePolyTransport (transport s)))) ] else [])))
  where
    field′ : String → SExpr → SExpr
    field′ k v = list (sym k ∷ v ∷ [])
    some : String → SExpr
    some txt = list (sym "just" ∷ str txt ∷ [])

assert : String → Bool → IO ⊤
assert label true = return tt
assert label false = failIO label

require : ∀ {A : Set} → String → Maybe A → IO A
require label nothing = failIO label
require label (just a) = return a

expectedOK : String → ActionResult → IO ⊤
expectedOK label (accepted msg) = assert (label ++ˢ ": " ++ˢ msg) (elemᵇ _==ˢ_ label (lines msg))
expectedOK label (rejected e) = failIO (label ++ˢ ": " ++ˢ e)
expectedOK _ _ = failIO "unexpected finish"

-- Each service is bound to one ownership slot. An unexpected fork, bind or
-- retry fails immediately, including any attempt to wake a retained Engine.
service : Stage → IORef (List String) → IO (RunningIO AIReq AIReply (⊤ × ⊤))
service s calls = do
  slot ← newIORef ""
  repaired ← newIORef false
  return (record { onCall = request slot repaired ; onStop = return (tt , tt) })
  where
    note : String → IO ⊤
    note event = readIORef calls >>= λ events → writeIORef calls (event ∷ events)

    allowed : String → Bool
    allowed n = elemᵇ _==ˢ_ n (root s ∷ parser s ∷ (if split s then [] else [ engine s ]))

    good : String → String
    good n = if n ==ˢ root s then rootPlan s true else
      if n ==ˢ parser s then parserPlan s true else submission "implement the Engine boundary" (engineSource s false) []
        (newUnits (engine s) (if upper s then "observe" ∷ "vertical" ∷ [] else []))

    negative : String → Maybe (String × String)
    negative n = if n ==ˢ root s then atRoot s else
      if (n ==ˢ parser s) ∧ (epoch s ==ˢ "B1") then just (parserPlan s false , "missingPolySquare") else nothing
      where
        atRoot : Stage → Maybe (String × String)
        atRoot B0 = just (submission "attempt host import" (header (root B0) ++ˢ "import Code.Harness\n") [] [] ,
                          "sandbox: forbidden module name or import")
        atRoot B1 = just (rootPlan B1 false , "missingPolySquare")
        atRoot _ = nothing

    contains : String → String → Bool
    contains needle haystack = anyᵇ (λ suffix → eqList Agda.Builtin.Char.primCharEquality (toList needle) (take (length (toList needle)) suffix)) (tails (toList haystack))
      where import Agda.Builtin.Char

    request : IORef String → IORef Bool → AIReq → IO AIReply
    request slot repaired (bindNode n _) = assert ("unexpected bind " ++ˢ n) (allowed n) >>
      note ("bind " ++ˢ n) >> writeIORef slot n >> return (aiReply "bound" n)
    request slot repaired (forkNode n) = assert ("unexpected fork " ++ˢ n) (allowed n) >>
      note ("fork " ++ˢ n) >> return (aiReply "" n)
    request slot repaired (accept _) = return (aiReply "accepted" "")
    request slot repaired (propose prompt retry _) = do
      n ← readIORef slot
      note ("propose " ++ˢ n)
      let diagnostic = unlines (reverse (take 16 (reverse (lines prompt))))
      respond n diagnostic (negative n) retry
      where
        respond : String → String → Maybe (String × String) → Bool → IO AIReply
        respond n _ nothing false = return (aiReply (good n) n)
        respond n _ (just (bad , _)) false = return (aiReply bad n)
        respond n diag nothing true = failIO (n ++ˢ " unexpectedly retried\n" ++ˢ diag)
        respond n diag (just (_ , wanted)) true = do
          again ← readIORef repaired
          assert (n ++ˢ " expected " ++ˢ wanted ++ˢ "\n" ++ˢ diag) (not again ∧ contains wanted diag)
          writeIORef repaired true
          putStrLn ("PASS rejected " ++ˢ n ++ˢ " at " ++ˢ wanted)
          return (aiReply (good n) n)

config : String → String → Stage → IORef (List String) → SessionConfig
config repo ws s calls = sessionConfig repo ws "transport Parser; reuse Engine"
  (refSpec (local "/usr/bin/python3") ("-c" ∷ filterRef ∷ []) 30000)
  (ScriptedBackend []) (λ _ → ServiceBackend (service s calls))
  where
    filterRef = "import sys\ns = sys.stdin.buffer.read()\nif s != b'--drop\\n': sys.stdout.buffer.write(s)"

runStage : String → String → Stage → IO String
runStage repo ws s = do
  calls ← newIORef []
  action ← require "invalid drive-tree envelope" (parseSessionAction (wire s))
  executeAction (config repo ws s calls) action >>= expectedOK ("ok " ++ˢ epoch s)
  events ← readIORef calls
  let count = λ e → length (filterᵇ (_==ˢ e) events)
      extra = if (epoch s ==ˢ "B0") Data.Bool.∨ (epoch s ==ˢ "B1") then 2 else 1
  assert "root/Parser wake counts" ((count ("bind " ++ˢ root s) ≡ᵇ 1) ∧ (count ("propose " ++ˢ root s) ≡ᵇ extra)
    ∧ (count ("fork " ++ˢ parser s) ≡ᵇ 1) ∧ (count ("propose " ++ˢ parser s) ≡ᵇ (if epoch s ==ˢ "B1" then 2 else 1)))
  assert "Engine wake count" ((count ("propose " ++ˢ engine (previous s)) ≡ᵇ (if split s then 0 else 1)))
  let dir = ws ++ˢ "/store"
  key ← CAS.readRef dir ("trees/" ++ˢ epoch s) >>= require "missing tree ref"
  verifyCommitDAG dir key >>= assert "invalid commit ancestry"
  c ← CAS.getCommit dir key >>= require "missing tip"
  assert "commit metadata" ((CAS.epoch c ==ˢ epoch s) ∧ (CAS.why c ==ˢ ("seal " ++ˢ epoch s)))
  putStrLn ("PASS sealed " ++ˢ epoch s ++ˢ " " ++ˢ key)
  return key

kid : String → CAS.HomeNodeObj → IO String
kid n h = find (CAS.kids h)
  where
    find : List CAS.Kid → IO String
    find [] = failIO ("missing ownership slot " ++ˢ n)
    find ((k , hash) ∷ ks) = if k ==ˢ n then return hash else find ks

compareBranches : String → Stage → String → String → List String → IO ⊤
compareBranches dir s old new parents = do
  before ← CAS.getCommit dir old >>= require "old commit"
  after ← CAS.getCommit dir new >>= require "new commit"
  assert "commit parents" (eqList _==ˢ_ parents (CAS.parents after))
  a ← CAS.getHomeNode dir (CAS.rootHome before) >>= require "old root"
  b ← CAS.getHomeNode dir (CAS.rootHome after) >>= require "new root"
  let prev = previous s
  assert "exactly two owned children" ((length (CAS.kids a) ≡ᵇ 2) ∧ (length (CAS.kids b) ≡ᵇ 2))
  e ← kid (engine prev) a
  e′ ← kid (engineSlot s) b
  p ← kid (parser prev) a
  p′ ← kid (parser s) b
  assert "Merkle sharing" ((e ==ˢ e′) ∧ not (p ==ˢ p′) ∧ not (CAS.rootHome before ==ˢ CAS.rootHome after))
  putStrLn ("PASS " ++ˢ epoch s ++ˢ " reuses Engine HomeNode " ++ˢ e)

entry : String
entry = "Gen.U1.Root.app"

filterReplay : String
filterReplay = unlines
  ("{-# OPTIONS --guardedness #-}" ∷ "module FilterReplay where"
  ∷ "open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)"
  ∷ "open import Data.List using (List; []; _∷_)"
  ∷ "open import Data.Product using (_×_; _,_; proj₂)"
  ∷ "open import Data.String using (String)"
  ∷ "open import Data.Unit using (⊤; tt)"
  ∷ "open import Agda.Builtin.String renaming (primStringEquality to eq)"
  ∷ "import IO.Primitive as IO" ∷ "import IO.Primitive.Finite as F"
  ∷ "open import Ownership" ∷ "open import OwnershipIO.FFI using (procResult; exitFailure)"
  ∷ "open import SessionEnv"
  ∷ "agrees : String → ProcOut → ProcOut → Bool"
  ∷ "agrees expected (procResult 0 ref \"\") (procResult 0 cand \"\") = eq expected ref ∧ eq ref cand"
  ∷ "agrees _ _ _ = false"
  ∷ "corpus : List (String × String)"
  ∷ "corpus = (\"\" , \"\") ∷ (\"λ多行\\nabc\\n\" , \"λ多行\\nabc\\n\") ∷ (\"tail\" , \"tail\")"
  ∷ "       ∷ (\"--drop\\n\" , \"\") ∷ (\"keep\\n--drop\\n\" , \"keep\\n--drop\\n\") ∷ []"
  ∷ "Live : St"
  ∷ "Live = Dir ((\"procExec\" , Chan (Srv ProcReq ProcOut (Dir []))) ∷ [])"
  ∷ "compareAll : List (String × String) → Prog SessionΨ Live Live Bool"
  ∷ "compareAll [] = done true"
  ∷ "compareAll ((s , expected) ∷ rest) = call \"procExec\" (procReq \"ref\" [] s) >>= λ ref →"
  ∷ "  call \"procExec\" (procReq \"cand\" [] s) >>= λ cand →"
  ∷ "  compareAll rest >>= λ ok → done (agrees expected ref cand ∧ ok)"
  ∷ "replay : Prog SessionΨ (Dir []) (Dir []) Bool"
  ∷ "replay = mkdir \"procExec\" >> open′ \"procExec\" >> compareAll corpus >>= λ ok →"
  ∷ "  stop \"procExec\" >> rmdir \"procExec\" >> done ok"
  ∷ "main : IO.IO ⊤"
  ∷ "main = evalIO sessionEnv replay tt IO.>>= λ r → if proj₂ r then F.putStrLn \"U1 replay passed\" else exitFailure"
  ∷ [])

run : String → String → IO ⊤
run repo ws = do
  b₀ ← runStage repo ws B0
  u₀ ← runStage repo ws U0
  -- Transport must recover both source homes, including Agda aliases, from
  -- the verified commits even without the legacy working-copy pointers.
  removeAll (ws ++ˢ "/trees/B0/current")
  removeAll (ws ++ˢ "/trees/U0/current")
  let misplaced = P.transportSpecTree (moduleQName (root B0)) (moduleQName (root B1))
        (P.keepChild (moduleQName (engine B0)) (moduleQName "Gen.Other.Root.Engine") ∷
         P.keepChild (moduleQName (parser B0)) (moduleQName (parser B0)) ∷ []) []
  attempts ← newIORef []
  executeAction (config repo ws B1 attempts) (drive-tree-with "B1" "invalid keep destination"
    (rootSource B1 true true) (bases B1) nothing (just (showSExpr (P.encodePolyTransport misplaced)))) >>= λ where
      (rejected e) → assert e (e ==ˢ "drive-tree: invalid TransportSpec, source snapshot or nested child mapping")
      _ → failIO "accepted a new keepChild alias outside the target epoch"
  readIORef attempts >>= λ events → assert "invalid keep destination woke AI" (length events ≡ᵇ 0)
  b₁ ← runStage repo ws B1
  compareBranches (ws ++ˢ "/store") B1 b₀ b₁ [ b₀ ]
  u₁ ← runStage repo ws U1
  compareBranches (ws ++ˢ "/store") U1 u₀ u₁ (u₀ ∷ b₁ ∷ [])
  let shared = ws ++ˢ "/generated/B1/Gen/B0/Root/Engine.agda"
  original ← readFile shared
  writeFile shared (original ++ˢ "\n-- present in neither sealed source\n")
  refused ← catchIO (withOpenIncludes repo ws (λ _ → return false)) (λ _ → return true)
  writeFile shared original
  assert "accepted a modified shared export" refused
  unused ← newIORef []
  let cfg = config repo ws U1 unused
  executeAction cfg (build-exe "compile concrete filter" entry) >>= λ where
    (accepted _) → return tt
    (rejected e) → failIO e
    _ → failIO "unexpected finish"
  executeAction cfg (finish "premature") >>= λ where
    (rejected e) → assert e (e ==ˢ "finish: mandatory real replay missing or stale for current bin/candidate; run a passing run-script that compares both \"ref\" and \"cand\" after the latest build-exe")
    _ → failIO "finish accepted U1 before replay"
  putStrLn "PASS finish rejected U1 before replay"
  executeAction cfg (run-script "compare the U1 filter with the reference" filterReplay) >>= expectedOK "U1 replay passed"
  putStrLn "PASS U1 batch replay on empty, multiline Unicode, unterminated and filtered input"
  executeAction cfg (finish "replayed U1") >>= λ where
    (finished _) → putStrLn "PASS finish audited the four sealed trees"
    (rejected e) → failIO e
    _ → failIO "expected a finished session"

main : IO ⊤
main = currentDirectory >>= λ repo → withPrivateTemp (repo ++ˢ "/tmp/v3-e2e") (run repo)
