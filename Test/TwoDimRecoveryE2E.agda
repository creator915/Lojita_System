{-# OPTIONS --guardedness #-}
module Test.TwoDimRecoveryE2E where

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; length; reverse; take)
open import Data.Maybe using (Maybe; just; nothing; is-nothing)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; unlines; lines; words; toList) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
open import IO.Primitive.Finite using (putStrLn; readFile)
open import OwnershipIO using (RunningIO)
open import OwnershipIO.FFI
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp)
open import Code using (code; sig; plain; set; import′; everything; _==ˢ_; elemᵇ; filterᵇ; eqList; modName)
open import Code.AI using (ServiceBackend; ScriptedBackend)
open import Code.Protocol using (AIReq; AIReply; bindNode; forkNode; propose; accept; aiReply)
open import Code.SExpr using (str; list; sym; showSExpr)
open import Code.NodeTransport using (moduleKey; moduleQName)
import Code.Tree as Tree
open import Code.SessionProtocol
open import Code.SessionRunner using (SessionConfig; sessionConfig; ActionResult; accepted; rejected; finished; executeAction)
open import Code.SessionWorkspace using (partialTreeRef; treeRef; loadClosure; baseCodes; loadPartialBases; PartialSealed; treeEpoch)
import Store.CAS as CAS
open import Store.Verify using (verifyCommitDAG)
open import Test.HarnessPure using (submission)
open import Test.EndToEndPolyTransport using (header; useAs; decl; newUnits; assert; require; expectedOK; kid)

-- Every stage goes through executeAction, the scoped frontend and the real
-- compiler. A proposal is counted at the bound ownership node.
common : String
common = unlines
  ( "open import Data.Bool using (Bool; true; false; if_then_else_)"
  ∷ "open import Data.Char as C using (Char)"
  ∷ "open import Data.List as L using (List; []; _∷_)"
  ∷ "open import Data.Maybe using (Maybe; just; nothing)"
  ∷ "open import Data.Product using (_×_; _,_; proj₁; proj₂)"
  ∷ "open import Data.String as S using (String; toList; fromList; fromChar; _++_)"
  ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)" ∷ "" ∷ [])

-- A definition and a whole-line reference link share the first bracketed
-- field. The two passes operate on arbitrary keys, labels and destinations.
definitionParser : String
definitionParser = unlines
  ( "definition : String → Maybe (String × String)"
  ∷ "definition line with toList line"
  ∷ "... | '[' ∷ cs with L.break (λ c → C._≟_ c ']') cs"
  ∷ "...   | key , ']' ∷ ':' ∷ ' ' ∷ url = just (fromList key , fromList url)"
  ∷ "...   | _ = nothing"
  ∷ "definition line | _ = nothing" ∷ "" ∷ [])

linkParser : String
linkParser = unlines
  ( "link : String → Maybe (String × String)"
  ∷ "link line with toList line"
  ∷ "... | '[' ∷ cs with L.break (λ c → C._≟_ c ']') cs"
  ∷ "...   | label , ']' ∷ '[' ∷ rest with L.break (λ c → C._≟_ c ']') rest"
  ∷ "...     | key , ']' ∷ [] = just (fromList label , fromList key)"
  ∷ "...     | _ = nothing"
  ∷ "link line | '[' ∷ cs | _ = nothing"
  ∷ "link line | _ = nothing"
  ∷ ""
  ∷ "lookupURL : String → List (String × String) → Maybe String"
  ∷ "lookupURL key [] = nothing"
  ∷ "lookupURL key ((k , u) ∷ rest) = if primStringEquality k key then just u else lookupURL key rest" ∷ "" ∷ [])

lineKinds : String
lineKinds = unlines
  ( "data LineKind : Set where"
  ∷ "  KRefDef : LineKind"
  ∷ "  KText : String → LineKind" ∷ "" ∷ [])

parse₀ : Bool → String
parse₀ spec = header "Gen.T0.ParseLine" ++ˢ common ++ˢ lineKinds
  ++ˢ (if spec then "" else definitionParser)
  ++ˢ decl spec "classify : String → LineKind"
    "classify s with definition s\n... | just _ = KRefDef\n... | nothing = KText s"
  ++ˢ decl spec "parseLine₀ : LineKind → Maybe String"
    "parseLine₀ KRefDef = nothing\nparseLine₀ (KText s) = just s"
  ++ˢ decl spec "dropDef : parseLine₀ KRefDef ≡ nothing" "dropDef = refl"
  ++ˢ decl spec "keepText : (s : String) → parseLine₀ (KText s) ≡ just s" "keepText s = refl"

escape : String → Bool → Bool → String
escape epoch upper spec = header ("Gen." ++ˢ epoch ++ˢ ".Escape") ++ˢ common
  ++ˢ (if upper ∧ not spec then useAs "Gen.T0.Escape" "Base" else "")
  ++ˢ decl spec "escapeChar : Char → String" (if upper then
    "-- The retained source delegates the original two cases to T0.\nescapeChar '>' = \"&gt;\"\nescapeChar c = Base.escapeChar c"
    else "escapeChar '<' = \"&lt;\"\nescapeChar '&' = \"&amp;\"\nescapeChar c = fromChar c")
  ++ˢ decl spec "lt : escapeChar '<' ≡ \"&lt;\"" "lt = refl"
  ++ˢ decl spec "amp : escapeChar '&' ≡ \"&amp;\"" "amp = refl"
  ++ˢ (if upper then decl spec "gt : escapeChar '>' ≡ \"&gt;\"" "gt = refl" else "")

singlePass : Bool → String
singlePass spec = header "Gen.T0.Root" ++ˢ common
  ++ˢ (if spec then "" else useAs "Gen.T0.ParseLine" "P" ++ˢ useAs "Gen.T0.Escape" "E")
  ++ˢ decl spec "mdToHtml : String → String"
    "mdToHtml doc = S.unlines (L.map (λ x → \"<p>\" ++ S.concat (L.map E.escapeChar (toList x)) ++ \"</p>\") (L.mapMaybe (λ s → P.parseLine₀ (P.classify s)) (S.lines doc)))"

-- With the single-pass projection, the common first line and the two erased
-- definition lines yield equal observations. The specification asks which
-- document resolves the forward link to a, so it requires distinct results.
obstructed : String → Bool → String
obstructed node spec = header node ++ˢ common ++ˢ useAs "Gen.T0.ParseLine" "Base"
  ++ˢ (if spec then "" else useAs "Gen.T1.ParseLine" "P" ++ˢ useAs "Gen.T1.Escape" "E")
  ++ˢ decl spec "parse : String → Maybe String" "parse = P.parse"
  ++ˢ decl spec "commutes : (s : String) → parse s ≡ Base.parseLine₀ (Base.classify s)" "commutes = P.commutes"
  ++ˢ decl spec "pointsToA : List (Maybe String) → Bool" "pointsToA = P.pointsToA"
  ++ˢ decl spec "linkA : pointsToA (parse \"[go][1]\" ∷ parse \"[1]: a\" ∷ []) ≡ true" "linkA = P.linkA"
  ++ˢ decl spec "linkB : pointsToA (parse \"[go][1]\" ∷ parse \"[1]: b\" ∷ []) ≡ false" "linkB = P.linkB"
  ++ˢ (if node ==ˢ "Gen.T1.Root" then
    decl spec "escapeHTML : Char → String" "escapeHTML = E.escapeChar"
    ++ˢ decl spec "escapeGT : escapeHTML '>' ≡ \"&gt;\"" "escapeGT = E.gt" else "")

refutation : String → String
refutation node = header "LostReference" ++ˢ common ++ˢ useAs "Gen.T0.ParseLine" "Base" ++ˢ useAs node "Spec"
  ++ˢ witness
  where
    witness : String
    witness = unlines
      ( "open import Data.Empty using (⊥)"
      ∷ ""
      ∷ "erased : Base.parseLine₀ (Base.classify \"[1]: a\") ≡ Base.parseLine₀ (Base.classify \"[1]: b\")"
      ∷ "erased = refl"
      ∷ ""
      ∷ "sameLine : Spec.parse \"[1]: a\" ≡ Spec.parse \"[1]: b\""
      ∷ "sameLine = trans (Spec.commutes \"[1]: a\") (trans erased (sym (Spec.commutes \"[1]: b\")))"
      ∷ ""
      ∷ "distinct : true ≡ false → ⊥"
      ∷ "distinct ()"
      ∷ ""
      ∷ "absurd : ⊥"
      ∷ "absurd = distinct (trans (sym Spec.linkA) (trans (cong (λ x → Spec.pointsToA (Spec.parse \"[go][1]\" ∷ x ∷ [])) sameLine) Spec.linkB))" ∷ "" ∷ [])

refsType resultType : String
refsType = "List (String × String)"
resultType = "Maybe (String × String)"

collectSig resolveSig : String
collectSig = "collect : List String → " ++ˢ refsType
resolveSig = "resolve : " ++ˢ refsType ++ˢ " → String → " ++ˢ resultType

collectRefs : Bool → String
collectRefs spec = header "Gen.T0v2.CollectRefs" ++ˢ common
  ++ˢ (if spec then "" else definitionParser)
  ++ˢ decl spec collectSig "collect = L.mapMaybe definition"

resolveBody : String
resolveBody = unlines
  ( "resolve refs \"\" = nothing"
  ∷ "resolve refs line with definition line"
  ∷ "... | just _ = nothing"
  ∷ "... | nothing with link line"
  ∷ "...   | nothing = just (line , \"\")"
  ∷ "...   | just (label , key) with lookupURL key refs"
  ∷ "...     | nothing = just (line , \"\")"
  ∷ "...     | just url = just (label , url)" ∷ "" ∷ [])

resolveRefs : Bool → String
resolveRefs spec = header "Gen.T0v2.Resolve" ++ˢ common
  ++ˢ (if spec then "" else "open import Agda.Builtin.String using (primStringEquality)\n" ++ˢ definitionParser ++ˢ linkParser)
  ++ˢ decl spec resolveSig resolveBody

references : Bool → String
references spec = header "Gen.T1v2.References" ++ˢ common
  ++ˢ useAs "Gen.T0v2.CollectRefs" "Collect" ++ˢ useAs "Gen.T0v2.Resolve" "Resolve"
  ++ˢ decl spec collectSig "collect = Collect.collect"
  ++ˢ decl spec resolveSig "resolve = Resolve.resolve"
  ++ˢ decl spec "collectLaw : (doc : List String) → collect doc ≡ Collect.collect doc" "collectLaw doc = refl"
  ++ˢ decl spec "resolveLaw : (env : List (String × String)) (s : String) → resolve env s ≡ Resolve.resolve env s"
                "resolveLaw env s = refl"

paragraphs : String
paragraphs = unlines
  ( "escaped : String → String"
  ∷ "escaped s = S.concat (L.map E.escapeChar (toList s))"
  ∷ ""
  ∷ "paragraph : String × String → String"
  ∷ "paragraph (s , \"\") = \"<p>\" ++ escaped s ++ \"</p>\\n\""
  ∷ "paragraph (s , url) = \"<p><a href=\\\"\" ++ escaped url ++ \"\\\">\" ++ escaped s ++ \"</a></p>\\n\"" ∷ "" ∷ [])

square : String
square = unlines
  ( "open import Context.PolyTransport using (TransportsPoly; idPort)"
  ∷ "open import Data.Unit using (⊤)"
  ∷ "square : TransportsPoly (idPort (List String × String)) (idPort (Maybe (String × String))) (λ _ → ⊤)"
  ∷ "  (λ z → Base.resolve (Base.collect (proj₁ z)) (proj₂ z)) (λ z → resolve (collect (proj₁ z)) (proj₂ z))"
  ∷ "square (doc , s) .(doc , s) _ refl = trans (cong (λ env → Base.resolve env s) (sym (R.collectLaw doc))) (sym (R.resolveLaw (collect doc) s))" ∷ "" ∷ [])

world = "open import Context.World using (CliApp; CliCaps; readStdinAllW; env∈Cli; writeStdoutStrW; tty∈Cli; decodeUtf8Lossy; pure; _>>=w_; _>>w_)\n"

twoPass : Bool → Bool → String
twoPass upper spec = header (prefix ++ˢ "Root") ++ˢ common ++ˢ (if upper then world else "")
  ++ˢ (if spec then "" else kids ++ˢ useAs (prefix ++ˢ "Escape") "E" ++ˢ paragraphs)
  ++ˢ decl spec collectSig (if upper then "collect = R.collect" else "collect = Collect.collect")
  ++ˢ decl spec resolveSig "resolve = R.resolve"
  ++ˢ decl spec "mdToHtml : String → String"
    "mdToHtml s = let doc = S.lines s in S.concat (L.map paragraph (L.mapMaybe (resolve (collect doc)) doc))"
  ++ˢ (if upper then decl spec "app : CliApp CliCaps"
    "app = readStdinAllW env∈Cli >>=w λ bs → writeStdoutStrW tty∈Cli (mdToHtml (decodeUtf8Lossy bs)) >>w pure 0" else "")
  ++ˢ (if upper ∧ not spec then useAs "Gen.T0v2.Root" "Base" ++ˢ square else "")
  where
    prefix = if upper then "Gen.T1v2." else "Gen.T0v2."
    kids = if upper then useAs (prefix ++ˢ "References") "R"
           else useAs (prefix ++ˢ "CollectRefs") "Collect" ++ˢ useAs (prefix ++ˢ "Resolve") "R"

-- Both descriptors use the public session wire syntax. The final vertical
-- square relates composition of the two base units to both upper units.
initialLift finalLift baseTransport partialTransport : String
initialLift = unlines
  ( "(lift \"Gen.T0.Root\" \"Gen.T1.Root\""
  ∷ "((\"Gen.T0.Escape\" \"Gen.T1.Escape\") (\"Gen.T0.ParseLine\" \"Gen.T1.ParseLine\"))"
  ∷ "((\"Gen.T0.ParseLine.parseLine₀\" \"Gen.T1.Root.parse\" \"Gen.T1.Root.commutes\")))" ∷ [])

baseTransport = unlines
  ( "(poly-transport \"Gen.T0.Root\" \"Gen.T0v2.Root\""
  ∷ "((keep \"Gen.T0.Escape\" \"Gen.T0v2.Escape\")"
  ∷ "(move (\"Gen.T0.ParseLine\") (\"Gen.T0v2.CollectRefs\" \"Gen.T0v2.Resolve\") ())) ())" ∷ [])

finalLift = unlines
  ( "(lift \"Gen.T0v2.Root\" \"Gen.T1v2.Root\""
  ∷ "((move (\"Gen.T0v2.CollectRefs\" \"Gen.T0v2.Resolve\") (\"Gen.T1v2.References\") ())"
  ∷ "(\"Gen.T0v2.Escape\" \"Gen.T1v2.Escape\" (lift \"Gen.T0v2.Escape\" \"Gen.T1v2.Escape\" () ())))"
  ∷ "(((\"Gen.T0v2.Root.collect\" \"Gen.T0v2.Root.resolve\")"
  ∷ "(\"Gen.T1v2.Root.collect\" \"Gen.T1v2.Root.resolve\") \"Gen.T1v2.Root.square\")))" ∷ [])

partialTransport = "(poly-transport \"Gen.T1.Root\" \"Gen.T1v2.Root\" ((keep \"Gen.T1.Escape\" \"Gen.T1v2.Escape\")) ())"

reason : String
reason = "The single pass erases both reference destinations."

refute : String → String
refute node = showSExpr (list (sym "submission" ∷ list (sym "kind" ∷ [ sym "refute-lift" ])
  ∷ list (sym "why" ∷ [ str reason ]) ∷ list (sym "refute" ∷ [ str (refutation node) ]) ∷ []))

plan : String → String → List (String × String) → List String → String
plan node body specs extra = submission ("implement " ++ˢ node) body specs (newUnits node extra)

proposal : String → Maybe String
proposal n@"Gen.T0.Root" = just (plan n (singlePass false)
  (("Gen.T0.ParseLine" , parse₀ true) ∷ [ "Gen.T0.Escape" , escape "T0" false true ]) [])
proposal n@"Gen.T0.ParseLine" = just (plan n (parse₀ false) [] [ "definition" ])
proposal n@"Gen.T0.Escape" = just (plan n (escape "T0" false false) [] [])
proposal n@"Gen.T1.Root" = just (plan n (obstructed n false)
  (("Gen.T1.ParseLine" , obstructed "Gen.T1.ParseLine" true) ∷ [ "Gen.T1.Escape" , escape "T1" true true ]) [])
proposal n@"Gen.T1.Escape" = just (plan n (escape "T1" true false) [] [])
proposal n@"Gen.T1.ParseLine" = just (refute n)
proposal n@"Gen.T0v2.Root" = just (plan n (twoPass false false)
  (("Gen.T0v2.CollectRefs" , collectRefs true) ∷ [ "Gen.T0v2.Resolve" , resolveRefs true ]) ("escaped" ∷ [ "paragraph" ]))
proposal n@"Gen.T0v2.CollectRefs" = just (plan n (collectRefs false) [] [ "definition" ])
proposal n@"Gen.T0v2.Resolve" = just (plan n (resolveRefs false) [] ("definition" ∷ "link" ∷ [ "lookupURL" ]))
proposal n@"Gen.T1v2.Root" = just (plan n (twoPass true false)
  [ "Gen.T1v2.References" , references true ] ("escaped" ∷ "paragraph" ∷ [ "square" ]))
proposal n@"Gen.T1v2.References" = just (plan n (references false) [] [])
proposal _ = nothing

Calls = IORef (List (String × String))

callCount : Calls → String → String → IO ℕ
callCount calls event node = readIORef calls >>= λ xs → return
  (length (filterᵇ (λ { (e , n) → (e ==ˢ event) ∧ (n ==ˢ node) }) xs))

service : Calls → IO (RunningIO AIReq AIReply (⊤ × ⊤))
service calls = newIORef "" >>= λ slot → return (record { onCall = request slot ; onStop = return (tt , tt) })
  where
    note : String → String → IO ⊤
    note event node = modifyIORef calls ((event , node) ∷_)
    request : IORef String → AIReq → IO AIReply
    request slot (bindNode n _) = note "bind" n >> writeIORef slot n >> return (aiReply "" n)
    request slot (forkNode n) = note "fork" n >> return (aiReply "" n)
    request slot (accept _) = return (aiReply "" "")
    request slot (propose prompt retry _) = do
      n ← readIORef slot
      note "propose" n
      reply ← if retry then retryReply n else require ("unexpected AI call at " ++ˢ n) (proposal n)
      return (aiReply reply n)
      where
        retryReply : String → IO String
        retryReply n = if (n ==ˢ "Gen.T1.Root") ∧ elemᵇ _==ˢ_ "CHILD: Gen.T1.ParseLine" (lines prompt)
          then return (refute n) else failIO (n ++ˢ " unexpectedly retried\n" ++ˢ unlines (reverse (take 18 (reverse (lines prompt)))))

referenceProgram : String
referenceProgram = unlines
  ( "import html, re, sys"
  ∷ "doc = sys.stdin.read().splitlines()"
  ∷ "definition = re.compile(r'\\[([^\\]]+)\\]: (.+)')"
  ∷ "link = re.compile(r'\\[([^\\]]+)\\]\\[([^\\]]+)\\]')"
  ∷ "refs = {}"
  ∷ "for line in doc:"
  ∷ "    m = definition.fullmatch(line)"
  ∷ "    if m: refs.setdefault(m[1], m[2])"
  ∷ "def escape(s): return html.escape(s, quote=False)"
  ∷ "for line in doc:"
  ∷ "    if not line or definition.fullmatch(line): continue"
  ∷ "    m = link.fullmatch(line)"
  ∷ "    if m and m[2] in refs:"
  ∷ "        body = '<a href=\"' + escape(refs[m[2]]) + '\">' + escape(m[1]) + '</a>'"
  ∷ "    else:"
  ∷ "        body = escape(line)"
  ∷ "    print('<p>' + body + '</p>')" ∷ "" ∷ [])

replay : String
replay = unlines
  ( "{-# OPTIONS --guardedness #-}"
  ∷ "module MarkdownReplay where"
  ∷ "open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)"
  ∷ "open import Data.List using (List; []; _∷_)"
  ∷ "open import Data.String using (String)"
  ∷ "open import Data.Product using (_×_; _,_; proj₂)"
  ∷ "open import Data.Unit using (⊤; tt)"
  ∷ "open import Agda.Builtin.String using (primStringEquality)"
  ∷ "import IO.Primitive as IO"
  ∷ "import IO.Primitive.Finite as F"
  ∷ "open import Ownership"
  ∷ "open import OwnershipIO.FFI using (procResult; exitFailure)"
  ∷ "open import SessionEnv"
  ∷ ""
  ∷ "cases : List (String × String)"
  ∷ "cases = (\"[go][1]\\n<script>&\\n\\n[1]: https://agda.io\\n\" , \"<p><a href=\\\"https://agda.io\\\">go</a></p>\\n<p>&lt;script&gt;&amp;</p>\\n\")"
  ∷ "      ∷ (\"[go][1]\\n[1]: a\" , \"<p><a href=\\\"a\\\">go</a></p>\\n\")"
  ∷ "      ∷ (\"[go][1]\\n[1]: b\" , \"<p><a href=\\\"b\\\">go</a></p>\\n\")"
  ∷ "      ∷ (\"[λ&][doc]\\n[doc]: https://x/?a&b\\n[x][missing]\" , \"<p><a href=\\\"https://x/?a&amp;b\\\">λ&amp;</a></p>\\n<p>[x][missing]</p>\\n\")"
  ∷ "      ∷ (\"\" , \"\") ∷ []"
  ∷ "agrees : String → ProcOut → ProcOut → Bool"
  ∷ "agrees expected (procResult 0 x \"\") (procResult 0 y \"\") = primStringEquality expected x ∧ primStringEquality x y"
  ∷ "agrees _ _ _ = false"
  ∷ "Live : St"
  ∷ "Live = Dir ((\"procExec\" , Chan (Srv ProcReq ProcOut (Dir []))) ∷ [])"
  ∷ "compareAll : List (String × String) → Prog SessionΨ Live Live Bool"
  ∷ "compareAll [] = done true"
  ∷ "compareAll ((doc , want) ∷ rest) = call \"procExec\" (procReq \"ref\" [] doc) >>= λ ref →"
  ∷ "  call \"procExec\" (procReq \"cand\" [] doc) >>= λ cand → compareAll rest >>= λ ok → done (agrees want ref cand ∧ ok)"
  ∷ "probe : Prog SessionΨ (Dir []) (Dir []) Bool"
  ∷ "probe = mkdir \"procExec\" >> open′ \"procExec\" >> compareAll cases >>= λ ok → stop \"procExec\" >> rmdir \"procExec\" >> done ok"
  ∷ "main : IO.IO ⊤"
  ∷ "main = evalIO sessionEnv probe tt IO.>>= λ r → if proj₂ r then F.putStrLn \"Markdown replay passed\" else exitFailure" ∷ "" ∷ [])

acceptedText : ActionResult → IO String
acceptedText (accepted msg) = return msg
acceptedText (rejected e) = failIO e
acceptedText (finished _) = failIO "unexpected finish"

refused : String → ActionResult → IO ⊤
refused want (rejected msg) = assert msg (want ==ˢ msg)
refused want _ = failIO ("expected rejection: " ++ˢ want)

culprit : List String → Bool
culprit [] = false
culprit (s ∷ ss) with words s
... | "CULPRIT_BASE_UNITS:" ∷ qs = elemᵇ _==ˢ_ "Gen.T0.ParseLine.parseLine₀" qs
... | _ = culprit ss

-- A well-formed Merkle DAG alone does not authorize a child mount. Include
-- invalid parent code under an otherwise genuine preserved Escape home.
checkPartialReader : String → String → String → IO ⊤
checkPartialReader ws base partial = do
  let store = ws ++ˢ "/store"
  c ← CAS.getCommit store partial >>= require "missing obstruction commit"
  assert "partial did not pin t0" (eqList _==ˢ_ (CAS.parents c) [ base ])
  readHome ← CAS.newCommitHomeReader store
  home ← readHome c >>= require "missing obstruction snapshot"
  let inject = λ name bad → do
        parent ← CAS.storeTreeCommit store [] "bad_parent" "" (Tree.node [] , bad , [] , [] , tt)
        key ← CAS.storeTreeCommit store [ parent ] name "" home
        verifyCommitDAG store key >>= assert "malformed negative fixture"
        CAS.writeRef store (partialTreeRef name) key
      badModule = code (moduleQName "Gen.Other.Bad") []
  inject "open_parent" (badModule [ sig plain "assumption" (set 0) ])
  inject "forbidden_parent" (badModule [ import′ (moduleQName "Ownership") false everything [] ])
  CAS.writeRef store (partialTreeRef "wrong_epoch") partial
  sha256 "absent commit" >>= CAS.writeRef store (partialTreeRef "missing_commit")
  ps ← loadPartialBases ws
  assert "partial reader admitted an invalid source" (eqList _==ˢ_ (map (λ p → treeEpoch (PartialSealed.sealed p)) ps) [ "t1" ])

run : String → String → IO ⊤
run repo ws = do
  calls ← newIORef []
  let cfg = sessionConfig repo ws "Resolve forward Markdown links and escape raw HTML"
        (refSpec (local "/usr/bin/python3") ("-c" ∷ referenceProgram ∷ []) 30000)
        (ScriptedBackend []) (λ _ → ServiceBackend (service calls))
      act = executeAction cfg
      t1 = λ name → drive-tree name "lift the single pass" (obstructed "Gen.T1.Root" true) [ "t0" ] (just initialLift)
      store = ws ++ˢ "/store"
      tipOf = λ ref → CAS.readRef store ref >>= require ("missing ref " ++ˢ ref)
      homeOf = λ key → CAS.getCommit store key >>= require "missing commit" >>= λ c →
        CAS.getHomeNode store (CAS.rootHome c) >>= require "missing snapshot"
      turns = λ node count → callCount calls "propose" node >>= λ n → assert ("proposal count for " ++ˢ node) (n ≡ᵇ count)
      asleep = λ node → do
        turns node 0
        callCount calls "bind" node >>= λ n → assert ("bound " ++ˢ node) (n ≡ᵇ 0)
        callCount calls "fork" node >>= λ n → assert ("forked " ++ˢ node) (n ≡ᵇ 0)
  act (drive-tree "t0" "single pass" (singlePass true) [] nothing) >>= expectedOK "ok t0"
  t₀ ← tipOf (treeRef "t0")
  putStrLn "PASS t0 sealed the single-pass parser and escape module"

  msg ← act (t1 "t1") >>= acceptedText
  let diagnostic = lines msg
  assert msg (eqList _==ˢ_ (take 1 diagnostic) [ "lift-obstruction t1 — " ++ˢ reason ]
    ∧ culprit diagnostic ∧ elemᵇ _==ˢ_ "PRESERVED_CHILDREN: Gen.T1.Escape" diagnostic)
  turns "Gen.T1.Escape" 1
  turns "Gen.T1.ParseLine" 1
  turns "Gen.T1.Root" 2
  readFile (ws ++ˢ "/trees/t1/verdict") >>= λ v → assert v (v ==ˢ "lift-obstruction")
  act (build-exe "obstructed root" "Gen.T1.Root.app") >>= refused
    "build-exe: entry module 'Gen.T1.Root' is not exported by any verified (ok) Dialectica tree; verify it via drive-tree first"
  loadClosure ws [ "t1" ] >>= λ b → assert "obstructed direct base resolved" (is-nothing b)
  partial ← tipOf (partialTreeRef "t1")
  verifyCommitDAG store partial >>= assert "invalid partial DAG"
  checkPartialReader ws t₀ partial
  old ← homeOf partial
  assert "partial owns exactly Escape" (eqList _==ˢ_ (map proj₁ (CAS.kids old)) [ "Gen.T1.Escape" ])
  putStrLn "PASS t1 refuted the lift and preserved Gen.T1.Escape"

  before ← readIORef calls
  act (t1 "t1_retry") >>= refused "drive-tree: identical base closure, specification, and LiftSpec already produced lift-obstruction; refactor CULPRIT_BASE_UNITS in a new base tree or revise the upper specification/LiftSpec before retrying"
  after ← readIORef calls
  assert "identical retry contacted AI" (length before ≡ᵇ length after)
  putStrLn "PASS identical retry rejected before any node call"

  act (drive-tree-with "t0_v2" "collect definitions, then resolve links" (twoPass false true) [ "t0" ] nothing (just baseTransport))
    >>= expectedOK "ok t0_v2"
  asleep "Gen.T0v2.Escape"
  turns "Gen.T0.Escape" 1
  t₀′ ← tipOf (treeRef "t0_v2")
  a ← homeOf t₀ >>= kid "Gen.T0.Escape"
  b ← homeOf t₀′ >>= kid "Gen.T0v2.Escape"
  assert "base Escape HomeNode changed" (a ==ˢ b)
  putStrLn "PASS t0_v2 kept the original Escape with zero proposals"

  act (drive-tree-with "t1_v2" "lift the two passes and reuse verified HTML escaping"
    (twoPass true true) [ "t0_v2" ] (just finalLift) (just partialTransport)) >>= expectedOK "ok t1_v2"
  asleep "Gen.T1v2.Escape"
  turns "Gen.T1.Escape" 1
  turns "Gen.T1v2.References" 1
  t₁′ ← tipOf (treeRef "t1_v2")
  verifyCommitDAG store t₁′ >>= assert "invalid recovery DAG"
  c ← CAS.getCommit store t₁′ >>= require "missing final commit"
  assert "incorrect recovery parents" (eqList _==ˢ_ (CAS.parents c) (t₀′ ∷ [ partial ]))
  kept ← kid "Gen.T1.Escape" old
  mounted ← homeOf t₁′ >>= kid "Gen.T1v2.Escape"
  assert "upper Escape HomeNode changed" (kept ==ˢ mounted)
  readFile (ws ++ˢ "/generated/t1_v2/Gen/T1/Escape.agda") >>= λ s → assert "lost authored Escape" (s ==ˢ escape "T1" true false)
  closure ← loadClosure ws [ "t1_v2" ] >>= require "unreadable recovered closure"
  assert "partial root shell appeared among completed ancestors"
    (not (elemᵇ _==ˢ_ "Gen.T1.Root" (map (λ m → moduleKey (modName m)) (baseCodes closure))))
  putStrLn "PASS t1_v2 mounted the partial Escape with zero proposals, identical source and HomeNode"

  act (build-exe "compile recovered CliApp" "Gen.T1v2.Root.app") >>= acceptedText
  act (run-script "compare candidate and reference Markdown output" replay) >>= expectedOK "Markdown replay passed"
  act (finish "Replayed reference links and HTML escaping") >>= λ where
    (finished _) → putStrLn "PASS Markdown replay and finish"
    (rejected e) → failIO e
    _ → failIO "expected finish"

main : IO ⊤
main = enableLineBuffering >> currentDirectory >>= λ repo → withPrivateTemp (repo ++ˢ "/tmp/v7-pandoc") (run repo)
