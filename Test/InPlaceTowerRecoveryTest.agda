{-# OPTIONS --guardedness #-}
module Test.InPlaceTowerRecoveryTest where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; length; reverse; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; unlines; lines; words) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import IO.Primitive using (IO; return; _>>=_)
open import IO.Primitive.Finite using (putStrLn; readFile)
open import OwnershipIO using (RunningIO)
open import OwnershipIO.FFI
open import OwnershipIO.MetaFFI using (_>>_; withPrivateTemp)
open import Code using (decls; QName; unit; ext; ⊥; _==ˢ_; _==ᴺ_; elemᵇ; anyᵇ; allᵇ; eqList; units; uname)
open import Code.Transport using (nullᵇ; keep; Plan; plan; Proarrow; _⇝_; Memory; notesOf; crossChildMemory; unmappedChildMemory; absorbDeadMemory; inherit)
open import Code.Protocol using (AIReq; AIReply; bindNode; forkNode; propose; accept; aiReply)
open import Code.AI using (ScriptedBackend; ServiceBackend)
open import Code.SExpr using (list; sym; str; showSExpr; parseSExpr)
open import Code.Parse using (parseMemory; decodeCode)
open import Code.NodeTransport using (moduleQName)
open import Code.SessionProtocol
open import Code.SessionRunner using (sessionConfig; ActionResult; finished; rejected; executeAction; auditTrees)
open import Code.SessionWorkspace using (treeRef; partialTreeRef; loadClosure; baseCodes)
import Store.CAS as CAS
open import Store.Verify using (verifyCommitDAG)
open import Test.HarnessPure using (submission)
open import Test.EndToEndPolyTransport using (header; useAs; decl; newUnits; assert; require; expectedOK; kid)
open import Test.TwoDimRecoveryE2E using (common; definitionParser; linkParser; resolveBody; collectSig; resolveSig; paragraphs; world;
  escape; reason; replay; referenceProgram; acceptedText; Calls; callCount)

t₀ t₁ t₂ p₀ p₁ p₂ e₀ e₁ e₂ toc collect resolve : String
t₀ = "Gen.T0.Root"
t₁ = "Gen.T1.Root"
t₂ = "Gen.T2.Root"
p₀ = "Gen.T0.ParseLine"
p₁ = "Gen.T1.ParseLine"
p₂ = "Gen.T2.ParseLine"
e₀ = "Gen.T0.Escape"
e₁ = "Gen.T1.Escape"
e₂ = "Gen.T2.Escape"
toc = "Gen.T2.PureTOC"
collect = "Gen.T0.CollectRefs"
resolve = "Gen.T0.Resolve"

member : String → String → QName
member m n = moduleQName (m ++ˢ "." ++ˢ n)

parserNote splitWhy : String
parserNote = "Definition lines erase the destination in the single-pass projection."
splitWhy = "Collect definitions before resolving forward links."

route : Proarrow
route = ext (member p₀ "parseLine₀") ⇝ ext (member resolve "resolve")

-- A surviving source can split as well. Private notes and another child's
-- identically spelled local unit cannot travel along this edge.
private
  split = plan splitWhy [] (route ∷ [ ext (member p₀ "parseLine₀") ⇝ ext (member p₀ "parseLine₀") ])
  sourceMemory : Memory
  sourceMemory = (unit (member p₀ "parseLine₀") , [ parserNote ]) ∷ [ unit (member p₀ "definition") , [ "private" ] ]
  _ : crossChildMemory split ((moduleQName p₀ , sourceMemory) ∷ [ moduleQName e₀ , sourceMemory ]) (moduleQName resolve)
    ≡ [ unit (member resolve "resolve") , (parserNote ∷ [ splitWhy ]) ]
  _ = refl
  _ : notesOf (inherit split (absorbDeadMemory (moduleQName p₀)
        (unmappedChildMemory split [ moduleQName resolve ] (moduleQName p₀) sourceMemory) [])) ⊥ ≡ [ "private" ]
  _ = refl

singleParser : Bool → String
singleParser spec = header p₀ ++ˢ common ++ˢ (if spec then "" else definitionParser)
  ++ˢ decl spec "parseLine₀ : String → Maybe String"
       "parseLine₀ s with definition s\n... | just _ = nothing\n... | nothing = just s"

singleRoot : Bool → String
singleRoot spec = header t₀ ++ˢ common ++ˢ (if spec then "" else useAs p₀ "P" ++ˢ useAs e₀ "E")
  ++ˢ decl spec "mdToHtml : String → String"
    "mdToHtml s = S.unlines (L.map (λ l → \"<p>\" ++ S.concat (L.map E.escapeChar (toList l)) ++ \"</p>\") (L.mapMaybe P.parseLine₀ (S.lines s)))"

collector : Bool → String
collector spec = header collect ++ˢ common ++ˢ (if spec then "" else definitionParser)
  ++ˢ decl spec collectSig "collect = L.mapMaybe definition"

resolver : Bool → Bool → String
resolver revised spec = header resolve ++ˢ common ++ˢ (if spec then "" else
  "open import Agda.Builtin.String using (primStringEquality)\n" ++ˢ definitionParser ++ˢ linkParser)
  ++ˢ decl spec resolveSig resolveBody
  ++ˢ (if revised then decl spec "empty : resolve [] \"\" ≡ nothing" "empty = refl"
       else if spec then "" else "resolveLine : List (String × String) → String → Maybe (String × String)\nresolveLine = resolve\n")

baseRoot : Bool → String
baseRoot spec = header t₀ ++ˢ common ++ˢ (if spec then "" else
  useAs collect "C₀" ++ˢ useAs resolve "R" ++ˢ useAs e₀ "E" ++ˢ paragraphs)
  ++ˢ decl spec collectSig "collect = C₀.collect"
  ++ˢ decl spec resolveSig "resolve = R.resolve"
  ++ˢ decl spec "mdToHtml : String → String"
    "mdToHtml s = let doc = S.lines s in S.concat (L.map paragraph (L.mapMaybe (resolve (collect doc)) doc))"

-- The same child and root signatures are used to check each obstruction.
-- The universal square equates the visible line with the lower projection.
projection : String → Bool → Bool → Bool → String
projection name top strong spec = header name ++ˢ common ++ˢ useAs base "Base"
  ++ˢ (if root ∧ not spec then useAs parser "P" ++ˢ useAs esc "E" ++ˢ (if top then useAs toc "TOC" else "") else "")
  ++ˢ (if root ∧ top then world else "")
  ++ˢ decl spec "parse : String → Maybe String" (if root then "parse = P.parse" else "parse = Base." ++ˢ port)
  ++ˢ decl spec ("commutes : (s : String) → parse s ≡ Base." ++ˢ port ++ˢ " s")
       (if root then "commutes = P.commutes" else "commutes s = refl")
  ++ˢ (if strong then destination spec (if root then "P" else "Base") else "")
  ++ˢ (if top then decl spec collectSig (if root then "collect = P.collect" else "collect = Base.collect")
         ++ˢ decl spec resolveSig (if root then "resolve = P.resolve" else "resolve = Base.resolve") else "")
  ++ˢ (if root then decl spec "escapeHTML : Char → String" "escapeHTML = E.escapeChar" else "")
  ++ˢ (if root ∧ top then
     decl spec "tocTitle : String → String" "tocTitle = TOC.title"
     ++ˢ (if spec then "" else paragraphs)
     ++ˢ decl spec "mdToHtml : String → String"
       "mdToHtml s = let doc = S.lines s in S.concat (L.map paragraph (L.mapMaybe (resolve (collect doc)) doc))"
     ++ˢ decl spec "app : CliApp CliCaps"
       "app = readStdinAllW env∈Cli >>=w λ bs → writeStdoutStrW tty∈Cli (mdToHtml (decodeUtf8Lossy bs)) >>w pure 0" else "")
  where
    root = (name ==ˢ t₁) ∨ (name ==ˢ t₂)
    base = if top then p₁ else p₀
    port = if top then "parse" else "parseLine₀"
    parser = if top then p₂ else p₁
    esc = if top then e₂ else e₁
    destination : Bool → String → String
    destination spec alias = decl spec "pointsToA : List (Maybe String) → Bool" ("pointsToA = " ++ˢ alias ++ˢ ".pointsToA")
      ++ˢ decl spec "linkA : pointsToA (parse \"[go][1]\" ∷ parse \"[1]: a\" ∷ []) ≡ true" ("linkA = " ++ˢ alias ++ˢ ".linkA")
      ++ˢ decl spec "linkB : pointsToA (parse \"[go][1]\" ∷ parse \"[1]: b\" ∷ []) ≡ false" ("linkB = " ++ˢ alias ++ˢ ".linkB")

-- Following the split the middle level exposes the original line, plus
-- the genuine two-pass resolver. The upper specification can stay fixed.
middle : String → Bool → Bool → String
middle name adapted spec = header name ++ˢ common ++ˢ useAs resolve "R"
  ++ˢ (if spec then "" else if root then useAs p₁ "P" ++ˢ useAs e₁ "E" else
    useAs collect "C₀" ++ˢ "open import Agda.Builtin.String using (primStringEquality)\n")
  ++ˢ decl spec "parse : String → Maybe String" (if root then "parse = P.parse" else "parse = just")
  ++ˢ decl spec collectSig (if root then "collect = P.collect" else "collect = C₀.collect")
  ++ˢ decl spec resolveSig (if root then "resolve = P.resolve" else if adapted then "resolve = R.resolve" else "resolve = R.resolveLine")
  ++ˢ decl spec "commutes : (env : List (String × String)) (s : String) → resolve env s ≡ R.resolve env s"
       (if root then "commutes = P.commutes" else "commutes env s = refl")
  ++ˢ decl spec "pointsToA : List (Maybe String) → Bool" (if root then "pointsToA = P.pointsToA" else unlines
       ("pointsToA (just first ∷ rest) with resolve (collect (L.mapMaybe (λ x → x) rest)) first"
       ∷ "... | just (_ , url) = primStringEquality url \"a\"" ∷ "... | nothing = false" ∷ "pointsToA _ = false" ∷ []))
  ++ˢ decl spec "linkA : pointsToA (parse \"[go][1]\" ∷ parse \"[1]: a\" ∷ []) ≡ true" (if root then "linkA = P.linkA" else "linkA = refl")
  ++ˢ decl spec "linkB : pointsToA (parse \"[go][1]\" ∷ parse \"[1]: b\" ∷ []) ≡ false" (if root then "linkB = P.linkB" else "linkB = refl")
  ++ˢ (if root then decl spec "escapeHTML : Char → String" "escapeHTML = E.escapeChar" else "")
  where root = name ==ˢ t₁

topEscape pureTOC : Bool → String
topEscape spec = header e₂ ++ˢ common ++ˢ (if spec then "" else useAs e₁ "Base")
  ++ˢ decl spec "escapeChar : Char → String" "-- Preserve the authored delegation.\nescapeChar = Base.escapeChar"
  ++ˢ decl spec "gt : escapeChar '>' ≡ \"&gt;\"" "gt = refl"
pureTOC spec = header toc ++ˢ common
  ++ˢ decl spec "title : String → String" "-- A heading introduced at the top level.\ntitle s = \"# \" ++ s"

lift₀ lift₁ splitLift : String
lift₀ = "(lift \"Gen.T0.Root\" \"Gen.T1.Root\" ((\"Gen.T0.Escape\" \"Gen.T1.Escape\") (\"Gen.T0.ParseLine\" \"Gen.T1.ParseLine\")) ((\"Gen.T0.ParseLine.parseLine₀\" \"Gen.T1.Root.parse\" \"Gen.T1.Root.commutes\")))"
lift₁ = "(lift \"Gen.T1.Root\" \"Gen.T2.Root\" ((\"Gen.T1.Escape\" \"Gen.T2.Escape\") (\"Gen.T1.ParseLine\" \"Gen.T2.ParseLine\")) ((\"Gen.T1.ParseLine.parse\" \"Gen.T2.Root.parse\" \"Gen.T2.Root.commutes\")))"
splitLift = "(lift \"Gen.T0.Root\" \"Gen.T1.Root\" ((\"Gen.T0.Escape\" \"Gen.T1.Escape\") (move (\"Gen.T0.CollectRefs\" \"Gen.T0.Resolve\") (\"Gen.T1.ParseLine\") ())) ((\"Gen.T0.Resolve.resolve\" \"Gen.T1.Root.resolve\" \"Gen.T1.Root.commutes\")))"

refutation : Bool → String → String
refutation top name = showSExpr (list (sym "submission" ∷ list (sym "kind" ∷ [ sym "refute-lift" ])
  ∷ list (sym "why" ∷ [ str reason ]) ∷ list (sym "refute" ∷ [ str proof ]) ∷ []))
  where
    port = if top then "Base.parse" else "Base.parseLine₀"
    proof = header "LostDestination" ++ˢ common ++ˢ useAs (if top then p₁ else p₀) "Base" ++ˢ useAs name "Spec"
      ++ˢ unlines ("open import Data.Empty using (⊥)"
        ∷ ("erased : " ++ˢ port ++ˢ " \"[1]: a\" ≡ " ++ˢ port ++ˢ " \"[1]: b\"")
        ∷ "erased = refl" ∷ "same : Spec.parse \"[1]: a\" ≡ Spec.parse \"[1]: b\""
        ∷ "same = trans (Spec.commutes \"[1]: a\") (trans erased (sym (Spec.commutes \"[1]: b\")))"
        ∷ "distinct : true ≡ false → ⊥" ∷ "distinct ()" ∷ "absurd : ⊥"
        ∷ "absurd = distinct (trans (sym Spec.linkA) (trans (cong (λ x → Spec.pointsToA (Spec.parse \"[go][1]\" ∷ x ∷ [])) same) Spec.linkB))" ∷ [])

data Stage : Set where initial childless upperObstruction middleObstruction splitBase recoverMiddle recoverTop contradictoryEdit breakBase adaptMiddle : Stage

proposal : Stage → String → Maybe String
proposal initial "Gen.T0.Root" = just (submission "single pass" (singleRoot false)
  ((p₀ , singleParser true) ∷ [ e₀ , escape "T0" false true ]) [])
proposal initial "Gen.T0.ParseLine" = just (submission parserNote (singleParser false) [] (newUnits p₀ [ "definition" ]))
proposal initial "Gen.T0.Escape" = just (submission "escape" (escape "T0" false false) [] [])
proposal initial "Gen.T1.Root" = just (submission "coarse projection" (projection t₁ false false false)
  ((p₁ , projection p₁ false false true) ∷ [ e₁ , escape "T1" true true ]) [])
proposal initial "Gen.T1.ParseLine" = just (submission "lift parse" (projection p₁ false false false) [] [])
proposal initial "Gen.T1.Escape" = just (submission "also escape greater-than" (escape "T1" true false) [] [])
proposal childless "Gen.T2.Root" = just (refutation true t₂)
proposal upperObstruction "Gen.T2.Root" = just (submission "full-space forward references" (projection t₂ true true false)
  ((p₂ , projection p₂ true true true) ∷ (e₂ , topEscape true) ∷ [ toc , pureTOC true ]) (newUnits t₂ ("escaped" ∷ [ "paragraph" ])))
proposal upperObstruction "Gen.T2.PureTOC" = just (submission "heading" (pureTOC false) [] [])
proposal upperObstruction "Gen.T2.Escape" = just (submission "lift escaping" (topEscape false) [] [])
proposal upperObstruction "Gen.T2.ParseLine" = just (refutation true p₂)
proposal middleObstruction "Gen.T1.Root" = just (submission "require distinct destinations" (projection t₁ false true false)
  [ p₁ , projection p₁ false true true ] [])
proposal middleObstruction "Gen.T1.ParseLine" = just (refutation false p₁)
proposal splitBase "Gen.T0.Root" = just (submission splitWhy (baseRoot false)
  ((collect , collector true) ∷ [ resolve , resolver false true ])
  (route ∷ newUnits t₀ ("escaped" ∷ [ "paragraph" ])))
proposal splitBase "Gen.T0.CollectRefs" = just (submission "collect definitions" (collector false) [] (newUnits collect [ "definition" ]))
proposal splitBase "Gen.T0.Resolve" = just (submission "resolve references" (resolver false false) []
  (newUnits resolve ("definition" ∷ "link" ∷ "lookupURL" ∷ [ "resolveLine" ])))
proposal recoverMiddle "Gen.T1.Root" = just (submission "lift both passes" (middle t₁ false false) [ p₁ , middle p₁ false true ] [])
proposal recoverMiddle "Gen.T1.ParseLine" = just (submission "distinguish destinations" (middle p₁ false false) [] [])
proposal recoverTop "Gen.T2.Root" = just (submission "recover top" (projection t₂ true true false)
  [ p₂ , projection p₂ true true true ] (newUnits t₂ ("escaped" ∷ [ "paragraph" ])))
proposal recoverTop "Gen.T2.ParseLine" = just (submission "lift both passes" (projection p₂ true true false) [] [])
proposal contradictoryEdit "Gen.T0.Root" = just (showSExpr (list (sym "submission" ∷ list (sym "kind" ∷ [ sym "contradiction" ])
  ∷ list (sym "refute" ∷ [ str (header "ImpossibleEdit" ++ˢ "open import Data.Empty using (⊥)\n" ++ˢ useAs t₀ "Spec"
    ++ˢ "absurd : ⊥\nabsurd = Spec.impossible\n") ]) ∷ [])))
proposal breakBase "Gen.T0.Root" = just (submission "strengthen resolver" (baseRoot false) [ resolve , resolver true true ]
  (keep (ext (member collect "collect")) ∷ [ ext (member collect "collect") ⇝ ext (member resolve "resolve") ]))
proposal breakBase "Gen.T0.Resolve" = just (submission "retire the implementation helper" (resolver true false) []
  [ unit (member resolve "resolveLine") ⇝ ⊥ ])
proposal adaptMiddle "Gen.T1.Root" = just (submission "check the changed base" (middle t₁ true false) [] [])
proposal adaptMiddle "Gen.T1.ParseLine" = just (submission "use public resolve" (middle p₁ true false) [] [])
proposal _ _ = nothing

memoryInPrompt : List String → Maybe Memory
memoryInPrompt ("MEMORY" ∷ text ∷ _) = parseMemory text
memoryInPrompt (_ ∷ rest) = memoryInPrompt rest
memoryInPrompt [] = nothing

service : Stage → Calls → IO (RunningIO AIReq AIReply (⊤ × ⊤))
service stage calls = newIORef "" >>= λ slot → return (record { onCall = request slot ; onStop = return (tt , tt) })
  where
    note : String → String → IO ⊤
    note event name = modifyIORef calls ((event , name) ∷_)

    checkShell : Stage → String → Bool → String → IO ⊤
    checkShell upperObstruction "Gen.T2.Root" false ctx with parseSExpr ctx
    ... | just (list (sym "plan-context" ∷ old ∷ _)) = require "missing previous root" (decodeCode old) >>= λ c →
      assert "childless obstruction lost its empty shell" (nullᵇ (decls c))
    ... | _ = failIO "missing planning context"
    checkShell _ _ _ _ = return tt

    checkPrompt : Stage → String → String → IO ⊤
    checkPrompt splitBase "Gen.T0.Resolve" prompt = require "missing initial MEMORY" (memoryInPrompt (lines prompt)) >>= λ m →
      assert "Resolve's initial MEMORY lacks the routed parser note and the split reason"
        (eqList _==ˢ_ (notesOf m (unit (member resolve "resolve"))) (parserNote ∷ [ splitWhy ]))
    checkPrompt breakBase "Gen.T0.Resolve" prompt = require "missing edited MEMORY" (memoryInPrompt (lines prompt)) >>= λ m →
      assert "existing Resolve lost its birth notes or missed notes from surviving CollectRefs"
        (allᵇ (λ n → elemᵇ _==ˢ_ n (notesOf m (unit (member resolve "resolve"))))
          (parserNote ∷ splitWhy ∷ "collect definitions" ∷ [ "strengthen resolver" ]))
    checkPrompt _ _ _ = return tt

    retry : String → String → IO String
    retry n prompt = if (n ==ˢ t₂) ∧ elemᵇ _==ˢ_ ("CHILD: " ++ˢ p₂) (lines prompt)
      then return (refutation true n)
      else if (n ==ˢ t₁) ∧ elemᵇ _==ˢ_ ("CHILD: " ++ˢ p₁) (lines prompt)
      then return (refutation false n)
      else failIO (n ++ˢ " unexpectedly retried\n" ++ˢ unlines (reverse (take 35 (reverse (lines prompt)))))

    request : IORef String → AIReq → IO AIReply
    request slot (bindNode n _) = note "bind" n >> writeIORef slot n >> return (aiReply "" n)
    request slot (forkNode n) = note "fork" n >> return (aiReply "" n)
    request slot (accept _) = return (aiReply "" "")
    request slot (propose prompt again ctx) = do
      n ← readIORef slot
      note "propose" n
      checkShell stage n again ctx
      checkPrompt stage n prompt
      response ← if again then retry n prompt else require ("unexpected proposal at " ++ˢ n) (proposal stage n)
      return (aiReply response n)

assertObstruction : String → String → List String → ActionResult → IO ⊤
assertObstruction name culprit children result = acceptedText result >>= λ msg → assert msg
  (eqList _==ˢ_ (take 1 (lines msg)) [ "lift-obstruction " ++ˢ name ++ˢ " — " ++ˢ reason ]
  ∧ anyᵇ culpritLine (lines msg) ∧ anyᵇ childrenLine (lines msg))
  where
    culpritLine : String → Bool
    culpritLine line with words line
    ... | "CULPRIT_BASE_UNITS:" ∷ qs = elemᵇ _==ˢ_ culprit qs
    ... | _ = false
    childrenLine : String → Bool
    childrenLine line with words line
    ... | "PRESERVED_CHILDREN:" ∷ "(none)" ∷ [] = nullᵇ children
    ... | "PRESERVED_CHILDREN:" ∷ ns = (length children ≡ᵇ length ns) ∧ allᵇ (λ n → elemᵇ _==ˢ_ n ns) children
    ... | _ = false

run : String → String → IO ⊤
run repo ws = do
  calls ← newIORef []
  let cfg = λ stage → sessionConfig repo ws "Resolve forward Markdown links and escape HTML"
        (refSpec (local "/usr/bin/python3") ("-c" ∷ referenceProgram ∷ []) 30000)
        (ScriptedBackend []) (λ _ → ServiceBackend (service stage calls))
      act = λ stage → executeAction (cfg stage)
      base = λ why spec → drive-tree "T0" why spec [] nothing
      mid = λ why spec lifting → drive-tree "T1" why spec [ "T0" ] (just lifting)
      top = drive-tree "T2" "check forward destinations" (projection t₂ true true true) [ "T1" ] (just lift₁)
      store = ws ++ˢ "/store"
      ref = λ name → CAS.readRef store name >>= require ("missing ref " ++ˢ name)
      commit = λ key → CAS.getCommit store key >>= require "missing commit"
      rootNode = λ key → commit key >>= λ c → CAS.getHomeNode store (CAS.rootHome c) >>= require "missing root"
      hashOf = λ key n → rootNode key >>= kid n
      same = λ key n hash → hashOf key n >>= λ actual → assert ("changed HomeNode " ++ˢ n) (actual ==ˢ hash)
      parents = λ key ps → commit key >>= λ c → assert "incorrect parent tips" (eqList _==ˢ_ (CAS.parents c) ps)
      turns = λ event n count → callCount calls event n >>= λ total → assert (event ++ˢ " count at " ++ˢ n) (total ≡ᵇ count)
      once = λ n → turns "propose" n 1 >> turns "bind" n 1 >> turns "fork" n 1
      verdict = λ name want → readFile (ws ++ˢ "/trees/" ++ˢ name ++ˢ "/verdict") >>= λ v → assert v (v ==ˢ want)
      absent = λ path → fileExists path >>= λ present → assert ("stale file " ++ˢ path) (not present)
      source = λ path expected → readFile (ws ++ˢ "/generated/" ++ˢ path) >>= λ bytes → assert ("authored source " ++ˢ path) (bytes ==ˢ expected)

  act initial (base "single pass" (singleRoot true)) >>= expectedOK "ok T0"
  act initial (mid "lift coarse parser" (projection t₁ false false true) lift₀) >>= expectedOK "ok T1"
  b ← ref (treeRef "T0")
  m ← ref (treeRef "T1")
  parents m [ b ]
  h₀ ← hashOf b e₀
  h₁ ← hashOf m e₁
  putStrLn "PASS initial parser, escaping and coarse lift"

  act childless (drive-tree "T2" "direct witness" (projection t₂ true true true ++ˢ "postulate extra : Bool\n")
    [ "T1" ] (just lift₁)) >>= assertObstruction "T2" (p₁ ++ˢ ".parse") []
  absent (store ++ˢ "/refs/" ++ˢ partialTreeRef "T2")
  act upperObstruction top >>= assertObstruction "T2" (p₁ ++ˢ ".parse") (toc ∷ [ e₂ ])
  verdict "T2" "lift-obstruction"
  uPartial ← ref (partialTreeRef "T2")
  parents uPartial [ m ]
  h₂ ← hashOf uPartial e₂
  hToc ← hashOf uPartial toc
  once e₂ >> once toc
  putStrLn "PASS upper obstruction saved Escape and the upper-only PureTOC"

  act middleObstruction (mid "strengthen projection" (projection t₁ false true true) lift₀)
    >>= assertObstruction "T1" (p₀ ++ˢ ".parseLine₀") [ e₁ ]
  verdict "T1" "lift-obstruction"
  mPartial ← ref (partialTreeRef "T1")
  parents mPartial [ b ]
  same mPartial e₁ h₁ >> once e₁
  putStrLn "PASS middle obstruction convicted T0 and kept Escape asleep"

  act splitBase (base splitWhy (baseRoot true)) >>= expectedOK "ok T0"
  b′ ← ref (treeRef "T0")
  parents b′ [ b ]
  same b′ e₀ h₀ >> once e₀
  root ← rootNode b′
  assert "ParseLine still owned" (not (elemᵇ _==ˢ_ p₀ (map proj₁ (CAS.kids root))))
  parentMemory ← CAS.getObject store CAS.memK (CAS.memHash root) >>= require "missing parent memory"
  -- The parser had two local units with the same planning reason. Only
  -- its private definition helper belongs in the graveyard.
  assert "mapped parser note was buried or private note was lost" (eqList _==ˢ_ (notesOf parentMemory ⊥) [ parserNote ])
  absent (ws ++ˢ "/generated/T0/Gen/T0/ParseLine.agda")
  once resolve
  putStrLn "PASS split removed ParseLine and delivered its memory to Resolve"

  act recoverMiddle (mid "recover against two passes" (middle t₁ false true) splitLift) >>= expectedOK "ok T1"
  m′ ← ref (treeRef "T1")
  parents m′ (b′ ∷ [ m ])
  same m′ e₁ h₁ >> once e₁
  absent (store ++ˢ "/refs/" ++ˢ partialTreeRef "T1")
  act recoverTop top >>= expectedOK "ok T2"
  u ← ref (treeRef "T2")
  parents u [ m′ ]
  absent (store ++ˢ "/refs/" ++ˢ partialTreeRef "T2")
  same u e₂ h₂ >> once e₂ >> same u toc hToc >> once toc
  source "T0/Gen/T0/Escape.agda" (escape "T0" false false)
  source "T1/Gen/T1/Escape.agda" (escape "T1" true false)
  source "T2/Gen/T2/Escape.agda" (topEscape false)
  source "T2/Gen/T2/PureTOC.agda" (pureTOC false)
  verifyCommitDAG store u >>= assert "invalid recovered tower"
  putStrLn "PASS in-place recovery retained all innocent HomeNodes and authored bytes"

  -- T1 still pins the preceding T0 tip. A direct + transitive base list
  -- must select the new T0 once, and a real compiler must reject the stale
  -- use of Resolve.resolveLine, even though T1's child interface is equal.
  act contradictoryEdit (base "inconsistent edit" (header t₀ ++ˢ "open import Data.Empty using (⊥)\npostulate impossible : ⊥\n"))
    >>= expectedOK "contradiction T0"
  verdict "T0" "contradiction"
  act breakBase (base "drop resolver helper" (baseRoot true)) >>= expectedOK "ok T0"
  b″ ← ref (treeRef "T0")
  parents b″ [ b′ ]
  source "T0/Gen/T0/Escape.agda" (escape "T0" false false)
  same b″ e₀ h₀
  live ← loadClosure ws ("T0" ∷ [ "T1" ]) >>= require "live ancestor diamond conflicted"
  assert "old Resolve leaked into the closure" (not (anyᵇ (λ c → elemᵇ _==ᴺ_ (member resolve "resolveLine") (map uname (units c))) (baseCodes live)))
  auditTrees (cfg adaptMiddle) ("T0" ∷ [ "T1" ]) >>= require "audit accepted broken T1" >>= λ msg →
    assert msg (eqList _==ˢ_ (take 1 (lines msg)) [ "finish: exported module no longer typechecks" ])
  act adaptMiddle top >>= λ where
    (rejected msg) → assert msg (elemᵇ _==ˢ_ ("drive-tree: ancestor " ++ˢ p₁ ++ˢ " no longer typechecks") (lines msg)
                               ∨ elemᵇ _==ˢ_ ("drive-tree: ancestor " ++ˢ t₁ ++ˢ " no longer typechecks") (lines msg))
    _ → failIO "T2 accepted an invalid live ancestor"
  turns "propose" p₁ 3
  act adaptMiddle (mid "recheck imports" (middle t₁ true true) splitLift) >>= expectedOK "ok T1"
  turns "propose" p₁ 4
  m″ ← ref (treeRef "T1")
  parents m″ (b″ ∷ [ m′ ])
  same m″ e₁ h₁ >> once e₁ >> once e₀ >> once e₂ >> once toc
  putStrLn "PASS changed ancestor woke the dependent parser"

  names ← listDirectory (ws ++ˢ "/trees")
  assert "unexpected tower names" ((length names ≡ᵇ 3) ∧ allᵇ (λ n → elemᵇ _==ˢ_ n names) ("T0" ∷ "T1" ∷ [ "T2" ]))
  act recoverTop (build-exe "compile the recovered tower" "Gen.T2.Root.app") >>= acceptedText
  act recoverTop (run-script "compare Markdown with the reference" replay) >>= expectedOK "Markdown replay passed"
  act recoverTop (finish "Recovered in place") >>= λ where
    (finished _) → putStrLn "PASS executable, reference replay and full live tower audit"
    (rejected err) → failIO err
    _ → failIO "expected finish"

main : IO ⊤
main = enableLineBuffering >> currentDirectory >>= λ repo → withPrivateTemp (repo ++ˢ "/tmp/v8-tower") (run repo)
