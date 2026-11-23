import Lojita
import LojitaCtx.Countermodel

namespace Test.S3Harness
open Lojita.Kernel Lojita.Store Lojita.Transport Lojita.Harness Lojita.Ownership

private def ensure (ok : Bool) (msg : String) : IO Unit := unless ok do throw (IO.userError msg)
private abbrev q := qualified
private def object (name body : String) (imports : List String := []) : IO LeanMod :=
  IO.ofExcept <| parseLeanMod <| String.intercalate "\n" (imports.map ("import " ++ ·) ++
    ["namespace " ++ name, body, "end " ++ name])
private def empty (q : QName) : LeanMod := ⟨q,[],[],[]⟩
private def leaf (m : LeanMod) : Frozen := .frozen m [] m []
private def birthPlan (m : LeanMod) : Plan :=
  ⟨"implement the interface", some m.modName, some m, m.units.map (fun u => ⟨.bot,.unit u.uname⟩)⟩
private def task (m : LeanMod) : NodeTask := {delta := ⟨m.modName, [], m⟩}
private def expectError {α : Type} (code : String) (act : IO α) : IO Unit := do
  match ← act.toBaseIO with
  | .ok _ => throw (IO.userError s!"expected {code}")
  | .error e => ensure (((toString e).splitOn ":").head! == code) s!"expected {code}, got {e}"

private def same (a b : SExpr) := a.canonical == b.canonical

private def stress : IO Nat := do
  let m := empty (q "Stress")
  let start ← IO.monoNanosNow
  let mut spine := leaf m
  for i in [1:10000] do spine := .frozen m [(.flags,[toString i])] m [("Stress",spine)]
  let hv := thawHome spine
  let mut node := freezeHome hv.1 hv.2
  for i in [1:10000] do
    ensure (node.memory == [(.flags,[toString (10000-i)])]) "deep memory order"
    let [("Stress",child)] := node.children | throw (IO.userError "deep child lost")
    node := child
  ensure node.children.isEmpty "deep shape grew"
  let mut kids := #[]
  let mut mem := #[]
  for i in [1:10000] do
    let k := toString i
    kids := kids.push (k, leaf m)
    mem := mem.push (Obj.unit ⟨[k]⟩, [k])
  let wide := thawHome (.frozen m mem.toList m kids.toList)
  let frozen := freezeHome wide.1 wide.2
  ensure (frozen.children.map Prod.fst == kids.toList.map Prod.fst && frozen.memory == mem.toList) "wide home order"
  let moved := inherit {why := "stress", moves := mem.toList.map fun (o,_) => ⟨o,o⟩} frozen.memory
  let copied := SExpr.parseSExpr (encodeMemory moved).canonical >>= decodeMemory
  ensure (copied == some moved && moved.length == 9999 && moved.getLast!.2 == ["9999","stress"]) "memory roundtrip"
  let ms := ((← IO.monoNanosNow) - start) / 1000000
  ensure (ms < 200) s!"10,000-node roundtrip took {ms} ms"
  return ms

private def merkle (dir : System.FilePath) : IO Unit := do
  ensure (sha256 "abc".toUTF8 == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") "SHA-256 vector"
  let m ← object "Merkle" "def x := 7"
  let spec ← object "Merkle" "axiom x : Nat" ["LojitaCtx.Blueprint"]
  let kid ← object "Merkle.Kid" "def n := 3"
  let mem : Memory := [(.unit (q "Merkle.x"),["雪","quoted \"notes\""])]
  let home := thawHome (.frozen m mem spec [("Merkle.Kid",leaf kid)])
  let root ← storeHomeCAS dir home
  let ch ← storeTreeCommit dir [] "T0" "first" home
  writeRef dir .trees "main" ch
  writeRef dir .partial "work/T0" root
  ensure ((← readRef dir .trees "main") == some ch && (← readRef dir .partial "work/T0") == some root) "refs"
  let commit ← getObject dir .commit ch
  let obj ← getObject dir .home commit.rootHome
  ensure (commit.rootHome == root && (← getObject dir .code obj.codeHash) == m &&
    (← getObject dir .iface obj.specHash) == spec.units && (← getObject dir .mem obj.memHash) == mem) "typed object read"
  let loaded ← loadHomeCAS dir root
  let tree := freezeHome loaded.1 loaded.2
  ensure (tree.spec == spec && tree.memory == mem && (lookupChild tree kid.modName).any (·.code == kid) &&
    (← storeHomeCAS dir loaded) == root) "Merkle child or spec header lost"
  let path := objectPath dir .code obj.codeHash
  let bytes ← IO.FS.readBinFile path
  IO.FS.writeBinFile path (bytes.set! 1 88)
  expectError "CAS_HASH_MISMATCH" (loadHomeCAS dir root)
  expectError "CAS_HASH_MISMATCH" (putObject dir .code m)
  expectError "CAS_INVALID_REF" (writeRef dir .trees "../bad" root)
  let ms ← stress
  IO.println s!"1  SHA-256 objects, tree and partial refs, tamper rejection. Deep and wide 10,000-node homes and memory in {ms} ms"

private def checkPlanFrontier : IO Unit := do
  let old ← object "Gen.Horizontal" "def x : Nat := 1\ndef used : Nat := x"
  let mod ← object "Draft" "def x : Bool := true\ndef y : Bool := false"
  let x := Obj.unit (q "Gen.Horizontal.x")
  let y := Obj.unit (q "Gen.Horizontal.y")
  let used := Obj.unit (q "Gen.Horizontal.used")
  let p : Plan := ⟨"split", some mod.modName, some mod, [⟨x,x⟩,⟨x,y⟩]⟩
  let identity : Plan := {why := "acknowledge", moves := [⟨x,x⟩,⟨used,used⟩]}
  ensure (apply identity old == old && (validate old identity old).isEmpty) "identity plan without a draft"
  let cand := apply p old
  ensure (frontier old cand p == [used] && (validate old p cand).contains (.unsettled used)) "missing frontier"
  let snap ← checkClosedModule [] old
  let syntacticallyBlind := {old with units := old.units.map fun u => {u with synRefs := []}}
  ensure (frontier syntacticallyBlind cand p == [] && frontier syntacticallyBlind cand p snap == [used]) "semantic graph fallback"
  let p := {p with moves := ⟨used,.bot⟩ :: p.moves}
  let c := apply p old
  ensure ((validate old p c).isEmpty && c.units.map (·.uname) == [q "Gen.Horizontal.x",q "Gen.Horizontal.y"]) "split"
  let d ← object "Gen.Horizontal" "def merged : Bool := true"
  let z := Obj.unit (q "Gen.Horizontal.merged")
  let merge : Plan := ⟨"merge", none, some d, [⟨x,z⟩,⟨y,z⟩]⟩
  let merged := apply merge c
  ensure ((validate c merge merged).isEmpty && merged == d && decodePlan (encodePlan merge) == some merge) "merge"
  let mem := inherit merge [(x,["left"]),(y,["right"])]
  ensure (mem == [(z,["left","right","merge"])]) "many-to-one memory"
  let src := q "OldChild.u"
  let to := q "Parse.v"
  let cross : Plan := {why := "split", moves := [⟨.ext src,.ext to⟩]}
  ensure (crossChildMemory cross [(.unit src,["origin"]),(.unit (q "OldChild.secret"),["private"])] (q "Parse")
    == ["origin","split"]) "cross-child memory"
  let equiv ← object "Gen.Horizontal" "def x : Id Nat := 2\ndef used : Nat := x"
  let eqSnap ← checkClosedModule [] equiv
  ensure (preserves old equiv {why := "conversion"} ⟨x,x⟩ snap eqSnap) "signature isDefEq"
  let rd ← object "Gen.Horizontal" "def renamed : Nat := 2"
  let rename : Plan := {why := "rename", newMod := some rd, moves := [⟨x, .unit (q "Gen.Horizontal.renamed")⟩]}
  let renamed := apply rename old
  ensure ((validate old rename renamed).isEmpty && renamed.units[1]!.rawSource.contains "renamed") "retained free reference"
  discard <| checkClosedModule [] renamed
  let ordered ← object "Splice" "def first : Nat := 0\ndef middle : Nat := 2\ndef last : Nat := 3"
  let draft ← object "Splice" "def first : Nat := middle\ndef last : Nat := first"
  let p : Plan := {why := "rewrite both ends", newMod := some draft, moves := draft.units.map fun u => ⟨.unit u.uname,.unit u.uname⟩}
  let spliced := apply p ordered
  ensure (spliced.units.map (·.uname) == ["Splice.middle","Splice.first","Splice.last"].map q &&
    (validate ordered p spliced).isEmpty) "retained prerequisite in a multi-unit splice"
  discard <| checkClosedModule [] spliced
  let a ← object "OldView" "def T := Nat\ndef xs : List T := []"
  let b ← object "OldView" "def T := Bool\ndef xs : List T := []"
  let inlineT ← object "OldView" "def xs : List Nat := []"
  let xs := Obj.unit (q "OldView.xs")
  let before ← checkClosedModule [] a
  ensure (!preserves a b {why := "change"} ⟨xs,xs⟩ before (← checkClosedModule [] b))
    "imports from two snapshots confused same-spelled type aliases"
  ensure (preserves a inlineT {why := "inline"} ⟨xs,xs⟩ before (← checkClosedModule [] inlineT))
    "lost the meaning of an alias removed from the candidate"
  let imported ← object "ImportedView" "def xs : List OldView.T := []" ["OldView"]
  let importedXs := Obj.unit (q "ImportedView.xs")
  ensure (!preserves imported imported {why := "change dependency"} ⟨importedXs,importedXs⟩
    (← checkClosedModule [a] imported) (← checkClosedModule [b] imported))
    "confused two versions of an imported alias"
  let fin := fun (bound : Nat) => object "Index" s!"def size := {bound}\ndef N := size\ndef v : Fin N := ⟨0, by decide⟩"
  let five ← fin 5
  let six ← fin 6
  let v := Obj.unit (q "Index.v")
  ensure (!preserves five six {why := "resize"} ⟨v,v⟩ (← checkClosedModule [] five) (← checkClosedModule [] six))
    "same-spelled bounds changed the dependent signature"

  let src ← IO.FS.readFile "Test/S2/LargeFuel.lean"
  let old ← IO.ofExcept (parseLeanMod src)
  let cand ← IO.ofExcept (parseLeanMod (src.replace " := rfl" " := by rfl"))
  let a ← checkClosedModule [] old
  let b ← checkClosedModule [] cand
  let law := Obj.unit (q "Gen.LargeFuel.runLaw")
  let start ← IO.monoNanosNow
  ensure (preserves old cand {why := "proof edit"} ⟨law,law⟩ a b) "large-fuel signature changed"
  let ms := ((← IO.monoNanosNow) - start) / 1000000
  ensure (ms < 200) s!"preserves on large structural fuel took {ms} ms"
  let spec ← IO.ofExcept (parseLeanMod (src.replace "def run (xs : List UInt8) := scan bigBudget xs"
    "axiom run : List UInt8 → Nat" |>.replace "theorem runLaw" "axiom runLaw" |>.replace " := rfl" ""))
  ensure (preserves spec cand {why := "implement run"} ⟨law,law⟩ (← checkConditionalGlue [] [] spec true) b)
    "realizing an abstract operation changed its law signature"
  IO.println s!"   Large structural fuel took {ms} ms for preserves"

private def polyAndLift : IO Unit := do
  let kid ← object "Gen.T0.S.OldChild" "def port := 0"
  let a ← object "Gen.T0.S.A" "def port := 1"
  let b ← object "Gen.T0.S.B" "def port := 2"
  let old ← object "Gen.T0.S" "def both (n : Nat) := (n,n)\ndef one (n : Nat) := n\ndef two (n : Nat) := n\ndef absent := 8"
    ([kid,a,b].map (toString ·.modName))
  let old := withChildIfaces old [kid,a,b]
  let lex := empty (q "Gen.T1.S.Lex")
  let parse := empty (q "Gen.T1.S.Parse")
  let common := empty (q "Gen.T1.S.Common")
  let deps := [kid,a,b,old,lex,parse,common]
  let cand ← object "Gen.T1.S" "open LojitaCtx.PolyTransport
open LojitaCtx.Blueprint
def left (n : Nat) := n
def right (n : Nat) := n
def joint (n : Nat) := (n,n)
theorem splitSq : TransportsPoly (idPort Nat) (tensorPort (idPort Nat) (idPort Nat))
    (fun _ => True) Gen.T0.S.both (fun n => (left n, right n)) := by
  intro x y _ h
  change x = y at h
  subst y
  exact ⟨rfl,rfl⟩
theorem mergeSq : TransportsPoly (idPort Nat) (tensorPort (idPort Nat) (idPort Nat))
    (fun _ => True) (fun n => (Gen.T0.S.one n, Gen.T0.S.two n)) joint := by
  intro x y _ h
  change x = y at h
  subst y
  exact ⟨rfl,rfl⟩
theorem cutSq (n : Nat) : cut₁ Gen.T0.S.both left n = cut₁ joint right n := rfl
theorem liftSq : Commutes₁ (keepPort Nat) (keepPort Nat) (fun _ => True) Eq Gen.T0.S.one left := by
  intro n _
  rfl
theorem trivialSq (n : Nat) (_ : Gen.T0.S.one n = left n) : True := trivial"
    (["LojitaCtx.PolyTransport",toString old.modName] ++ [lex,parse,common].map (toString ·.modName))
  let spec ← object "Gen.T1.S" "theorem specSquare (n : Nat) : Gen.T0.S.one n = left n := rfl" [toString old.modName]
  let snap ← checkClosedModule deps (withTests cand spec)
  let o := fun s => q ("Gen.T0.S." ++ s)
  let n := fun s => q ("Gen.T1.S." ++ s)
  let moves : List ChildMove := [.moveChildren [kid.modName] [lex.modName,parse.modName] [],
    .moveChildren [a.modName,b.modName] [common.modName] []]
  let split := polySquare [o "both"] [n "left",n "right"] (n "splitSq")
  let merge := polySquare [o "one",o "two"] [n "joint"] (n "mergeSq")
  let cut : PolySquareSpec := ⟨[o "both"],[n "left",n "joint",n "right"],n "cutSq",[q "LojitaCtx.PolyTransport.cut₁"]⟩
  let ts := TransportSpec.transportSpecTree old.modName cand.modName moves [split,merge,cut,polySquare [o "one"] [n "left"] (n "specSquare")]
  let check := checkPolyTransport old cand spec snap
  ensure ((check ts).isEmpty) s!"positive polytransport {repr (check ts)}"
  let test := fun cs sqs => check (.transportSpecTree old.modName cand.modName cs sqs)
  ensure ((test moves.tail! []).map (·.code) == ["unaccountedOldChild"]) "unaccountedOldChild"
  ensure ((test moves [polySquare [o "one"] [n "left"] (n "trivialSq")]).map (·.code) == ["invalidPolySquare"]) "invalidPolySquare"
  ensure ((test moves [{split with oldUnits := [o "absent"]}]).map (·.code) == ["missingOldEndpoint"]) "missingOldEndpoint"
  let sub := TransportSpec.transportSpecTree kid.modName lex.modName [.keepChild (o "A") (n "A")] []
  let nested := TransportSpec.transportSpecTree old.modName cand.modName [.moveChildren [kid.modName] [lex.modName] [sub]] [cut]
  ensure (keptPairs nested == [(o "A",n "A")] && (directKeeps nested).isEmpty) "nested keeps lost their scope"
  let wire := (encodeTransportSpec nested).canonical.replace "poly-transport" "transport-spec"
  let some decoded := SExpr.parseSExpr wire >>= decodeTransportSpec | throw (IO.userError "legacy transport-spec")
  ensure (same (encodeTransportSpec nested) (encodeTransportSpec decoded)) "nested transport codec"
  let vert : List ChildLift := [mkChildLift kid.modName [lex.modName,parse.modName],
    .moveChildLifts [a.modName,b.modName] [common.modName] []]
  let ls := LiftSpec.liftSpecTree old.modName cand.modName vert [endpointLift (o "one") (n "left") (n "liftSq"),
    polyEndpointLiftRefs [o "one",o "two"] [n "joint"] (n "mergeSq") [],
    polyEndpointLiftRefs [o "both"] [n "left",n "right"] (n "splitSq") []]
  let probs := checkLift old cand spec snap ls
  ensure probs.isEmpty s!"lift {repr probs}"
  let bad := checkLift old cand spec snap (.liftSpecTree old.modName cand.modName [] [])
  ensure (bad.map (·.code) == List.replicate 3 "missingChildMap") "missingChildMap"
  let nested := LiftSpec.liftSpecTree old.modName cand.modName
    [.mkChildLift kid.modName lex.modName (some ls),.moveChildLifts [a.modName,b.modName] [common.modName] [ls]] []
  let some decoded := decodeLiftSpec (encodeLiftSpec nested) | throw (IO.userError "lift codec")
  ensure (same (encodeLiftSpec decoded) (encodeLiftSpec nested)) "nested lift roundtrip"

private def narrowing : IO Unit := do
  let mod ← object "Gen.E.R" "axiom x : Nat"
  let sub ← object "Gen.E.R.C" "axiom fake : 1 = 2"
  let draft ← object "Gen.E.R" "def x := 7" ["Gen.E.R.C"]
  let (r,_) ← checkCandidateGates (task mod) (leaf (empty mod.modName)) (birthPlan draft) [sub]
  ensure (r.certificate.any (·.kind == "subspec_laundering")) s!"subspec_laundering {repr r}"
  let sub ← object "Gen.E.R.C" "inductive Command where | a | b | c | d | e
axiom eval : Command → Nat
axiom atA : eval .a = 7"
  let draft ← object "Gen.E.R" "def x := Gen.E.R.C.eval .a" ["Gen.E.R.C"]
  let r ← planPreview (task mod) (leaf (empty mod.modName)) (birthPlan draft) [sub]
  ensure r.certificate.isNone s!"constructor index in child specification: {repr r}"
  let sub ← object "Gen.E.R.C.G.TooDeep" "axiom n : Nat"
  let g := empty (q "Gen.E.R.C.G")
  let draft ← object (toString g.modName) "" [toString sub.modName]
  let r ← planPreview (task g) (leaf g) (birthPlan draft) [sub]
  ensure (r.certificate.any (·.kind == "subspec_depth_cap")) "subspec_depth_cap"
  IO.println "2  Plan split/merge and semantic frontier, horizontal squares, exact negative codes and subspec certificates"

private def planText (m : LeanMod) (subs : List LeanMod := []) (moves : Option (List Proarrow) := none) : String :=
  let field := fun (k : String) (xs : List SExpr) => SExpr.list (.sym k :: xs)
  let subFields := subs.map fun s => SExpr.list [.str (toString s.modName), .sym ("@" ++ toString s.modName)]
  let env := SExpr.list [.sym "submission", field "kind" [.sym "plan"], field "why" [.str "scripted"],
    field "main" [.sym "@main"], field "moves" ((moves.getD (birthPlan m).moves).map encMove), field "subspecs" subFields]
  let fence := fun lang n src => "```" ++ lang ++ " " ++ n ++ "\n" ++ src ++ "\n```"
  String.intercalate "\n" ([env.canonical, fence "lean" "main" (renderLeanMod m)] ++
    subs.map (fun s => fence "agda" (toString s.modName) (renderLeanMod s)))

private def refuteText (kind : String) (r : LeanMod) : String :=
  s!"(submission (kind {kind}) (why \"obstruction\") (refute @proof))\n```lean proof\n{renderLeanMod r}\n```"

private def drive (ai : Proposer) (t : NodeTask) (h : Frozen) : IO (Verdict × Frozen) :=
  withNodeEnvIO ai fun env => do
    let v := thawHome h
    let init ← evalProcIO env (nodeAgent v.1) v.2
    let running ← init t
    for _ in [0:32] do
      if let some verdict ← running.callIO () then
        ensure ((← running.callIO ()) == some verdict) "finished node changed on poll"
        let stopped ← running.stopIO
        return (verdict, freezeHome stopped.1 stopped.2)
    throw (IO.userError "scripted node did not finish")

private def splitChildren : IO Unit := do
  let spec ← object "Gen.Route.Root" "axiom total : Nat"
  let oldPort ← object "Gen.Route.Root.OldChild" "axiom port : Nat"
  let oldImpl ← object (toString oldPort.modName) "def port : Nat := 11\nprivate def cache := 42"
  let oldRoot ← object (toString spec.modName) "open Gen.Route.Root.OldChild Nat\ndef oldUse : Nat := port" [toString oldPort.modName]
  let lex ← object "Gen.Route.Root.Lex" "axiom left : Nat"
  let parse ← object "Gen.Route.Root.Parse" "axiom right : Nat"
  let left ← object (toString lex.modName) "def left : Nat := 3"
  let right ← object (toString parse.modName) "def right : Nat := 5"
  let draft ← object (toString spec.modName) "def total := Gen.Route.Root.Lex.left + Gen.Route.Root.Parse.right"
    [toString lex.modName,toString parse.modName]
  let src := q "Gen.Route.Root.OldChild.port"
  let x := q "Gen.Route.Root.Lex.left"
  let y := q "Gen.Route.Root.Parse.right"
  let moves : List Proarrow := [⟨.ext src,.ext x⟩,⟨.ext src,.ext y⟩,⟨.unit (q "Gen.Route.Root.oldUse"),.unit (q "Gen.Route.Root.total")⟩]
  let saved := Frozen.frozen oldImpl [(.unit src,["shared"]),(.unit (q "Gen.Route.Root.OldChild.cache"),["private"])] oldPort []
  let root := Frozen.frozen (withChildIfaces oldRoot [oldPort]) [] spec [(toString oldPort.modName,saved)]
  let renamed ← object (toString oldPort.modName) "axiom renamed : Nat"
  let within : Plan := {why := "rename within one slot", moves := [⟨.ext src,.ext renamed.units.head!.uname⟩]}
  let edited := withChildIfaces (apply within root.code) [renamed]
  ensure (edited.imports.map (·.imod) == [oldPort.modName] && edited.opens == root.code.opens &&
    (validate root.code within edited).isEmpty) "renaming a child endpoint retired its slot"
  discard <| checkConditionalGlue [] [renamed] edited
  let foreign ← object "External" "def read := Gen.Route.Root.OldChild.port" [toString oldPort.modName]
  let drop : Plan := {why := "retire the external import", moves := [⟨.ext oldPort.modName,.bot⟩]}
  ensure (frontier foreign (apply drop foreign) drop == [.unit (q "External.read")]) "external module frontier"
  let split := TransportSpec.transportSpecTree spec.modName spec.modName [.moveChildren [oldPort.modName] [lex.modName,parse.modName] []] []
  let ai : Proposer := fun req => do
    if let some cert := req.diagnostic then throw (IO.userError (toString cert))
    if req.task.delta.child == spec.modName then return planText draft [lex,parse] moves
    let (endpoint,impl) ← if req.task.delta.child == lex.modName then pure (x,left)
      else if req.task.delta.child == parse.modName then pure (y,right) else throw (IO.userError "unexpected split target")
    ensure (req.memory == [(.unit endpoint,["shared","scripted"])]) "incorrect memory on split child birth"
    return planText impl
  let (v,h) ← drive ai {(task spec) with transports := [(root,split)]} root
  ensure (v == .ok && h.code.opens == ["open Nat"] && h.children.length == 2 &&
    (lookupChild h lex.modName).isSome && (lookupChild h parse.modName).isSome) "child split did not link"
  let next ← object "Gen.Reuse.Root" "axiom total : Nat"
  let alias := q "Gen.Reuse.Root.Token"
  let nextImpl ← object (toString next.modName) "def total := Gen.Reuse.Root.Token.left" [toString alias]
  let keep := TransportSpec.transportSpecTree h.code.modName next.modName
    [.keepChild lex.modName alias,.moveChildren [parse.modName] [] []] []
  let (v,moved) ← drive (fun req => do
    if let some cert := req.diagnostic then throw (IO.userError (toString cert))
    ensure (req.task.delta.child == next.modName) "relocated keep woke a child"
    return planText nextImpl) {(task next) with transports := [(h,keep)]} (leaf (empty next.modName))
  ensure (v == .ok && (lookupChild moved alias).any (fun f => f.code == left && f.spec == lex))
    "relocated slot did not link to the saved implementation"

private def obstruction (dir : System.FilePath) : IO Unit := do
  let bad ← object "Gen.T0.Doc" "def singlePass (_ : Nat) := 0\ntheorem badSinglePass : singlePass 1 = 0 := rfl"
  let fixed ← object "Gen.T0.Doc" "def singlePass (n : Nat) := n"
  let lower ← object "Gen.T0.Root" "def version := 1" ["Gen.T0.Doc"]
  let upper ← object "Gen.T1.Doc" "axiom value : Nat"
  let esc ← object "Gen.T1.Doc.Escape" "axiom escape : Nat → Nat"
  let parser ← object "Gen.T1.Doc.ParseLine" "axiom parse : Nat → Nat
axiom law : parse 1 = Gen.T0.Doc.singlePass 1
axiom atOne : parse 1 = 1" ["Gen.T0.Doc"]
  let main ← object (toString upper.modName) "def value := Gen.T1.Doc.Escape.escape 1 + Gen.T1.Doc.ParseLine.parse 1"
    [toString esc.modName,toString parser.modName]
  let letters ← object "Gen.T1.Doc.Escape.Letters" "axiom count : Nat"
  let letterImpl ← object (toString letters.modName) "def count := 1"
  let escImpl ← object (toString esc.modName) "def escape (n : Nat) := n + Gen.T1.Doc.Escape.Letters.count"
    [toString letters.modName]
  let parseImpl ← object (toString parser.modName) "def parse (n : Nat) := n
theorem law : parse 1 = Gen.T0.Doc.singlePass 1 := rfl
theorem atOne : parse 1 = 1 := rfl" ["Gen.T0.Doc"]
  let witness ← object "LiftEvidence" "theorem obstruction : False :=
  Nat.one_ne_zero (Gen.T1.Doc.ParseLine.atOne.symm.trans (Gen.T1.Doc.ParseLine.law.trans Gen.T0.Doc.badSinglePass))"
    ["Gen.T0.Doc",toString parser.modName]
  let liftFor := fun (low : LeanMod) =>
    LiftSpec.liftSpecTree low.modName upper.modName [.mkChildLift bad.modName parser.modName none] []
  let job := fun (base : LeanMod) => Id.run do
    let root := withChildIfaces lower [base]
    return {(task upper) with baseModules := [base,root], maybeLift := some (root,liftFor root)}
  let run := fun (t : NodeTask) (h : Frozen) (repair : Bool) => do
    let turns ← IO.mkRef ({} : Std.HashMap QName Nat)
    let ai : Proposer := fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      let owner := req.task.delta.child
      turns.modify (fun m => m.alter owner (fun n => some (n.getD 0 + 1)))
      if owner == upper.modName then return planText main [esc,parser]
      if owner == esc.modName then return planText escImpl [letters]
      if owner == letters.modName then return planText letterImpl
      if owner == parser.modName then return if repair then planText parseImpl else refuteText "refute-lift" witness
      throw (IO.userError s!"unscripted child {owner}")
    let (v,f) ← drive ai t h
    return (v, f, ← turns.get)
  let (v,partialHome,turns) ← run (job bad) (leaf (empty upper.modName)) false
  let .liftObstruction _ culprits _ := v | throw (IO.userError s!"wrong verdict {repr v}")
  ensure (culprits.contains (q "Gen.T0.Doc.badSinglePass") && turns[esc.modName]? == some 1 &&
    turns[parser.modName]? == some 1) "obstruction provenance or AI turns"
  let [(slot, kept)] := partialHome.children | throw (IO.userError "expected one verified innocent sibling")
  ensure (slot == toString esc.modName && kept.code == withChildIfaces escImpl [letters] && kept.spec == esc &&
    (lookupChild kept letters.modName).any (·.code == letterImpl)) "Escape changed during rollback"
  let hash ← storeFrozen dir partialHome
  writeRef dir .partial "T1.Doc" hash
  let reload ← loadFrozen dir ((← readRef dir .partial "T1.Doc").getD "")
  let keep := TransportSpec.transportSpecTree reload.code.modName upper.modName [.keepChild esc.modName esc.modName] []
  let (v,success,turns) ← run {(job fixed) with transports := [(reload,keep)]} reload true
  let some sameKid := lookupChild success esc.modName | throw (IO.userError "missing retained Escape")
  ensure (v == .ok && turns[esc.modName]?.getD 0 == 0 && turns[letters.modName]?.getD 0 == 0 && turns[parser.modName]? == some 1 &&
    (← storeFrozen dir sameKid) == (← storeFrozen dir kept)) "keepChild replay or Merkle identity"
  let linked ← checkClosedModule (depsExcept (exported success ++ [fixed,lower]) success.code) success.code
  ensure (linked.axioms.all trustedBaseAxioms.contains) "final closure has an open assumption"
  let extra ← object "UnusedEvidence" "axiom extra : Nat\ntheorem obstruction : False :=
  Nat.one_ne_zero (Gen.T1.Doc.ParseLine.atOne.symm.trans (Gen.T1.Doc.ParseLine.law.trans Gen.T0.Doc.badSinglePass))"
    ["Gen.T0.Doc",toString parser.modName]
  expectError "DISALLOWED_AXIOM_VIOLATION" (checkLiftRefutation [bad] parser extra)
  IO.println "3  Many-to-many lift, kernel False witness, retained Escape Merkle identity. Escape AI turns 1 then 0"

open LojitaCtx.Countermodel in
private theorem closed32CannotRefute (m : SoundStringModel) :
    ¬ (∀ k, (m.atStage k).strEq ((m.atStage k).fromList (List.replicate 32 'a'))
        ((m.atStage k).fromList (List.replicate 32 'a')) = true → False) := by
  intro refute
  apply refute 32
  rw [m.strEqWithin 32 _ _ (by simp [within]) (by simp [within])]
  simp

open LojitaCtx.Countermodel in
private theorem boundedCharCannotRefute (m : SoundCharModel) (n : Nat) :
    ¬ (∀ k, (m.atCharStage k).charEq ((m.atCharStage k).natToChar n) ((m.atCharStage k).natToChar n) = true → False) := by
  intro refute
  apply refute n
  rw [m.natToCharLaw, m.charEqLaw]
  simp

private def countermodels : IO Unit := do
  let t0 ← object "Gen.T0.Native" "def chars := String.toList\ndef pack := String.ofList\ndef charEq (c d : Char) := c == d"
  let t1 ← object "Gen.T1.Native" "def unpack (xs : List Char) := Gen.T0.Native.chars (Gen.T0.Native.pack xs)
def same (c : Char) := Gen.T0.Native.charEq c c" [toString t0.modName]
  let spec ← object "Gen.T2.Native" "axiom roundLaw : ∀ xs, Gen.T1.Native.unpack xs = xs
axiom charLaw : ∀ c, Gen.T1.Native.same c = true" [toString t1.modName]
  let bases := [t0,t1]
  discard <| checkClosedModule [t0] t1
  discard <| checkConditionalGlue bases [] spec true
  let lib := ["LojitaCtx.Countermodel"]
  let model ← object "SwapModel" "open LojitaCtx.Countermodel
def claim (a : StringAlg) := ∀ xs, a.toList (a.fromList xs) = xs
def bundle : CountermodelBundle :=
  .stringCountermodel claim (swapStringModel ' ' 'a') (by
    intro k h
    have bad := h (' ' :: List.replicate k 'a')
    change fromListSwapped ' ' 'a' k (' ' :: List.replicate k 'a') = _ at bad
    simp [fromListSwapped, swapChar] at bad)" lib
  let chars ← object "PhantomModel" "open LojitaCtx.Countermodel
def claim (a : CharAlg) := ∀ x, a.charEq x x = true
def bundle : CountermodelBundle :=
  .charCountermodel claim phantomCharModel (by
    intro k h
    have bad := h none
    contradiction)" lib
  let imports := ["CountermodelCheck",toString spec.modName]
  let refute ← object "StringEvidence" "theorem witness : CountermodelCheck.VerifiedClaim := Gen.T2.Native.roundLaw" imports
  let charRefute ← object "CharEvidence" "theorem witness : CountermodelCheck.VerifiedClaim := Gen.T2.Native.charLaw" imports
  let timed := fun (m r : LeanMod) => do
    let start ← IO.monoNanosNow
    let snap ← checkCountermodel bases spec m r
    let ms := ((← IO.monoNanosNow) - start) / 1000000
    ensure (ms < 300 && snap.declaredAxioms.isEmpty) s!"countermodel {m.modName} took {ms} ms"
    return ms
  let sm ← timed model refute
  let cm ← timed chars charRefute
  let closed ← object "Closed32" "open LojitaCtx.Countermodel
def claim (a : StringAlg) := a.strEq (a.fromList (List.replicate 32 'a')) (a.fromList (List.replicate 32 'a')) = true
def bundle : CountermodelBundle := .stringCountermodel claim (swapStringModel ' ' 'a') (by
  intro k h
  simp [claim, swapStringModel, swapStringAlg, fromListSwapped] at h)" lib
  let bounded ← object "Bounded" "open LojitaCtx.Countermodel
def claim (a : CharAlg) := a.charEq (a.natToChar 65) (a.natToChar 65) = true
def bundle : CountermodelBundle := .charCountermodel claim phantomCharModel (by
  intro k h
  simp [claim, phantomCharModel, phantomCharAlg] at h)" lib
  for m in [closed,bounded] do expectError "ELABORATION_ERROR" (checkCountermodel bases spec m refute)
  let literal ← object "Literal" "def leak := \"string literal\"" lib
  expectError "MODEL_STRING_LITERAL" (checkCountermodel bases spec literal refute)
  let imported ← object "Unauthorized" "" ["LojitaCtx.Blueprint"]
  expectError "UNAUTHORIZED_IMPORT" (checkCountermodel bases spec imported refute)
  let ax ← object "Axiomatic" "axiom cheat : False" lib
  expectError "DISALLOWED_AXIOM_VIOLATION" (checkCountermodel bases spec ax refute)
  let other ← object "WrongClaim" "theorem wrong : True := trivial" imports
  expectError "REFUTATION_TARGET_MISMATCH" (checkCountermodel bases spec model other)
  let noBundle ← object "NoPublicBundle" "private def x := 1" lib
  expectError "MISSING_COUNTERMODEL_BUNDLE" (checkCountermodel bases spec noBundle other)
  let text := "(submission (kind countermodel) (model @m) (refute @r))"
  let t := {(task spec) with baseModules := bases, drafts := Std.HashMap.ofList [("m",renderLeanMod model),("r",renderLeanMod refute)]}
  let (v,_) ← drive (fun req => if let some e := req.diagnostic then throw (IO.userError (toString e)) else pure text)
    t (leaf (empty spec.modName))
  ensure (v matches .countermodel ..) "countermodel NodeServer verdict"
  IO.println s!"4  Native interface-cut countermodels in {sm} ms (String) and {cm} ms (Char), bounded conservation and exact rejection codes"

private def filesUnder (dir : System.FilePath) : IO (List (String × Hash)) := do
  let mut todo := [dir]
  let mut files := #[]
  while let p :: rest := todo do
    todo := rest
    if ← p.isDir then
      for entry in ← p.readDir do todo := entry.path :: todo
    else files := files.push (p.toString,sha256 (← IO.FS.readBinFile p))
  return files.toList.mergeSort (fun a b => a.1 ≤ b.1)

private def preview (dir : System.FilePath) : IO Unit := do
  let old ← object "Gen.P.Root" "def n : Nat := 1\ndef use : Nat := n"
  let spec ← object "Gen.P.Root" "axiom n : Bool"
  let draft ← object "Gen.P.Root" "def n : Bool := true"
  let invalid : Plan := {
    why := "preview", newMod := some draft
    moves := [⟨.unit (q "Gen.P.Root.n"),.unit (q "Gen.P.Root.n")⟩]}
  let good := {invalid with moves := invalid.moves ++ [⟨.unit (q "Gen.P.Root.use"),.bot⟩]}
  let t := task spec
  let home := leaf old
  let before ← filesUnder dir
  let no ← planPreview t home invalid
  let yes ← planPreview t home good
  ensure (no.certificate.any (·.kind == "frontier_incomplete") && no.passed.isEmpty &&
    no.frontier == [(encObj (.unit (q "Gen.P.Root.use"))).canonical] && yes.certificate.isNone &&
    yes.passed == #["frontier","Namespace","checkConditionalGlue","satisfies","PolyTransport","Lift"]) s!"preview {repr no} {repr yes}"
  ensure ((← checkPlanJSON t home invalid).contains "frontier_incomplete" && (← filesUnder dir) == before) "preview side effect or JSON"
  let calls ← IO.mkRef 0
  let (v, result) ← drive (fun req => do
    ensure (req.task.delta.child == t.delta.child) "preview or rejection woke a child"
    let n ← calls.get
    calls.set (n+1)
    if n == 0 then return planText draft [] invalid.moves
    ensure (n == 1 && req.diagnostic == no.certificate) s!"live gate differs from preview {repr req.diagnostic}"
    return planText draft [] good.moves) t home
  ensure (v == .ok && (← calls.get) == 2 && result.code.units.length == 1) "live acceptance differs from preview"
  let mismatch ← object "Gen.P.Root" "def n : Nat := 4"
  let rr ← planPreview t home {good with newMod := some mismatch}
  ensure (rr.certificate.any (·.kind == "interface_mismatch")) "interface_mismatch"
  let badSpec ← object "Gen.P.Inconsistent" "axiom impossible : False"
  let witness ← object "Contradiction" "theorem witness : False := Gen.P.Inconsistent.impossible" [toString badSpec.modName]
  let txt := "(submission (kind contradiction) (refute @proof))\n```lean proof\n" ++ renderLeanMod witness ++ "\n```"
  let (v,_) ← drive (fun req => if let some e := req.diagnostic then throw (IO.userError (toString e)) else pure txt)
    (task badSpec) (leaf (empty badSpec.modName))
  ensure (v matches .contradiction _) "contradiction verdict"
  IO.println "5  Stateless JSON preview and live retry returned the same frontier certificate and accepted the same repair"

def run : IO Unit := IO.FS.withTempDir fun dir => do
  merkle dir
  preload
  try
    checkPlanFrontier
    polyAndLift
    narrowing
    splitChildren
    obstruction dir
    countermodels
    preview dir
  finally close

end Test.S3Harness

def main : IO Unit := Test.S3Harness.run
