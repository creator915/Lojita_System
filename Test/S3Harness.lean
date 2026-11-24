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

private def drive (ai : Proposer) (t : NodeTask) (h : Frozen)
    (accept : AcceptNode := fun _ _ => pure ()) (cancelOwner : String → IO Unit := fun _ => pure ()) : IO (Verdict × Frozen) :=
  withNodeEnvIO ai (fun env => do
    let v := thawHome h
    let init ← evalProcIO env (nodeAgent v.1) v.2
    let (some verdict, stopped) ← WorkerIO.awaitIO (← init t)
      | throw (IO.userError "scripted node stopped without a verdict")
    return (verdict, freezeHome stopped.1 stopped.2)) accept cancelOwner

private abbrev Events := Std.Mutex (Array (QName × String))

private def mark (events : Events) (owner : QName) (event : String) : IO Unit :=
  events.atomically (modify (·.push (owner, event)))

private def eventLog (events : Events) : IO (List (QName × String)) :=
  events.atomically (return (← get).toList)

private def concurrentTreeSpeedupAndDeterminism (dir : System.FilePath) : IO Unit := do
  let port := fun (name : String) => object ("Gen.Concurrent.Top" ++ name) "axiom val : Nat"
  let top ← port ""
  let a ← port ".A"
  let b ← port ".B"
  let c ← port ".C"
  let d ← port ".D"
  let a1 ← port ".A.A1"
  let a2 ← port ".A.A2"
  let join := fun (m : LeanMod) (kids : List LeanMod) =>
    let names := kids.map (toString ·.modName)
    object (toString m.modName) ("def val : Nat := " ++ String.intercalate " + " (names.map (· ++ ".val"))) names
  let rootKids := [a, b, c, d]
  let topImpl ← join top rootKids
  let aImpl ← join a [a1, a2]
  let rootPlan := planText topImpl rootKids
  let aPlan := planText aImpl [a1, a2]
  let leaves := [a1, a2, b, c, d]
  let implementations ← leaves.mapM fun m => object (toString m.modName) "def val : Nat := 1"
  let replies := Std.HashMap.ofList (implementations.map fun m => (m.modName, planText m))
  -- Check an independently assembled reference tree in the resident kernel. Both
  -- timed workers still run every plan gate and closure check through the normal entry point.
  let sealed := fun (m spec : LeanMod) (kids : List (String × Frozen)) =>
    Frozen.frozen m (inherit {birthPlan m with why := "scripted"} []) spec kids
  let slots := implementations.zipWith (fun m spec => (toString m.modName, sealed m spec [])) leaves
  let aHome := sealed (withChildIfaces aImpl [a1, a2]) a (slots.take 2)
  let reference := sealed (withChildIfaces topImpl rootKids) top ((toString a.modName, aHome) :: slots.drop 2)
  let setupStart ← IO.monoMsNow
  verifyClosure [] reference
  let expected ← storeHomeCAS dir (thawHome reference)
  for (spec, glue, kids) in [(top, topImpl, rootKids), (a, aImpl, [a1, a2])] do
    let report ← planPreview (task spec) (leaf (empty spec.modName)) (birthPlan glue) kids
    ensure report.certificate.isNone s!"invalid concurrent fixture {repr report.certificate}"
  let setupMs := (← IO.monoMsNow) - setupStart
  let run := fun (reverse : Bool) => do
    let events ← Std.Mutex.new #[]
    let started ← Std.Mutex.new (0 : Nat)
    let allStarted ← IO.Promise.new
    let fastAwake ← Std.Mutex.new (0 : Nat)
    let fastDone ← IO.Promise.new
    let fastCount := if reverse then 3 else 2
    let ai : Proposer := fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      let n := req.task.delta.child
      mark events n "start"
      if n == top.modName then return rootPlan
      if n == a.modName then return aPlan
      let some reply := replies[n]? | throw (IO.userError s!"unexpected concurrent child {n}")
      let count ← started.atomically (modifyGet fun k => (k + 1, k + 1))
      if count == leaves.length then allStarted.resolve ()
      IO.wait allStarted.result!
      let isFast := ([a1, a2].any (·.modName == n)) != reverse
      if !isFast then IO.wait fastDone.result!
      mark events n "awake"
      if isFast then
        let done ← fastAwake.atomically (modifyGet fun k => (k + 1, k + 1))
        if done == fastCount then fastDone.resolve ()
      return reply
    let start ← IO.monoMsNow
    let (v, h) ← drive ai (task top) (leaf (empty top.modName))
    let ms := (← IO.monoMsNow) - start
    ensure (v == .ok && h.children.map Prod.fst == rootKids.map (toString ·.modName) &&
      (lookupChild h a.modName).any (fun kid => kid.children.map Prod.fst == [a1, a2].map (toString ·.modName)))
      "concurrent tree did not seal in specification order"
    let log ← eventLog events
    for m in top :: a :: leaves do ensure (log.count (m.modName, "start") == 1) s!"extra turn for {m.modName}"
    let fast := if reverse then b else a1
    let slow := if reverse then a1 else b
    ensure (log.idxOf (fast.modName, "awake") < log.idxOf (slow.modName, "awake")) s!"barrier order {repr log}"
    ensure (log.idxOf (a2.modName, "start") < log.idxOf (b.modName, "awake")) "grandchildren waited for a sibling barrier"
    return (ms, ← storeHomeCAS dir (thawHome h))
  let (forward, hash) ← run false
  let (reverse, other) ← run true
  ensure (hash == expected && hash == other) "sealed Merkle root differs from the reference tree or reversed schedule"
  IO.println s!"A  Verified fixture in {setupMs} ms. Concurrent drives in {forward}/{reverse} ms, identical Merkle root {hash}"

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

open Lojita.Session in
private def deepKeptLift : IO Unit := do
  let lower := "Gen.Base.R"
  let source := "Gen.T0.R"
  let target := "Gen.T1.R"
  let slots := ["JsonInput","JsonRecords"]
  let makeTree := fun (root : String) => do
    let decode := root ++ ".Decode"
    let mut kids := []
    for slot in slots do
      let name := decode ++ "." ++ slot
      let base := lower ++ ".Decode." ++ slot
      let impl ← if root == lower then object name "def val : Nat := 7" else
        object name s!"def val : Nat := {base}.val\ntheorem square : val = {base}.val := rfl" [base]
      let spec ← object name "axiom val : Nat"
      kids := kids ++ [(name, Frozen.frozen impl [] spec [])]
    let join := fun (n : String) (children : List (String × Frozen)) => do
      let code ← object n ("def val : Nat := " ++ children.head!.1 ++ ".val") (children.map Prod.fst)
      let spec ← object n "axiom val : Nat"
      return Frozen.frozen (withChildIfaces code (children.map (·.2.spec))) [] spec children
    join root [(decode, ← join decode kids)]
  let base ← makeTree lower
  let old ← makeTree source
  let spec ← object target "axiom val : Nat"
  let dq := fun (r : String) => q (r ++ ".Decode")
  let draft ← object target ("def val := " ++ target ++ ".Decode.val") [target ++ ".Decode"]
  let h := leaf (empty spec.modName)
  let transport := TransportSpec.transportSpecTree old.code.modName spec.modName [.keepChild (dq source) (dq target)] []
  let job := fun child => {(task spec) with
    baseModules := exported base, transports := [(old,transport)]
    maybeLift := some (base.code, .liftSpecTree base.code.modName spec.modName [child] [])}
  let grand := fun (slot : String) (proof : String) =>
    let b := lower ++ ".Decode." ++ slot
    let u := target ++ ".Decode." ++ slot
    ChildLift.mkChildLift (q b) (q u) (some (.liftSpecTree (q b) (q u) []
      [endpointLift (q (b ++ ".val")) (q (u ++ ".val")) (q (u ++ "." ++ proof))]))
  let explicit := fun cs => ChildLift.mkChildLift (dq lower) (dq target) (some (.liftSpecTree (dq lower) (dq target) cs []))
  for child in [explicit (slots.map (grand · "square")), .mkChildLift (dq lower) (dq target) none,
      .moveChildLifts [dq lower] [dq target] []] do
    let t := job child
    let (report, some c) ← checkCandidateGates t h (birthPlan draft) | throw (IO.userError "deep Lift + keep failed")
    ensure report.certificate.isNone "deep keep certificate"
    let st : NodeState := {task := t, original := h, current := h}
    let r ← reconcileChildren st c
    ensure (r.toSpawn.isEmpty && r.verified.size == 1) "Decode or its grandchildren required a worker"
    let result ← finish {st with current := r.current, verified := r.verified} c
    verifyClosure (exported base) result
    let mods := exported result
    let some alias := mods.find? (·.modName == dq target) | throw (IO.userError "missing Decode alias")
    for slot in slots do
      let childName := target ++ ".Decode." ++ slot
      ensure (alias.imports.any (fun i => i.imod == q childName && i.assumes.map (·.uname) == [q (childName ++ ".val")]) &&
        mods.any (·.modName == q childName)) "missing requalified grandchild contract"
    ensure ((duplicates (mods.map (·.modName))).isEmpty) "duplicate deep alias"
  for (child,kind) in [(explicit [], "missingChildMap"), (explicit (slots.map (grand · "absent")), "missingSquare")] do
    let r ← planPreview (job child) h (birthPlan draft)
    ensure (r.certificate.any (·.kind == kind)) s!"unchecked explicit deep lift: {repr r}"
  IO.FS.withTempDir fun ws => do
    initWorkspace ws
    discard <| publishTree ws "Base" "vertical source" [] [] .ok base
    let closure ← loadCurrentClosure ws ["Base"]
    verifyClosure closure.modules old
    discard <| publishTree ws "T0" "horizontal source" ["Base"] closure.directTips .ok old
    let t := job (.mkChildLift (dq lower) (dq target) none)
    let some (_,ls) := t.maybeLift | throw (IO.userError "missing fixture lift")
    let lift := (encodeLiftSpec ls).canonical
    let prepared ← prepareSpec ws "T1" (renderLeanMod spec) ["Base"] lift (encodeTransportSpec transport).canonical
    let r ← planPreview prepared.task prepared.home (birthPlan draft)
    ensure r.certificate.isNone s!"session preflight rejected a shorthand kept subtree: {repr r}"
  -- S2: Strip a dead non-base peer root import even when squares are empty and a kept child
  -- under that root prefix is used; reject operational use of the non-base peer at the gate.
  let deadPeerDraft ← object target ("def val := " ++ target ++ ".Decode.val") [source, target ++ ".Decode"]
  let (deadRep, some deadCand) ← checkCandidateGates (job (.mkChildLift (dq lower) (dq target) none)) h (birthPlan deadPeerDraft)
    | throw (IO.userError "S2 dead peer import with empty squares was rejected")
  ensure (deadRep.certificate.isNone && !deadCand.code.imports.any (·.imod == old.code.modName))
    s!"S2 dead peer root import survived sealing: {repr deadCand.code.imports}"
  let stDead : NodeState := {task := job (.mkChildLift (dq lower) (dq target) none), original := h, current := h}
  let recDead ← reconcileChildren stDead deadCand
  let sealedDead ← finish {stDead with current := recDead.current, verified := recDead.verified} deadCand
  verifyClosure (exported base) sealedDead
  let peerLeakDraft ← object target ("def val := " ++ source ++ ".val") [source, target ++ ".Decode"]
  let peerLeakRep ← planPreview (job (.mkChildLift (dq lower) (dq target) none)) h (birthPlan peerLeakDraft)
  ensure (peerLeakRep.certificate.any (·.kind == "transient_peer_leak"))
    s!"S2 operational use of non-base peer was not rejected at the gate: {repr peerLeakRep}"
  -- S2/S3 transitive peer child modules: private helper referencing a non-base peer child module
  -- (Gen.T0.R.Decode) for a declared square is stripped cleanly; surviving/public use of that
  -- peer child module emits transient_peer_leak.
  let sqName := q (target ++ ".sq")
  let tsWithSq := TransportSpec.transportSpecTree old.code.modName spec.modName
    [.keepChild (dq source) (dq target)] [polySquare [q (source ++ ".val")] [q (target ++ ".val")] sqName]
  let jobSq := {(job (.mkChildLift (dq lower) (dq target) none)) with transports := [(old, tsWithSq)]}
  let childHelperDraft ← object target
    s!"def val := {target}.Decode.val * 0 + 7
private theorem peerChildHelper : {source}.Decode.val = 7 := rfl
theorem sq : {source}.val = val := by
  change {source}.Decode.val = {target}.Decode.val * 0 + 7
  simp [peerChildHelper]" [source, target ++ ".Decode"]
  let (chRep, some chCand) ← checkCandidateGates jobSq h (birthPlan childHelperDraft)
    | throw (IO.userError "private helper referencing non-base peer child module failed gate")
  ensure (chRep.certificate.isNone &&
    !chCand.code.units.any (fun u => [sqName, q (target ++ ".peerChildHelper")].contains u.uname) &&
    !chCand.code.imports.any (·.imod == old.code.modName))
    s!"non-base peer child helper or peer import survived sealing: {repr chCand.code}"
  let stCh : NodeState := {task := jobSq, original := h, current := h}
  let recCh ← reconcileChildren stCh chCand
  let sealedCh ← finish {stCh with current := recCh.current, verified := recCh.verified} chCand
  verifyClosure (exported base) sealedCh
  let childLeakDraft ← object target s!"def val := {source}.Decode.val" [source, target ++ ".Decode"]
  let childLeakRep ← planPreview (job (.mkChildLift (dq lower) (dq target) none)) h (birthPlan childLeakDraft)
  ensure (childLeakRep.certificate.any (fun c => c.kind == "transient_peer_leak" && c.witness == source ++ ".Decode"))
    s!"surviving use of non-base peer child module did not emit transient_peer_leak: {repr childLeakRep}"

private def inPlaceSquare : IO Unit := do
  let n := "Gen.T1.InPlace"
  let operand := n ++ ".Operand"
  let spec ← object n "open LojitaCtx.World\naxiom fn : Nat → Nat\naxiom app : CliApp []" ["LojitaCtx.World"]
  let opSpec ← object operand "axiom fn : Nat → Nat"
  let op ← object operand "def fn (x : Nat) := x + 1"
  let app := "def app : CliApp [] := pure (fn 4)"
  let old ← object n s!"open LojitaCtx.World\ndef fn := {operand}.fn\n{app}" ["LojitaCtx.World",operand]
  let h := Frozen.frozen (withChildIfaces old [opSpec]) [] spec [(operand, .frozen op [] opSpec [])]
  let square := q (n ++ ".square")
  let fn := q (n ++ ".fn")
  let ts := TransportSpec.transportSpecTree spec.modName spec.modName [.keepChild op.modName op.modName]
    [⟨[fn],[fn],square,[fn]⟩]
  let t := {(task spec) with transports := [(h,ts)], allowedAncestors := some []}
  let impl := fun body => object n ("open LojitaCtx.PolyTransport LojitaCtx.World Old.Gen.T1\ndef fn (x : Nat) := " ++ body ++ "\n" ++ app ++
    s!"\ntheorem square : TransportsPoly (idPort Nat) (idPort Nat) (fun _ => True) Old.{n}.fn fn := by
  intro x y _ h
  change x = y at h
  subst y
  rfl") ["LojitaCtx.PolyTransport","LojitaCtx.World","Old." ++ n,operand]
  let draft ← impl "Nat.succ x"
  let entry := q (n ++ ".app")
  let moves : List Proarrow := [⟨.unit fn,.unit fn⟩,⟨.unit entry,.unit entry⟩,⟨.bot,.unit square⟩]
  let p := {birthPlan draft with moves}
  let (report,c) ← checkCandidateGates t h p
  ensure (report.certificate.isNone && c.any (fun v => !(v.code.units.map (·.uname)).contains square))
    s!"old snapshot square: {repr report}"
  -- C1: Same-name in-place squares MUST reference Old.*, never only the shadowed new name.
  let reflexiveEq ← object n ("open LojitaCtx.World\ndef fn (x : Nat) := Nat.succ x\n" ++ app ++
    "\ntheorem square : ∀ x, fn x = fn x := fun _ => rfl") ["LojitaCtx.World", operand]
  let reflexivePoly ← object n ("open LojitaCtx.PolyTransport LojitaCtx.World\ndef fn (x : Nat) := Nat.succ x\n" ++ app ++
    "\ntheorem square : TransportsPoly (idPort Nat) (idPort Nat) (fun _ => True) fn fn := by
  intro x y _ h
  change x = y at h
  subst y
  rfl") ["LojitaCtx.PolyTransport", "LojitaCtx.World", operand]
  let tsNoRefs := TransportSpec.transportSpecTree spec.modName spec.modName [.keepChild op.modName op.modName]
    [polySquare [fn] [fn] square]
  for fake in [reflexiveEq, reflexivePoly] do
    for taskVar in [t, {t with transports := [(h, tsNoRefs)]}] do
      let fakeRep ← planPreview taskVar h {p with newMod := some fake}
      ensure (fakeRep.certificate.any (fun cert => cert.kind == "missingOldEndpoint" && cert.cause.contains (reprStr fn)))
        s!"C1 reflexive same-name square bypassed Old.* check: {repr fakeRep}"
  -- S3: Private helper lemmas referencing Old.* (transitively) for a square are stripped at seal;
  -- public helpers or operational private helpers referencing Old.* are rejected at the gate and in MCP check_lean.
  let helperDraft ← object n ("open LojitaCtx.PolyTransport LojitaCtx.World Old.Gen.T1\ndef fn (x : Nat) := Nat.succ x\n" ++ app ++
    s!"\nprivate theorem helper1 (x : Nat) : Old.{n}.fn x = x + 1 := rfl
private theorem helper2 (x : Nat) : Old.{n}.fn x = fn x := helper1 x
theorem square : TransportsPoly (idPort Nat) (idPort Nat) (fun _ => True) Old.{n}.fn fn := by
  intro x y _ h
  change x = y at h
  subst y
  exact helper2 x") ["LojitaCtx.PolyTransport","LojitaCtx.World","Old." ++ n,operand]
  let helperMoves : List Proarrow := [⟨.unit fn,.unit fn⟩,⟨.unit entry,.unit entry⟩,
    ⟨.bot,.unit (q (n ++ ".helper1"))⟩,⟨.bot,.unit (q (n ++ ".helper2"))⟩,⟨.bot,.unit square⟩]
  let (helperRep, some helperCand) ← checkCandidateGates t h {birthPlan helperDraft with moves := helperMoves}
    | throw (IO.userError "S3 private Old.* helper lemmas failed gate")
  ensure (helperRep.certificate.isNone &&
    !helperCand.code.units.any (fun u => [square, q (n ++ ".helper1"), q (n ++ ".helper2")].contains u.uname) &&
    !helperCand.code.imports.any (·.imod == q ("Old." ++ n)))
    s!"S3 private Old.* helper survived sealing: {repr helperCand.code}"
  let pubHelperDraft ← object n ("open LojitaCtx.PolyTransport LojitaCtx.World Old.Gen.T1\ndef fn (x : Nat) := Nat.succ x\n" ++ app ++
    s!"\ntheorem helperPub (x : Nat) : Old.{n}.fn x = fn x := rfl
theorem square : TransportsPoly (idPort Nat) (idPort Nat) (fun _ => True) Old.{n}.fn fn := by
  intro x y _ h
  change x = y at h
  subst y
  exact helperPub x") ["LojitaCtx.PolyTransport","LojitaCtx.World","Old." ++ n,operand]
  let pubHelperRep ← planPreview t h {birthPlan pubHelperDraft with moves :=
    [⟨.unit fn,.unit fn⟩,⟨.unit entry,.unit entry⟩,⟨.bot,.unit (q (n ++ ".helperPub"))⟩,⟨.bot,.unit square⟩]}
  ensure (pubHelperRep.certificate.any (·.kind == "transient_snapshot_leak"))
    s!"S3 public Old.* helper was not rejected: {repr pubHelperRep}"
  let privLeakDraft ← object n ("open LojitaCtx.PolyTransport LojitaCtx.World Old.Gen.T1\nprivate def leak (x : Nat) := Old." ++ n ++
    ".fn x\ndef fn (x : Nat) := leak x\n" ++ app ++
    s!"\ntheorem square : TransportsPoly (idPort Nat) (idPort Nat) (fun _ => True) Old.{n}.fn fn := by
  intro x y _ h
  change x = y at h
  subst y
  rfl") ["LojitaCtx.PolyTransport","LojitaCtx.World","Old." ++ n,operand]
  let privLeakRep ← planPreview t h {birthPlan privLeakDraft with moves :=
    [⟨.unit fn,.unit fn⟩,⟨.unit entry,.unit entry⟩,⟨.bot,.unit (q (n ++ ".leak"))⟩,⟨.bot,.unit square⟩]}
  ensure (privLeakRep.certificate.any (·.kind == "transient_snapshot_leak"))
    s!"S3 operational private Old.* helper was not rejected: {repr privLeakRep}"
  IO.FS.withTempDir fun dir => do
    let repo ← IO.FS.realPath "."
    Lojita.Session.writeContext dir ⟨t,old,h.memory,none,some h⟩
    let rpc := fun (id : Nat) (method : String) (args : Lean.Json) => Lean.Json.mkObj [
      ("jsonrpc","2.0"),("id",Lean.toJson id),("method","tools/call"),
      ("params",Lean.Json.mkObj [("name",method),("arguments",args)])]
    let queries := [
      rpc 1 "check_lean" (Lean.Json.mkObj [("source",renderLeanMod draft),("dep_blocks",Lean.toJson [renderLeanMod opSpec])]),
      rpc 2 "check_plan" (Lean.Json.mkObj [("submission",planText draft [] moves)]),
      rpc 3 "check_lean" (Lean.Json.mkObj [("source",renderLeanMod helperDraft),("dep_blocks",Lean.toJson [renderLeanMod opSpec])]),
      rpc 4 "check_lean" (Lean.Json.mkObj [("source",renderLeanMod privLeakDraft),("dep_blocks",Lean.toJson [renderLeanMod opSpec])])]
    let input ← IO.mkRef {data := (String.intercalate "\n" (queries.map (·.compress)) ++ "\n").toUTF8 : IO.FS.Stream.Buffer}
    let output ← IO.mkRef ({} : IO.FS.Stream.Buffer)
    IO.withStdin (.ofBuffer input) <| IO.withStdout (.ofBuffer output) <| Lojita.MCP.serve {mode := .node, repo, ctx := dir}
    let replies := (String.fromUTF8! (← output.get).data).splitOn "\n" |>.filter (!·.isEmpty)
    ensure (replies.length == 4 &&
      (replies.take 3).all (·.contains "\"isError\":false") &&
      replies[3]!.contains "\"isError\":true" && replies[3]!.contains "transient_snapshot_leak")
      s!"MCP snapshot preflight disagreed with the gate: {replies}"
  let (v,sealed) ← drive (fun req => do
    if let some cert := req.diagnostic then throw (IO.userError (toString cert))
    ensure (req.task.delta.child == spec.modName) "unchanged Operand was re-driven"
    return planText draft [] moves) t h
  verifyClosure [] sealed
  ensure (v == .ok && (exported sealed).all (fun m => !(renderLeanMod m).contains "Old.")) "sealed snapshot dependency"
  IO.FS.withTempDir fun dir => do
    let bin := dir / "candidate"
    compileVerifiedExe (exported sealed) entry .cli bin
    ensure ((← IO.Process.output {cmd := bin.toString}).exitCode == 5) "in-place candidate did not run the sealed function"
  let leaking ← impl ("Old." ++ n ++ ".fn x")
  let r ← planPreview t h {p with newMod := some leaking}
  ensure (r.certificate.any (·.kind == "transient_snapshot_leak")) "operational use of a retired snapshot survived sealing"
  IO.println "   Deep kept aliases, explicit and inferred grandchild lifts, C1/S2/S3 sealing, and in-place snapshot proof erasure"

private def historicalFrontier : IO Unit := do
  let base ← object "Gen.T0.Obsolete" "theorem fact : True := trivial"
  let old ← object "Gen.T1.History" "theorem premise : True := Gen.T0.Obsolete.fact
theorem dependent : True := by first | exact premise | trivial" [toString base.modName]
  -- Model an old stored reference hint that missed a tactic dependency.
  let h := leaf {old with units := old.units.map fun u => {u with synRefs := []}}
  let spec ← object (toString old.modName) "axiom dependent : True"
  let dep := Obj.unit (q "Gen.T1.History.dependent")
  let p : Plan := {
    why := "remove the obsolete premise"
    moves := [⟨.ext base.modName,.bot⟩,⟨.unit (q "Gen.T1.History.premise"),.bot⟩]}
  let t := {(task spec) with oldBaseModules := some [base]}
  let pinned ← planPreview t h p
  ensure (pinned.certificate.any (·.kind == "frontier_incomplete") && pinned.frontier == [(encObj dep).canonical])
    "the historical semantic frontier missed the tactic dependency"
  let acknowledged ← planPreview t h {p with moves := ⟨dep,dep⟩ :: p.moves}
  ensure acknowledged.certificate.isNone s!"acknowledged historical frontier failed: {repr acknowledged}"
  -- C3: Broken pinned historical bases emit an explicit gate certificate; unpinned elaboration failure
  -- falls back conservatively so unmoved old units are never silently skipped.
  let brokenPinned ← planPreview {t with oldBaseModules := some []} h p
  ensure (brokenPinned.certificate.any (·.kind == "historical_elaboration_failed"))
    s!"broken pinned oldBaseModules did not emit historical_elaboration_failed: {repr brokenPinned}"
  let fallback ← planPreview {t with oldBaseModules := none} h p
  ensure (fallback.certificate.any (·.kind == "frontier_incomplete") && fallback.frontier == [(encObj dep).canonical])
    s!"unpinned elaboration failure silently bypassed conservative frontier: {repr fallback}"
  let fallbackAck ← planPreview {t with oldBaseModules := none} h {p with moves := ⟨dep,dep⟩ :: p.moves}
  ensure fallbackAck.certificate.isNone s!"conservative frontier deadlocked when all old units moved: {repr fallbackAck}"
  -- S5: Candidate-era saved child spec whose units differ from old.code's import assumptions
  -- must not poison historical elaboration of old.code.
  let kidName := "Gen.T1.HistChild.Kid"
  let oldKidSpec ← object kidName "axiom val : Nat"
  let candKidSpec ← object kidName "axiom val : Bool\naxiom extra : Nat"
  let candKidImpl ← object kidName "def val : Bool := true\ndef extra : Nat := 0"
  let oldParent ← object "Gen.T1.HistChild"
    s!"def a : Nat := {kidName}.val\ndef b : Nat := a + 1" [kidName]
  let oldParentHome := Frozen.frozen (withChildIfaces oldParent [oldKidSpec]) []
    (← object "Gen.T1.HistChild" "axiom b : Nat")
    [(kidName, Frozen.frozen candKidImpl [] candKidSpec [])]
  let nextParent ← object "Gen.T1.HistChild" "def b : Nat := 42"
  let parentMoves : List Proarrow := [
    ⟨.ext (q kidName), .bot⟩,
    ⟨.unit (q "Gen.T1.HistChild.a"), .bot⟩,
    ⟨.unit (q "Gen.T1.HistChild.b"), .unit (q "Gen.T1.HistChild.b")⟩]
  let s5Rep ← planPreview {(task (← object "Gen.T1.HistChild" "axiom b : Nat")) with oldBaseModules := some []}
    oldParentHome {why := "drop kid", newMod := some nextParent, moves := parentMoves}
  ensure s5Rep.certificate.isNone s!"S5 candidate-era child spec poisoned oldStubs: {repr s5Rep}"
  -- Verifier #3: Empty-assumes closed base-module .ext moves must NOT vacuously preserve
  -- across conservative fallback, renamed bases, or updated base versions.
  let baseA ← object "Gen.T0.BaseA" "def k : Nat := 1"
  let baseA2 ← object "Gen.T0.BaseA" "def k : Nat := 2"
  let baseB ← object "Gen.T0.BaseB" "def k : Nat := 1"
  let useA ← object "Gen.T1.ExtMove" "def val : Nat := Gen.T0.BaseA.k" ["Gen.T0.BaseA"]
  let useB ← object "Gen.T1.ExtMove" "def val : Nat := Gen.T0.BaseB.k" ["Gen.T0.BaseB"]
  let valObj := Obj.unit (q "Gen.T1.ExtMove.val")
  let renameExt : Plan := {why := "swap base", moves := [⟨.ext baseA.modName, .ext baseB.modName⟩]}
  ensure (!preserves useA useB renameExt ⟨.ext baseA.modName, .ext baseB.modName⟩ &&
    frontier useA useB renameExt == [valObj])
    "renamed closed base-module .ext move vacuously returned preserved=true"
  let snapA1 ← checkClosedModule [baseA] useA
  let snapA2 ← checkClosedModule [baseA2] useA
  let idExt : Plan := {why := "keep base", moves := [⟨.ext baseA.modName, .ext baseA.modName⟩]}
  ensure (!preserves useA useA idExt ⟨.ext baseA.modName, .ext baseA.modName⟩ none (some snapA1) &&
    frontier useA useA idExt none (some snapA1) == [valObj])
    "conservative frontier on closed base-module (.ext Base, .ext Base) vacuously returned preserved=true"
  ensure (preserves useA useA idExt ⟨.ext baseA.modName, .ext baseA.modName⟩ (some snapA1) (some snapA1) &&
    !preserves useA useA idExt ⟨.ext baseA.modName, .ext baseA.modName⟩ (some snapA1) (some snapA2) &&
    frontier useA useA idExt (some snapA1) (some snapA2) == [valObj])
    "semantic frontier missed updated closed base-module version on (.ext Base, .ext Base)"

private def obstruction (dir : System.FilePath) (parserFirst := false) : IO Unit := do
  let bad ← object "Gen.T0.Doc" "def singlePass (_ : Nat) := 0\ntheorem badSinglePass : singlePass 1 = 0 := rfl"
  let fixed ← object "Gen.T0.Doc" "def singlePass (n : Nat) := n"
  let lower ← object "Gen.T0.Root" "def version := 1" ["Gen.T0.Doc"]
  let upper ← object "Gen.T1.Doc" "axiom value : Nat"
  let esc ← object "Gen.T1.Doc.Escape" "axiom escape : Nat → Nat"
  let parser ← object "Gen.T1.Doc.ParseLine" "axiom parse : Nat → Nat
axiom law : parse 1 = Gen.T0.Doc.singlePass 1
axiom atOne : parse 1 = 1" ["Gen.T0.Doc"]
  let children := if parserFirst then [parser, esc] else [esc, parser]
  let main ← object (toString upper.modName) "def value := Gen.T1.Doc.Escape.escape 1 + Gen.T1.Doc.ParseLine.parse 1"
    (children.map (toString ·.modName))
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
    let events ← Std.Mutex.new #[]
    let lettersStarted ← IO.Promise.new
    let parserAccepted ← IO.Promise.new
    let ai : Proposer := fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      let owner := req.task.delta.child
      mark events owner "start"
      if owner == upper.modName then return planText main children
      if owner == esc.modName then return planText escImpl [letters]
      if owner == letters.modName then
        if parserFirst && !repair then
          lettersStarted.resolve ()
          IO.wait parserAccepted.result!
        return planText letterImpl
      if owner == parser.modName then
        if parserFirst && !repair then IO.wait lettersStarted.result!
        return if repair then planText parseImpl else refuteText "refute-lift" witness
      throw (IO.userError s!"unscripted child {owner}")
    let (v,f) ← drive ai t h (fun t _ => do
      mark events t.delta.child "accepted"
      if t.delta.child == parser.modName then parserAccepted.resolve ()) (fun n => mark events (q n) "aborted")
    let log ← eventLog events
    if parserFirst && !repair then
      for kid in [letters, esc] do
        ensure (log.contains (kid.modName, "accepted") &&
          log.idxOf (parser.modName, "accepted") < log.idxOf (kid.modName, "accepted")) "obstruction did not finish first"
    ensure (!(log.any (·.2 == "aborted"))) "obstruction cancelled an innocent sibling"
    return (v, f, fun n => log.count (n, "start"))
  let (v,partialHome,turns) ← run (job bad) (leaf (empty upper.modName)) false
  let .liftObstruction _ culprits _ := v | throw (IO.userError s!"wrong verdict {repr v}")
  ensure (culprits.contains (q "Gen.T0.Doc.badSinglePass") &&
    [upper, esc, parser, letters].all (fun m => turns m.modName == 1)) "obstruction provenance or AI turns"
  let [(slot, kept)] := partialHome.children | throw (IO.userError "expected one verified innocent sibling")
  ensure (slot == toString esc.modName && kept.code == withChildIfaces escImpl [letters] && kept.spec == esc &&
    (lookupChild kept letters.modName).any (·.code == letterImpl)) "Escape changed during rollback"
  let hash ← storeFrozen dir partialHome
  writeRef dir .partial "T1.Doc" hash
  let reload ← loadFrozen dir ((← readRef dir .partial "T1.Doc").getD "")
  let keep := TransportSpec.transportSpecTree reload.code.modName upper.modName [.keepChild esc.modName esc.modName] []
  let (v,success,turns) ← run {(job fixed) with transports := [(reload,keep)]} reload true
  let some sameKid := lookupChild success esc.modName | throw (IO.userError "missing retained Escape")
  ensure (v == .ok && turns esc.modName == 0 && turns letters.modName == 0 && turns parser.modName == 1 &&
    (← storeFrozen dir sameKid) == (← storeFrozen dir kept)) "keepChild replay or Merkle identity"
  let linked ← checkClosedModule (depsExcept (exported success ++ [fixed,lower]) success.code) success.code
  ensure (linked.axioms.all trustedBaseAxioms.contains) "final closure has an open assumption"
  let extra ← object "UnusedEvidence" "axiom extra : Nat\ntheorem obstruction : False :=
  Nat.one_ne_zero (Gen.T1.Doc.ParseLine.atOne.symm.trans (Gen.T1.Doc.ParseLine.law.trans Gen.T0.Doc.badSinglePass))"
    ["Gen.T0.Doc",toString parser.modName]
  expectError "DISALLOWED_AXIOM_VIOLATION" (checkLiftRefutation [bad] parser extra)
  if parserFirst then IO.println "C  Parser obstructed first. Escape and Letters sealed and replayed with zero AI turns."
  else IO.println "3  Many-to-many lift, kernel False witness, retained Escape Merkle identity. Escape AI turns 1 then 0"

private def orderIndependentObstructionHarvest (dir : System.FilePath) : IO Unit := do
  obstruction dir true
  let spec := empty (q "Order")
  let home := leaf spec
  let names := ["Order.Z", "Order.A", "Order.B"]
  let state : NodeState := {
    task := task spec, original := home, current := home
    verified := Std.HashMap.ofList (names.map (·, home))}
  let c : Candidate := ⟨spec, [empty (q "Order.B")], [], {why := "order"}, [], {}⟩
  ensure ((freezeVerifiedKids state).children.map Prod.fst == ["Order.A", "Order.B", "Order.Z"] &&
    (freezeVerifiedKids {state with candidate := some c}).children.map Prod.fst == ["Order.B", "Order.A", "Order.Z"])
    "partial home order changed outside the candidate frontier"
  let salvagedHome := Frozen.frozen (empty (q "Order.S")) [(.flags, ["salvaged"])] (empty (q "Order.S")) []
  let staleA := Frozen.frozen (empty (q "Order.A")) [(.flags, ["stale"])] (empty (q "Order.A")) []
  let withSalvage := {state with salvaged := Std.HashMap.ofList [("Order.S", salvagedHome), ("Order.A", staleA)]}
  let frozen := freezeVerifiedKids withSalvage
  ensure (frozen.children.map Prod.fst == ["Order.A", "Order.B", "Order.S", "Order.Z"] &&
    (lookupChild frozen (q "Order.A")).any (·.memory == []) &&
    (lookupChild frozen (q "Order.S")).any (·.memory == [(.flags, ["salvaged"])]))
    "freezeVerifiedKids dropped salvaged subtree or overwrote verified slot"

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

private def phantomModel : IO LeanMod := object "PhantomModel" "open LojitaCtx.Countermodel
def claim (a : CharAlg) := ∀ x, a.charEq x x = true
def bundle : CountermodelBundle :=
  .charCountermodel claim phantomCharModel (by
    intro k h
    have bad := h none
    contradiction)" ["LojitaCtx.Countermodel"]

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
  let chars ← phantomModel
  let imports := ["CountermodelCheck",toString spec.modName]
  let refute ← object "StringEvidence" "theorem witness : CountermodelCheck.VerifiedClaim := Gen.T2.Native.roundLaw" imports
  let charRefute ← object "CharEvidence" "theorem witness : CountermodelCheck.VerifiedClaim := Gen.T2.Native.charLaw" imports
  let timed := fun (m r : LeanMod) => do
    let start ← IO.monoNanosNow
    let snap ← checkCountermodel bases spec m r
    let ms := ((← IO.monoNanosNow) - start) / 1000000
    ensure snap.declaredAxioms.isEmpty s!"countermodel {m.modName} declared axioms"
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

private inductive RepairOutcome where
  | repair | refuteParent | proposerError
  deriving BEq

-- Hold a grandchild in its proposer until its owner cancels it. Its sibling has
-- already sealed, so the replacement branch must be able to reuse that sibling.
private def replanCancellationAndSalvage : IO Unit := do
  let rootName := "Gen.Harvest.Root"
  let branchName := rootName ++ ".Branch"
  let branch ← object branchName "axiom old : Nat"
  let revised ← object branchName "axiom next : Nat"
  let kept ← object (branchName ++ ".Keep") "axiom val : Nat"
  let blocked ← object (branchName ++ ".Waiting") "axiom val : Nat"
  let extra ← object (rootName ++ ".Extra") "axiom val : Nat"
  let flaw ← object (rootName ++ ".Bad") "def zero : Nat := 0\naxiom bad : zero = 1"
  let childProof ← object "HarvestEvidence" s!"theorem witness : False := Nat.zero_ne_one {flaw.modName}.bad"
    [toString flaw.modName]
  let parentProof ← object "HarvestRootEvidence" s!"theorem witness : False := {rootName}.impossible" [rootName]
  let oldBranch ← object branchName s!"def old := {kept.modName}.val + {blocked.modName}.val"
    [toString kept.modName, toString blocked.modName]
  let newBranch ← object branchName s!"def next := {kept.modName}.val" [toString kept.modName]
  let leafPlan := fun (m : LeanMod) => planText <$> object (toString m.modName) "def val : Nat := 9"
  let keptPlan ← leafPlan kept
  let extraPlan ← leafPlan extra
  let repaired ← object rootName s!"def val := {branchName}.next + {extra.modName}.val" [branchName, toString extra.modName]
  let moves : List Proarrow := [⟨.ext flaw.modName, .bot⟩, ⟨.ext branch.units.head!.uname, .ext revised.units.head!.uname⟩,
    ⟨.unit repaired.units.head!.uname, .unit repaired.units.head!.uname⟩]
  for outcome in [RepairOutcome.repair, .refuteParent, .proposerError] do
    let refuteParent := outcome == .refuteParent
    let root ← object rootName ("axiom val : Nat" ++ (if refuteParent then "\naxiom impossible : False" else ""))
    let children := [flaw, branch, extra]
    let main ← object rootName (s!"def val := {branchName}.old + {extra.modName}.val" ++
      (if refuteParent then s!"\ntheorem impossible : False := Nat.zero_ne_one {flaw.modName}.bad" else ""))
      (children.map (toString ·.modName))
    let events ← Std.Mutex.new #[]
    let keptReady ← IO.Promise.new
    let extraReady ← IO.Promise.new
    let waiting ← IO.Promise.new
    let cancelled ← IO.Promise.new
    let ai : Proposer := fun req => do
      let n := req.task.delta.child
      mark events n "start"
      if let some cert := req.diagnostic then
        ensure (n == root.modName && !(← eventLog events).any (·.2 == "abort")) s!"premature abort {cert}"
        if cert.kind == "child_contradiction" then
          if refuteParent then return refuteText "contradiction" parentProof
          if outcome == .proposerError then throw (IO.userError "replan proposer failed")
          -- A rejected repair must leave exactly the same live channels in place.
          return planText repaired [revised] (⟨.unit (q "missing"), .bot⟩ :: moves)
        ensure (!refuteParent && cert.kind == "unknownSrc") s!"unexpected repair error {cert}"
        return planText repaired [revised] moves
      if n == root.modName then return planText main children
      if n == extra.modName then return extraPlan
      if n == flaw.modName then
        IO.wait keptReady.result!
        IO.wait extraReady.result!
        IO.wait waiting.result!
        return refuteText "contradiction" childProof
      if n == branch.modName then
        return if req.task.delta.newIface == revised then planText newBranch [kept] else planText oldBranch [kept, blocked]
      if n == kept.modName then return keptPlan
      if n == blocked.modName then
        waiting.resolve ()
        IO.wait cancelled.result!
        throw (IO.userError "proposer terminated by owner")
      throw (IO.userError s!"unexpected harvest child {n}")
    let accept : AcceptNode := fun t _ => do
      if t.delta.child == kept.modName then keptReady.resolve ()
      if t.delta.child == extra.modName then extraReady.resolve ()
    let cancel := fun n => do
      mark events (q n) "abort"
      if n == toString blocked.modName then cancelled.resolve ()
    let result ← (drive ai (task root) (leaf (empty root.modName)) accept cancel).toBaseIO
    let log ← eventLog events
    ensure (log.count (kept.modName, "start") == 1 && log.count (extra.modName, "start") == 1 &&
      log.count (branch.modName, "abort") == 1 && log.count (blocked.modName, "abort") == 1)
      "invalidated branch leaked, restarted a sealed child, or missed cancellation"
    if outcome == .proposerError then
      let .error (.userError "replan proposer failed") := result | throw (IO.userError "lost replan failure")
      continue
    let (v, h) ← EIO.ofExcept result
    if refuteParent then
      ensure (v == .contradiction parentProof &&
        h.children.map Prod.fst == [toString kept.modName, toString extra.modName])
        "parent's own refutation lost its verdict, dropped salvaged grandchild, or retained an unsealed branch"
    else
      let some b := lookupChild h revised.modName | throw (IO.userError "missing replacement branch")
      ensure (v == .ok && log.count (branch.modName, "start") == 2 &&
        b.children.map Prod.fst == [toString kept.modName]) "aborted branch did not yield its verified grandchild"
      verifyClosure [] h

private def reverseDialecticaLocalAbsorptionAndInFlightSurvival : IO Unit := do
  let top ← object "Gen.RD.Top" "axiom val : Nat"
  let mid ← object "Gen.RD.Top.Mid" "axiom val : Nat\nexample : val = val := rfl"
  let uncle ← object "Gen.RD.Top.Uncle" "axiom val : Nat"
  let slow ← object "Gen.RD.Top.Mid.SlowInnocent" "axiom val : Nat"
  let badName := "Gen.RD.Top.Mid.Bad"
  let good ← object badName "axiom good : Nat"
  let support ← object "Gen.RD.Support" "def initial : Nat := 0\ndef same (c : Char) := c == c"
  let model ← phantomModel
  let topImpl ← object (toString top.modName) "def val := Gen.RD.Top.Mid.val + Gen.RD.Top.Uncle.val"
    [toString mid.modName, toString uncle.modName]
  let glue := fun (name : String) => object (toString mid.modName)
    s!"def val := {slow.modName}.val + {badName}.{name}" [badName, toString slow.modName]
  let before ← glue "unused"
  let after ← glue "good"
  let topPlan := planText topImpl [mid, uncle]
  let answer := fun (m : LeanMod) => object (toString m.modName) "def val : Nat := 42"
  let slowPlan := planText (← answer slow)
  let unclePlan := planText (← answer uncle)
  let goodPlan := planText (← object badName "def good : Nat := 7")
  for isModel in [false, true] do
    let helper := if isModel then "sameChar" else "zero"
    let body := if isModel then "def sameChar := same\naxiom bad : ∀ c, sameChar c = true"
      else "def zero : Nat := initial\naxiom bad : zero = 1"
    let bad ← object badName ("open Gen.RD.Support\n" ++ body ++ "\naxiom unused : Nat") [toString support.modName]
    let target := if isModel then "CountermodelCheck.VerifiedClaim" else "False"
    let term := if isModel then s!"{badName}.bad" else s!"Nat.zero_ne_one {badName}.bad"
    let proof ← object "RDEvidence" s!"private theorem step : {target} := {term}
theorem refuted : {target} := step
theorem irrelevant : {badName}.unused = {badName}.unused := rfl"
      (badName :: (if isModel then ["CountermodelCheck"] else []))
    let why := "The interface assumes the missing character equality law."
    let evidence := if isModel then
        s!"(submission (kind countermodel) (why \"{why}\") (model @m) (refute @r))\n```lean m\n{renderLeanMod model}\n```\n```lean r\n{renderLeanMod proof}\n```"
      else refuteText "contradiction" proof
    let kind := if isModel then "child_countermodel" else "child_contradiction"
    let law := q (badName ++ ".bad")
    let used := [law, q (badName ++ "." ++ helper)].mergeSort (fun x y => x.toLeanName.lt y.toLeanName)
    let snap ← if isModel then checkCountermodel [support] bad model proof else checkRefutation [support] bad proof
    let targets := if isModel then [`CountermodelCheck.VerifiedClaim] else [``False]
    ensure (extractCulpritAssumptions bad {snap with owners := snap.owners.erase law.toLeanName} targets == used)
      "transitive provenance lost a direct axiom or included an unrelated theorem"
    let moves : List Proarrow := [⟨Obj.ext law, .ext good.units.head!.uname⟩,
      ⟨.ext (q (badName ++ ".unused")), .ext good.units.head!.uname⟩,
      ⟨.unit before.units.head!.uname, .unit after.units.head!.uname⟩]
    let firstPlan := planText before [bad, slow]
    -- The unchanged SlowInnocent contract comes from the last accepted snapshot.
    let repair := planText after [good] moves
    let privateNote := "private child exploration"
    let badSeed := Frozen.frozen (empty bad.modName) [(.flags, [privateNote])] (empty bad.modName) []
    let midSeed := Frozen.frozen (empty mid.modName) [] mid [(badName, badSeed)]
    let root := Frozen.frozen (empty top.modName) [] top [(toString mid.modName, midSeed)]
    let events ← Std.Mutex.new #[]
    let slowEntered ← IO.Promise.new
    let uncleEntered ← IO.Promise.new
    let goodStarted ← IO.Promise.new
    let ai : Proposer := fun req => do
      let n := req.task.delta.child
      mark events n "start"
      if let some cert := req.diagnostic then
        ensure (n == mid.modName && cert.kind == kind) s!"refutation escaped its parent: {cert}"
        let witness := s!"{badName} ({String.intercalate ", " (used.map toString)})"
        ensure (cert.witness == witness && cert.cause.contains (renderLeanMod proof) &&
          (!isModel || (cert.cause.contains why && cert.cause.contains (renderLeanMod model)))) s!"wrong certificate: {cert}"
        ensure (req.old == withChildIfaces before [bad, slow] && req.home.any (fun h =>
          (lookupChild h bad.modName).any (·.spec == bad))) "replan lost the current code or exact old stub"
        let notes := req.memory.filter fun (o, _) => o matches .ext _
        ensure (notes.map Prod.fst == used.map Obj.ext && notes.all (fun (_, xs) =>
          xs.length == 1 && xs.head!.contains kind) && !(reprStr req.memory).contains privateNote)
          "parent memory lost the projection or disclosed child exploration"
        let log ← eventLog events
        for sib in [slow, uncle] do
          ensure (log.contains (sib.modName, "sleep") && !log.contains (sib.modName, "awake"))
            s!"{sib.modName} was not in flight at local replan"
        return repair
      if n == top.modName then return topPlan
      if n == mid.modName then return firstPlan
      if n == bad.modName then
        if req.task.delta.newIface == good then
          goodStarted.resolve ()
          return goodPlan
        ensure (req.memory == badSeed.memory) "refuting worker lost its private seed"
        IO.wait slowEntered.result!
        IO.wait uncleEntered.result!
        return evidence
      if n == slow.modName || n == uncle.modName then
        mark events n "sleep"
        if n == slow.modName then slowEntered.resolve () else uncleEntered.resolve ()
        IO.wait goodStarted.result!
        mark events n "awake"
        return if n == slow.modName then slowPlan else unclePlan
      throw (IO.userError s!"unexpected RD child {n}")
    let start ← IO.monoMsNow
    let (v, h) ← drive ai {(task top) with baseModules := [support], allowedAncestors := some [support.modName]}
      root (cancelOwner := fun n => do mark events (q n) "abort"; goodStarted.resolve ())
    let ms := (← IO.monoMsNow) - start
    ensure (v == .ok) s!"{kind} propagated to root"
    verifyClosure [support] h
    let log ← eventLog events
    for (m, count) in [(top, 1), (uncle, 1), (mid, 2), (bad, 2), (slow, 1)] do
      ensure (log.count (m.modName, "start") == count) s!"{kind}: wrong turn count for {m.modName}"
    ensure (!(log.any (·.2 == "abort"))) "reconciliation cancelled a surviving slot"
    let some sealedMid := lookupChild h mid.modName | throw (IO.userError "missing repaired parent")
    ensure ((lookupChild sealedMid bad.modName).any (·.spec == good) &&
      sealedMid.code == withTests (withChildIfaces after [good, slow]) mid &&
      (memoryIndex sealedMid.memory)[Obj.ext good.units.head!.uname]?.any (·.any (·.contains kind)))
      "repair did not seal the revised glue, test or inherited refutation"
    IO.println s!"B  {kind} absorbed in Mid, one SlowInnocent turn and one Uncle turn ({ms} ms)"
  replanCancellationAndSalvage

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

/-- A reply naming a single draft (as `check_plan(submission="@plan")` does)
    resolves to the submission held there, including its nested drafts. -/
private def nodeReplyDrafts : IO Unit := do
  let main ← object "Gen.R.Root" "def n : Nat := 1"
  let sub ← object "Gen.R.Root.Child" "axiom k : Nat"
  let plan := s!"(submission (kind plan) (why \"draft\") (main @main) (subspecs (\"Child\" @subspec))\n  (moves {(encMove ⟨.bot,.unit (q "Gen.R.Root.n")⟩).canonical}))"
  let drafts : Lojita.Harness.DraftStore := Std.HashMap.ofList
    [("plan-draft", plan), ("main", renderLeanMod main), ("subspec", renderLeanMod sub)]
  let resolved ← IO.ofExcept (Lojita.Session.resolveNodeReply "@plan-draft" drafts)
  let .plan p subs ← IO.ofExcept (parseSubmission resolved) | throw (IO.userError "expected a plan")
  ensure (p.newMod == some main && subs == [sub]) s!"top-level draft resolution {resolved}"
  ensure ((← IO.ofExcept (Lojita.Session.resolveNodeReply "  @plan-draft\n" drafts)) == resolved) "whitespace around @draft"
  -- Fenced blocks inside the envelope draft are attached as well.
  let fenced := Std.HashMap.ofList [("plan-draft", plan.replace "@subspec" "@inner" ++
    "\n```lean inner\n" ++ renderLeanMod sub ++ "\n```"), ("main", renderLeanMod main)]
  let .plan _ subs ← IO.ofExcept (parseSubmission (← IO.ofExcept (Lojita.Session.resolveNodeReply "@plan-draft" fenced)))
    | throw (IO.userError "expected a fenced plan")
  ensure (subs == [sub]) "fenced block inside a draft envelope"
  -- A missing inner draft no longer aborts resolution: valid drafts are kept
  -- and the exact missing reference is reported.
  let partialDrafts := (drafts.insert "plan-draft" (plan.replace "@subspec" "@missing")).erase "subspec"
  let kept ← IO.ofExcept (Lojita.Session.resolveNodeReply "@plan-draft" partialDrafts)
  ensure (kept.contains "Gen.R.Root" && kept.contains "@missing") s!"partial draft resolution {kept}"
  match parseSubmission kept with
  | .error e => ensure (e == "UNRESOLVED_BLOCK: @missing") s!"expected UNRESOLVED_BLOCK: @missing, got {e}"
  | .ok _ => throw (IO.userError "accepted an unresolved draft")
  match parseSubmission "@typo" drafts with
  | .error e => ensure (e == "UNRESOLVED_BLOCK: @typo") s!"expected UNRESOLVED_BLOCK: @typo, got {e}"
  | .ok _ => throw (IO.userError "accepted an unresolved envelope draft")
  ensure ((Lojita.Session.resolveNodeReply "@typo" drafts) matches .error _) "missing envelope draft"
  -- Prose around the envelope gets an actionable diagnostic with a stable kind.
  for prose in ["Here is my plan: " ++ plan, "I think we are done.", "(kind plan)"] do
    match parseSubmission prose drafts with
    | .error e =>
      ensure (e.startsWith "INVALID_SUBMISSION: " && (e.splitOn ":").head! == "INVALID_SUBMISSION")
        s!"prose diagnostic {e}"
    | .ok _ => throw (IO.userError s!"accepted prose {prose}")
  ensure ((Lojita.Session.resolveNodeReply "I think we are done." drafts) matches .error _) "prose reply resolved"
  IO.println "6  Node replies resolve @draft envelopes, keep valid drafts and name missing ones"

private def engineRemediationTests : IO Unit := do
  -- 1. Post-seal accept errors and cancel-hook errors never lose verified seals or salvaged homes.
  do
    let root ← object "Gen.Rem.Resil" "axiom val : Nat"
    let bad ← object "Gen.Rem.Resil.Bad" "def zero : Nat := 0\naxiom bad : zero = 1\naxiom unused : Nat"
    let good ← object "Gen.Rem.Resil.Bad" "axiom good : Nat"
    let branch ← object "Gen.Rem.Resil.Branch" "axiom old : Nat"
    let revised ← object "Gen.Rem.Resil.Branch" "axiom next : Nat"
    let kept ← object "Gen.Rem.Resil.Branch.Keep" "axiom val : Nat"
    let waiter ← object "Gen.Rem.Resil.Branch.Wait" "axiom val : Nat"
    let main1 ← object "Gen.Rem.Resil"
      s!"def val : Nat := {branch.modName}.old + {bad.modName}.unused" [toString bad.modName, toString branch.modName]
    let main2 ← object "Gen.Rem.Resil"
      s!"def val : Nat := {revised.modName}.next + {good.modName}.good" [toString good.modName, toString revised.modName]
    let oldBranch ← object "Gen.Rem.Resil.Branch"
      s!"def old : Nat := {kept.modName}.val + {waiter.modName}.val" [toString kept.modName, toString waiter.modName]
    let newBranch ← object "Gen.Rem.Resil.Branch"
      s!"def next : Nat := {kept.modName}.val" [toString kept.modName]
    let keptPlan := planText (← object (toString kept.modName) "def val : Nat := 7")
    let goodPlan := planText (← object (toString good.modName) "def good : Nat := 1")
    let proof ← object "ResilEvidence" s!"theorem witness : False := Nat.zero_ne_one {bad.modName}.bad" [toString bad.modName]
    let moves : List Proarrow := [
      ⟨.ext (q "Gen.Rem.Resil.Bad.bad"), .ext (q "Gen.Rem.Resil.Bad.good")⟩,
      ⟨.ext (q "Gen.Rem.Resil.Bad.unused"), .ext (q "Gen.Rem.Resil.Bad.good")⟩,
      ⟨.ext (q "Gen.Rem.Resil.Branch.old"), .ext (q "Gen.Rem.Resil.Branch.next")⟩,
      ⟨.unit (q "Gen.Rem.Resil.val"), .unit (q "Gen.Rem.Resil.val")⟩]
    let events ← Std.Mutex.new #[]
    let keptReady ← IO.Promise.new
    let waiterEntered ← IO.Promise.new
    let waiterCancelled ← IO.Promise.new
    let ai : Proposer := fun req => do
      let n := req.task.delta.child
      mark events n "start"
      if let some cert := req.diagnostic then
        ensure (n == root.modName && cert.kind == "child_contradiction") s!"unexpected diag: {cert}"
        return planText main2 [good, revised] moves
      if n == root.modName then return planText main1 [bad, branch]
      if n == bad.modName then
        if req.task.delta.newIface == good then return goodPlan
        IO.wait keptReady.result!
        IO.wait waiterEntered.result!
        return refuteText "contradiction" proof
      if n == branch.modName then
        return if req.task.delta.newIface == revised then planText newBranch [kept] else planText oldBranch [kept, waiter]
      if n == kept.modName then return keptPlan
      if n == waiter.modName then
        waiterEntered.resolve ()
        IO.wait waiterCancelled.result!
        throw (IO.userError "waiter cancelled")
      throw (IO.userError s!"unexpected resil child {n}")
    let accept : AcceptNode := fun t _ => do
      if t.delta.child == kept.modName then keptReady.resolve ()
      throw (IO.userError s!"transient accept failure for {t.delta.child}")
    let cancel := fun n => do
      mark events (q n) "abort"
      if n == toString waiter.modName then waiterCancelled.resolve ()
      throw (IO.userError s!"transient cancel failure for {n}")
    let (v, h) ← drive ai (task root) (leaf (empty root.modName)) accept cancel
    let log ← eventLog events
    ensure (v == .ok && log.count (kept.modName, "start") == 1 &&
      log.count (branch.modName, "abort") == 1 && log.count (waiter.modName, "abort") == 1)
      s!"post-seal accept or cancel hook failure lost seal or salvage: {repr log}"
    verifyClosure [] h

  -- 2. Parallel cancellation triggers all invalidated siblings up front before joining any of them.
  do
    let root ← object "Gen.Rem.ParCancel" "axiom val : Nat"
    let bad ← object "Gen.Rem.ParCancel.Bad" "def zero : Nat := 0\naxiom bad : zero = 1\naxiom unused : Nat"
    let good ← object "Gen.Rem.ParCancel.Bad" "axiom good : Nat"
    let d1 ← object "Gen.Rem.ParCancel.Drop1" "axiom val : Nat"
    let d2 ← object "Gen.Rem.ParCancel.Drop2" "axiom val : Nat"
    let main1 ← object "Gen.Rem.ParCancel"
      s!"def val : Nat := {bad.modName}.unused + {d1.modName}.val + {d2.modName}.val"
      [toString bad.modName, toString d1.modName, toString d2.modName]
    let main2 ← object "Gen.Rem.ParCancel" s!"def val : Nat := {good.modName}.good" [toString good.modName]
    let goodPlan := planText (← object (toString good.modName) "def good : Nat := 1")
    let proof ← object "ParCancelEvidence" s!"theorem witness : False := Nat.zero_ne_one {bad.modName}.bad" [toString bad.modName]
    let moves : List Proarrow := [
      ⟨.ext (q "Gen.Rem.ParCancel.Bad.bad"), .ext (q "Gen.Rem.ParCancel.Bad.good")⟩,
      ⟨.ext (q "Gen.Rem.ParCancel.Bad.unused"), .ext (q "Gen.Rem.ParCancel.Bad.good")⟩,
      ⟨.ext d1.modName, .bot⟩, ⟨.ext d2.modName, .bot⟩,
      ⟨.unit (q "Gen.Rem.ParCancel.val"), .unit (q "Gen.Rem.ParCancel.val")⟩]
    let d1Started ← IO.Promise.new
    let d2Started ← IO.Promise.new
    let d1Cancelled ← IO.Promise.new
    let d2Cancelled ← IO.Promise.new
    let ai : Proposer := fun req => do
      let n := req.task.delta.child
      if let some cert := req.diagnostic then
        ensure (n == root.modName && cert.kind == "child_contradiction") s!"unexpected parcancel diag: {cert}"
        return planText main2 [good] moves
      if n == root.modName then return planText main1 [bad, d1, d2]
      if n == bad.modName then
        if req.task.delta.newIface == good then return goodPlan
        IO.wait d1Started.result!
        IO.wait d2Started.result!
        return refuteText "contradiction" proof
      if n == d1.modName then
        d1Started.resolve ()
        IO.wait d1Cancelled.result!
        IO.wait d2Cancelled.result!
        throw (IO.userError "d1 cancelled")
      if n == d2.modName then
        d2Started.resolve ()
        IO.wait d1Cancelled.result!
        IO.wait d2Cancelled.result!
        throw (IO.userError "d2 cancelled")
      throw (IO.userError s!"unexpected parcancel child {n}")
    let cancel := fun n => do
      if n == toString d1.modName then d1Cancelled.resolve ()
      if n == toString d2.modName then d2Cancelled.resolve ()
    let (v, h) ← drive ai (task root) (leaf (empty root.modName)) (cancelOwner := cancel)
    ensure (v == .ok) "parallel sibling cancellation did not seal"
    verifyClosure [] h

  -- 3. An eqIface-equivalent textually updated child spec survives replan and is normalized for finish.
  do
    let root ← object "Gen.Rem.EqSpec" "axiom val : Nat"
    let bad ← object "Gen.Rem.EqSpec.Bad" "def zero : Nat := 0\naxiom bad : zero = 1\naxiom unused : Nat"
    let good ← object "Gen.Rem.EqSpec.Bad" "axiom good : Nat"
    let slowV1 ← object "Gen.Rem.EqSpec.Slow" "axiom val : Nat"
    let slowV2 ← object "Gen.Rem.EqSpec.Slow" "axiom val : Id Nat"
    ensure (slowV1 != slowV2) "expected textually distinct eqIface specs"
    let main1 ← object "Gen.Rem.EqSpec"
      s!"def val : Nat := {slowV1.modName}.val + {bad.modName}.unused" [toString bad.modName, toString slowV1.modName]
    let main2 ← object "Gen.Rem.EqSpec"
      s!"def val : Nat := Nat.add {slowV2.modName}.val {good.modName}.good" [toString good.modName, toString slowV2.modName]
    let slowPlan := planText (← object (toString slowV1.modName) "def val : Nat := 42")
    let goodPlan := planText (← object (toString good.modName) "def good : Nat := 1")
    let proof ← object "EqSpecEvidence" s!"theorem witness : False := Nat.zero_ne_one {bad.modName}.bad" [toString bad.modName]
    let moves : List Proarrow := [
      ⟨.ext (q "Gen.Rem.EqSpec.Bad.bad"), .ext (q "Gen.Rem.EqSpec.Bad.good")⟩,
      ⟨.ext (q "Gen.Rem.EqSpec.Bad.unused"), .ext (q "Gen.Rem.EqSpec.Bad.good")⟩,
      ⟨.unit (q "Gen.Rem.EqSpec.val"), .unit (q "Gen.Rem.EqSpec.val")⟩]
    let events ← Std.Mutex.new #[]
    let slowEntered ← IO.Promise.new
    let goodStarted ← IO.Promise.new
    let ai : Proposer := fun req => do
      let n := req.task.delta.child
      mark events n "start"
      if let some cert := req.diagnostic then
        ensure (n == root.modName && cert.kind == "child_contradiction") s!"unexpected eqspec diag: {cert}"
        return planText main2 [good, slowV2] moves
      if n == root.modName then return planText main1 [bad, slowV1]
      if n == bad.modName then
        if req.task.delta.newIface == good then
          goodStarted.resolve ()
          return goodPlan
        IO.wait slowEntered.result!
        return refuteText "contradiction" proof
      if n == slowV1.modName then
        slowEntered.resolve ()
        IO.wait goodStarted.result!
        return slowPlan
      throw (IO.userError s!"unexpected eqspec child {n}")
    let (v, h) ← drive ai (task root) (leaf (empty root.modName)) (cancelOwner := fun n => do
      mark events (q n) "abort"
      goodStarted.resolve ())
    let log ← eventLog events
    ensure (v == .ok && log.count (slowV1.modName, "start") == 1 && !(log.any (·.2 == "abort")) &&
      (lookupChild h slowV2.modName).any (·.spec == slowV2))
      s!"eqIface-updated sibling was restarted or kept stale spec: {repr log}"
    verifyClosure [] h

  -- 4. A child with horizontal sub-transports survives a parent replan uninterrupted.
  do
    let oldLeafSpec ← object "Gen.T0.RemH.Branch.Leaf" "axiom val : Nat"
    let oldLeafImpl ← object "Gen.T0.RemH.Branch.Leaf" "def val : Nat := 7"
    let oldBranchSpec ← object "Gen.T0.RemH.Branch" "axiom val : Nat"
    let oldBranchCode ← object "Gen.T0.RemH.Branch" "def val : Nat := Gen.T0.RemH.Branch.Leaf.val" [toString oldLeafSpec.modName]
    let oldBranchHome := Frozen.frozen (withChildIfaces oldBranchCode [oldLeafSpec]) [] oldBranchSpec
      [(toString oldLeafSpec.modName, Frozen.frozen oldLeafImpl [] oldLeafSpec [])]
    let oldRootSpec ← object "Gen.T0.RemH" "axiom val : Nat"
    let oldRootCode ← object "Gen.T0.RemH" "def val : Nat := Gen.T0.RemH.Branch.val" [toString oldBranchSpec.modName]
    let oldRootHome := Frozen.frozen (withChildIfaces oldRootCode [oldBranchSpec]) [] oldRootSpec
      [(toString oldBranchSpec.modName, oldBranchHome)]

    let root ← object "Gen.T1.RemH" "axiom val : Nat"
    let branch ← object "Gen.T1.RemH.Branch" "axiom val : Nat"
    let newLeaf := q "Gen.T1.RemH.Branch.Leaf"
    let bad ← object "Gen.T1.RemH.Bad" "def zero : Nat := 0\naxiom bad : zero = 1\naxiom unused : Nat"
    let good ← object "Gen.T1.RemH.Bad" "axiom good : Nat"
    let main1 ← object "Gen.T1.RemH"
      s!"def val : Nat := {branch.modName}.val + {bad.modName}.unused" [toString branch.modName, toString bad.modName]
    let main2 ← object "Gen.T1.RemH"
      s!"def val : Nat := {branch.modName}.val + {good.modName}.good" [toString branch.modName, toString good.modName]
    let branchImpl ← object (toString branch.modName) s!"def val : Nat := {newLeaf}.val" [toString newLeaf]
    let goodPlan := planText (← object (toString good.modName) "def good : Nat := 1")
    let proof ← object "RemHEvidence" s!"theorem witness : False := Nat.zero_ne_one {bad.modName}.bad" [toString bad.modName]
    let sub := TransportSpec.transportSpecTree oldBranchSpec.modName branch.modName [.keepChild oldLeafSpec.modName newLeaf] []
    let ts := TransportSpec.transportSpecTree oldRootSpec.modName root.modName
      [.moveChildren [oldBranchSpec.modName] [branch.modName] [sub]] []
    let moves : List Proarrow := [
      ⟨.ext (q "Gen.T1.RemH.Bad.bad"), .ext (q "Gen.T1.RemH.Bad.good")⟩,
      ⟨.ext (q "Gen.T1.RemH.Bad.unused"), .ext (q "Gen.T1.RemH.Bad.good")⟩,
      ⟨.unit (q "Gen.T1.RemH.val"), .unit (q "Gen.T1.RemH.val")⟩]
    let events ← Std.Mutex.new #[]
    let branchEntered ← IO.Promise.new
    let goodStarted ← IO.Promise.new
    let ai : Proposer := fun req => do
      let n := req.task.delta.child
      mark events n "start"
      if let some cert := req.diagnostic then
        ensure (n == root.modName && cert.kind == "child_contradiction") s!"unexpected remh diag: {cert}"
        return planText main2 [good] moves
      if n == root.modName then return planText main1 [branch, bad]
      if n == bad.modName then
        if req.task.delta.newIface == good then
          goodStarted.resolve ()
          return goodPlan
        IO.wait branchEntered.result!
        return refuteText "contradiction" proof
      if n == branch.modName then
        ensure (!req.task.transports.isEmpty) "branch missing horizontal sub-transport"
        branchEntered.resolve ()
        IO.wait goodStarted.result!
        return planText branchImpl
      throw (IO.userError s!"unexpected remh child {n}")
    let (v, h) ← drive ai {(task root) with transports := [(oldRootHome, ts)]} (leaf (empty root.modName))
      (cancelOwner := fun n => do mark events (q n) "abort"; goodStarted.resolve ())
    let log ← eventLog events
    ensure (v == .ok && log.count (branch.modName, "start") == 1 && log.count (newLeaf, "start") == 0 &&
      !(log.any (·.2 == "abort"))) s!"horizontal sub-transport child did not survive replan: {repr log}"
    verifyClosure [] h

  -- 5. Salvaged grandchildren are preserved in freezeVerifiedKids on liftObstruction and written to refs/partial.
  do
    let badBase ← object "Gen.T0.Salv.Doc" "def singlePass (_ : Nat) := 0\ntheorem badSinglePass : singlePass 1 = 0 := rfl"
    let lower ← object "Gen.T0.Salv.Root" "def version := 1" [toString badBase.modName]
    let lowerRoot := withChildIfaces lower [badBase]
    let upper ← object "Gen.T1.Salv" "axiom value : Nat"
    let branch ← object "Gen.T1.Salv.Branch" "axiom value : Nat"
    let sibling ← object "Gen.T1.Salv.Sibling" "axiom value : Nat"
    let keep ← object "Gen.T1.Salv.Branch.Keep" "axiom value : Nat"
    let blocker ← object "Gen.T1.Salv.Branch.Blocker"
      s!"axiom parse : Nat → Nat\naxiom law : parse 1 = {badBase.modName}.singlePass 1\naxiom atOne : parse 1 = 1"
      [toString badBase.modName]
    let main ← object (toString upper.modName)
      s!"def value : Nat := {branch.modName}.value + {sibling.modName}.value" [toString branch.modName, toString sibling.modName]
    let branchCode ← object (toString branch.modName)
      s!"def value : Nat := {keep.modName}.value + {blocker.modName}.parse 1" [toString keep.modName, toString blocker.modName]
    let keepPlan := planText (← object (toString keep.modName) "def value : Nat := 3")
    let sibPlan := planText (← object (toString sibling.modName) "def value : Nat := 4")
    let witness ← object "SalvEvidence"
      s!"theorem obstruction : False := Nat.one_ne_zero ({blocker.modName}.atOne.symm.trans ({blocker.modName}.law.trans {badBase.modName}.badSinglePass))"
      [toString badBase.modName, toString blocker.modName]
    let ls := LiftSpec.liftSpecTree lowerRoot.modName upper.modName [.mkChildLift badBase.modName branch.modName none] []
    let t := {(task upper) with baseModules := [badBase, lowerRoot], maybeLift := some (lowerRoot, ls)}
    let ai : Proposer := fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      let n := req.task.delta.child
      if n == upper.modName then return planText main [branch, sibling]
      if n == branch.modName then return planText branchCode [keep, blocker]
      if n == keep.modName then return keepPlan
      if n == sibling.modName then return sibPlan
      if n == blocker.modName then return refuteText "refute-lift" witness
      throw (IO.userError s!"unexpected salv child {n}")
    let (v, partialHome) ← drive ai t (leaf (empty upper.modName))
    ensure (v matches .liftObstruction ..) s!"expected liftObstruction, got {repr v}"
    let names := partialHome.children.map Prod.fst
    ensure (names == [toString sibling.modName, toString keep.modName])
      s!"expected both verified sibling and salvaged grandchild in partial home, got {names}"
    IO.FS.withTempDir fun ws => do
      Lojita.Session.initWorkspace ws
      let baseHome := Frozen.frozen lowerRoot [] lowerRoot [(toString badBase.modName, Frozen.frozen badBase [] badBase [])]
      discard <| Lojita.Session.publishTree ws "T0" "base" [] [] .ok baseHome
      discard <| Lojita.Session.publishTree ws "T1" "obstructed with salvage" ["T0"] [] v partialHome
      let some key ← readRef (ws / "store") .partial "T1" | throw (IO.userError "missing partial ref")
      let commit ← getObject (ws / "store") .commit key
      let reloaded ← loadFrozen (ws / "store") commit.rootHome
      ensure (reloaded.children.map Prod.fst == [toString keep.modName, toString sibling.modName] &&
        (lookupChild reloaded keep.modName).isSome && (lookupChild reloaded sibling.modName).isSome)
        "refs/partial lost salvaged grandchild subtree"
      -- Verifier #1: isNestedDescendant distinguishes direct/epoch slots from salvaged grandchildren;
      -- prepareSpec (in-place and cross-tree via partialSource) does NOT trigger unaccountedOldChild
      -- on salvaged grandchildren, and re-driving reuses BOTH Sibling and salvaged Branch.Keep in 0 turns!
      ensure (!isNestedDescendant (q "Gen.T0.Root") (q "Gen.T0.Doc") &&
        isNestedDescendant (q "Gen.T0.Root") (q "Gen.T0.Doc.Keep") &&
        !isNestedDescendant upper.modName sibling.modName &&
        isNestedDescendant upper.modName keep.modName)
        "isNestedDescendant misclassified direct or epoch child"
      let some ps ← Lojita.Session.partialSource ws upper.modName | throw (IO.userError "missing partialSource")
      ensure (ps.children.map Prod.fst == [toString sibling.modName] &&
        ps.code.imports.map (·.imod) == [sibling.modName])
        s!"partialSource leaked salvaged grandchild as direct slot: {ps.children.map Prod.fst}"
      let inPlaceTs := (encodeTransportSpec (.transportSpecTree upper.modName upper.modName
        [.keepChild sibling.modName sibling.modName] [])).canonical
      discard <| Lojita.Session.prepareSpec ws "T1" (renderLeanMod upper) ["T0"]
        (some (encodeLiftSpec ls).canonical) (some inPlaceTs)
      let peerSpec ← object "Gen.T1b.Salv" "axiom value : Nat"
      let peerSib := q "Gen.T1b.Salv.Sibling"
      let crossTs := (encodeTransportSpec (.transportSpecTree upper.modName peerSpec.modName
        [.keepChild sibling.modName peerSib] [])).canonical
      let crossPrep ← Lojita.Session.prepareSpec ws "T1b" (renderLeanMod peerSpec) [] none (some crossTs)
      let peerDraft ← object "Gen.T1b.Salv" s!"def value : Nat := {peerSib}.value" [toString peerSib]
      let crossRep ← planPreview crossPrep.task crossPrep.home (birthPlan peerDraft)
      ensure crossRep.certificate.isNone s!"cross-tree partialSource transport rejected: {repr crossRep}"
      let fixedBase ← object "Gen.T0.Salv.Doc" "def singlePass (n : Nat) := n"
      let fixedRoot := withChildIfaces lower [fixedBase]
      let fixedT0 := Frozen.frozen fixedRoot [] fixedRoot [(toString fixedBase.modName, Frozen.frozen fixedBase [] fixedBase [])]
      discard <| Lojita.Session.publishTree ws "T0" "fixed base" [] [] .ok fixedT0
      let blockerImpl ← object (toString blocker.modName)
        s!"def parse (n : Nat) := n\ntheorem law : parse 1 = {fixedBase.modName}.singlePass 1 := rfl\ntheorem atOne : parse 1 = 1 := rfl"
        [toString fixedBase.modName]
      let redrivePrep ← Lojita.Session.prepareSpec ws "T1" (renderLeanMod upper) ["T0"]
        (some (encodeLiftSpec ls).canonical) none
      let redriveEvents ← Std.Mutex.new #[]
      let redriveAI : Proposer := fun req => do
        if let some cert := req.diagnostic then throw (IO.userError (toString cert))
        let n := req.task.delta.child
        mark redriveEvents n "start"
        if n == upper.modName then return planText main [branch, sibling]
        if n == branch.modName then return planText branchCode [keep, blocker]
        if n == blocker.modName then return planText blockerImpl
        throw (IO.userError s!"salvaged child or grandchild should reuse in 0 turns: {n}")
      let (v2, sealed2) ← drive redriveAI {redrivePrep.task with allowedAncestors := none} redrivePrep.home
      let rlog ← eventLog redriveEvents
      ensure (v2 == .ok && rlog.count (sibling.modName, "start") == 0 && rlog.count (keep.modName, "start") == 0 &&
        rlog.count (upper.modName, "start") == 1 && rlog.count (branch.modName, "start") == 1 &&
        rlog.count (blocker.modName, "start") == 1)
        s!"re-drive failed to reuse salvaged grandchild in 0 turns: {repr rlog}"
      verifyClosure [fixedBase, fixedRoot] sealed2
  IO.println "D  Post-seal accept/cancel resilience, parallel abort, eqIface normalization, horizontal survival, and liftObstruction salvage passed"

open Lojita.Session in
private def eqIfaceReuseAndOldStubsRegression : IO Unit := do
  -- Reproduces the live Gen.T2.Gron / Gen.T2.Gron.Input 3-drive bug:
  -- Child imports LojitaCtx.World + opens LojitaCtx LojitaCtx.Terminal LojitaCtx.World + uses Bytes;
  -- Parent imports only LojitaCtx.Cli (not LojitaCtx.World);
  -- Drive #2 alpha-renames Input's constructor binders (reused in 0 turns);
  -- Drive #3 re-drives both with unchanged T1 (oldBaseModules := none) and tweaked T1 (oldBaseModules := some ...).
  let t1Name := "Gen.T1.GronBase"
  let t2Name := "Gen.T2.Gron"
  let inputName := t2Name ++ ".Input"
  let t1Spec ← object t1Name "axiom tag : Nat"
  let t1V1 ← object t1Name "def tag : Nat := 1"
  let t1V2 ← object t1Name "def tag : Nat := 2"
  let t2Spec ← object t2Name "open LojitaCtx.Cli\naxiom run : Nat" ["LojitaCtx.Cli"]
  let inputSpec1 ← object inputName
    "open LojitaCtx LojitaCtx.Terminal LojitaCtx.World\ninductive Source where\n  | tls (sni : String) (skipVerify : Bool) (connect : Bytes)\naxiom handle : Source → Nat"
    ["LojitaCtx.World"]
  let inputSpec2 ← object inputName
    "open LojitaCtx LojitaCtx.Terminal LojitaCtx.World\ninductive Source where\n  | tls (sni : String) (insecure : Bool) (tunnel : Bytes)\naxiom handle : Source → Nat"
    ["LojitaCtx.World"]
  ensure (inputSpec1 != inputSpec2) "expected alpha-renamed specs to be textually distinct"
  let inputImpl ← object inputName
    "open LojitaCtx LojitaCtx.Terminal LojitaCtx.World\ninductive Source where\n  | tls (sni : String) (skipVerify : Bool) (connect : Bytes)\ndef handle : Source → Nat\n  | .tls _ _ bs => bs.length"
    ["LojitaCtx.World"]
  let mkParent := fun (extra : Nat) => object t2Name
    s!"open LojitaCtx.Cli\ndef run : Nat := {inputName}.handle ({inputName}.Source.tls \"host\" true []) + {t1Name}.tag + {extra}"
    ["LojitaCtx.Cli", t1Name, inputName]
  let parent1 ← mkParent 0
  let parent2 ← mkParent 1
  let parent3 ← mkParent 2
  let parent4 ← mkParent 3
  let liftSrc := (encodeLiftSpec (.liftSpecTree (q t1Name) (q t2Name) [] [])).canonical
  let runMove : List Proarrow := [⟨.unit (q (t2Name ++ ".run")), .unit (q (t2Name ++ ".run"))⟩]

  IO.FS.withTempDir fun ws => do
    initWorkspace ws
    -- Seal T1 v1
    discard <| publishTree ws "T1" "t1 v1" [] [] .ok (Frozen.frozen t1V1 [] t1Spec [])
    let t1Closure1 ← loadCurrentClosure ws ["T1"]

    -- T2 Drive #1: seals Gron and Gron.Input with spec v1 (skipVerify / connect).
    let prep1 ← prepareSpec ws "T2" (renderLeanMod t2Spec) ["T1"] (some liftSrc) none
    ensure (prep1.task.oldBaseModules.isNone && prep1.task.otherChildHistory.isNone)
      "fresh T2 should have no historical bases"
    let (v1, sealed1) ← drive (fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      if req.task.delta.child == q t2Name then return planText parent1 [inputSpec1]
      if req.task.delta.child == q inputName then return planText inputImpl
      throw (IO.userError s!"unexpected drive #1 node {req.task.delta.child}")) prep1.task prep1.home
    ensure (v1 == .ok) "T2 drive #1 did not seal"
    verifyClosure t1Closure1.modules sealed1
    discard <| publishTree ws "T2" "t2 drive 1" ["T1"] t1Closure1.directTips .ok sealed1

    -- T2 Drive #2 (T1 unchanged): alpha-renamed Input spec v2 (insecure / tunnel) reuses Input in 0 turns
    -- and normalizes h.spec to inputSpec2; oldBaseModules is none because T1 did not change.
    let prep2 ← prepareSpec ws "T2" (renderLeanMod t2Spec) ["T1"] (some liftSrc) none
    ensure (prep2.task.oldBaseModules.isNone && prep2.task.otherChildHistory.isNone)
      "Bug A: unchanged T1 populated oldBaseModules or otherChildHistory on T2 drive #2"
    let d2Events ← Std.Mutex.new #[]
    let (v2, sealed2) ← drive (fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      mark d2Events req.task.delta.child "start"
      if req.task.delta.child == q t2Name then return planText parent2 [inputSpec2] runMove
      throw (IO.userError s!"Input should reuse in 0 turns on drive #2: {req.task.delta.child}")) prep2.task prep2.home
    let d2Log ← eventLog d2Events
    ensure (v2 == .ok && d2Log.count (q inputName, "start") == 0)
      s!"T2 drive #2 did not reuse Input in 0 turns: {repr d2Log}"
    ensure ((lookupChild sealed2 (q inputName)).any (·.spec == inputSpec2))
      "Bug C: reusableHome did not normalize reused child's root spec to alpha-renamed inputSpec2"
    verifyClosure t1Closure1.modules sealed2
    discard <| publishTree ws "T2" "t2 drive 2" ["T1"] t1Closure1.directTips .ok sealed2

    -- Also verify partial commit on unchanged T1 keeps oldBaseModules == none and otherChildHistory == none.
    let dummyObs ← object "Gen.T2.DummyObs" "theorem t : True := trivial"
    let partialSameBase := Frozen.frozen sealed2.code [] t2Spec [(inputName, (lookupChild sealed2 (q inputName)).get!)]
    discard <| publishTree ws "T2" "partial unchanged base" ["T1"] t1Closure1.directTips
      (.liftObstruction "partial" [q (t1Name ++ ".tag")] dummyObs) partialSameBase
    let initUnchanged ← initialHomeWithBases ws "T2" t2Spec (some t1Closure1.modules)
    ensure (initUnchanged.oldBaseModules.isNone && initUnchanged.otherChildHistory.isNone)
      "Bug A: partial with identical vertical bases populated oldBaseModules or otherChildHistory"
    -- Clear partial by re-publishing drive #2 sealed home before drive #3.
    discard <| publishTree ws "T2" "t2 drive 2 restored" ["T1"] t1Closure1.directTips .ok sealed2

    -- T2 Drive #3a (T1 still unchanged): oldBaseModules == none, Input reuses in 0 turns.
    let prep3a ← prepareSpec ws "T2" (renderLeanMod t2Spec) ["T1"] (some liftSrc) none
    ensure prep3a.task.oldBaseModules.isNone "Bug A: unchanged T1 populated oldBaseModules on T2 drive #3a"
    let (v3a, sealed3a) ← drive (fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      if req.task.delta.child == q t2Name then return planText parent3 [inputSpec2] runMove
      throw (IO.userError s!"Input should reuse in 0 turns on drive #3a: {req.task.delta.child}")) prep3a.task prep3a.home
    ensure (v3a == .ok) "T2 drive #3a failed"
    verifyClosure t1Closure1.modules sealed3a

    -- T2 Drive #3b (T1 tweaked to v2): oldBaseModules == some [t1V1], elaborates cleanly and seals.
    discard <| publishTree ws "T1" "t1 v2" [] [] .ok (Frozen.frozen t1V2 [] t1Spec [])
    let t1Closure2 ← loadCurrentClosure ws ["T1"]
    let prep3b ← prepareSpec ws "T2" (renderLeanMod t2Spec) ["T1"] (some liftSrc) none
    ensure (prep3b.task.oldBaseModules.any (· == [t1V1]))
      "Bug A: tweaked T1 did not pin historical T1 v1 in oldBaseModules"
    let (v3b, sealed3b) ← drive (fun req => do
      if let some cert := req.diagnostic then throw (IO.userError (toString cert))
      if req.task.delta.child == q t2Name then return planText parent4 [inputSpec2] runMove
      throw (IO.userError s!"Input should reuse in 0 turns on drive #3b: {req.task.delta.child}")) prep3b.task prep3b.home
    ensure (v3b == .ok) "T2 drive #3b with pinned historical T1 v1 failed"
    verifyClosure t1Closure2.modules sealed3b

  -- Direct Bug B (oldStubs) tests simulating pre-fix poisoned homes where saved Input still has
  -- spec v1 (skipVerify/connect) while old.code.imports has spec v2 (insecure/tunnel), plus
  -- incompatible-import and missing-saved fallback paths.
  let poisonedCode := withChildIfaces parent2 [inputSpec2]
  let oldChildV1 := Frozen.frozen inputImpl [] inputSpec1 []
  let poisonedHome := Frozen.frozen poisonedCode [] t2Spec [(inputName, oldChildV1)]
  let plan3 : Plan := {why := "edit run", newMod := some parent3, moves := runMove}
  let baseTask : NodeTask := {(task t2Spec) with baseModules := [t1V2]}
  -- B1: candidateStub preserves s.imports + s.opens when s.units != i.assumes, both pinned and unpinned.
  for pinned in [none, some [t1V1]] do
    let rep ← planPreview {baseTask with oldBaseModules := pinned} poisonedHome plan3 [inputSpec2]
    ensure rep.certificate.isNone
      s!"Bug B (candidateStub, pinned={pinned.isSome}) failed historical elaboration: {repr rep}"
  -- B2: Verify old.code actually elaborated semantically (Bytes resolved, not Sort ?u) by checking
  -- that a syntactically-blind tactic dependent on `run` triggers frontier_incomplete.
  let parentWithDep ← object t2Name
    s!"open LojitaCtx.Cli\ndef run : Nat := {inputName}.handle ({inputName}.Source.tls \"host\" true []) + {t1Name}.tag\ntheorem dep : run = run := by first | exact rfl | trivial"
    ["LojitaCtx.Cli", t1Name, inputName]
  let blindCode := withChildIfaces parentWithDep [inputSpec2]
  let blindCode := {blindCode with units := blindCode.units.map fun u => {u with synRefs := []}}
  let blindHome := Frozen.frozen blindCode [] t2Spec [(inputName, oldChildV1)]
  let parent3Changed ← object t2Name
    s!"open LojitaCtx.Cli\ndef run : Bool := true" ["LojitaCtx.Cli"]
  let badSpecBool ← object t2Name "open LojitaCtx.Cli\naxiom run : Bool" ["LojitaCtx.Cli"]
  let dropInputPlan : Plan := {
    why := "change run type", newMod := some parent3Changed
    moves := [⟨.ext (q inputName), .bot⟩, ⟨.ext (q t1Name), .bot⟩, ⟨.unit (q (t2Name ++ ".run")), .unit (q (t2Name ++ ".run"))⟩]}
  let depRep ← planPreview {(task badSpecBool) with baseModules := [t1V2], oldBaseModules := some [t1V1]}
    blindHome dropInputPlan []
  ensure (depRep.certificate.any (·.kind == "frontier_incomplete") &&
      depRep.frontier == [(encObj (.unit (q (t2Name ++ ".dep")))).canonical])
    s!"Bug B semantic frontier check failed (expected frontier_incomplete on dep): {repr depRep}"
  -- B3: General fallback when saved child has an incompatible base import (not in histNames):
  -- filters incompatible import + opensAfterRemoval + contextHintsForRefs, no Sort ?u / historical_elaboration_failed.
  let compatBadBase ← object "Gen.T1.GoneBase" "def z : Nat := 0"
  let incompatSpec ← object inputName
    s!"open LojitaCtx LojitaCtx.Terminal LojitaCtx.World {compatBadBase.modName}\ninductive Source where\n  | tls (sni : String) (skipVerify : Bool) (connect : Bytes)\naxiom handle : Source → Nat\naxiom extra : Nat"
    ["LojitaCtx.World", toString compatBadBase.modName]
  let incompatHome := Frozen.frozen poisonedCode [] t2Spec [(inputName, Frozen.frozen inputImpl [] incompatSpec [])]
  let repIncompat ← planPreview {baseTask with oldBaseModules := some [t1V1]} incompatHome plan3 [inputSpec2]
  ensure repIncompat.certificate.isNone
    s!"Bug B (incompatible saved import fallback) failed: {repr repIncompat}"
  -- B4: General fallback when saved child is completely absent (old.children = []):
  -- recovers LojitaCtx.Terminal/World imports and opens purely from i.assumes synRefs!
  let noSavedHome := Frozen.frozen poisonedCode [] t2Spec []
  let repNoSaved ← planPreview {baseTask with oldBaseModules := some [t1V1]} noSavedHome plan3 [inputSpec2]
  ensure repNoSaved.certificate.isNone
    s!"Bug B (missing saved child synRefs fallback) failed: {repr repNoSaved}"
  IO.println "E  eqIface 0-turn spec normalization, unchanged-base oldBaseModules=none, and oldStubs LojitaCtx recovery passed"

def run : IO Unit := IO.FS.withTempDir fun dir => do
  merkle dir
  preload
  try
    checkPlanFrontier
    polyAndLift
    narrowing
    splitChildren
    deepKeptLift
    inPlaceSquare
    historicalFrontier
    obstruction dir
    countermodels
    preview dir
    nodeReplyDrafts
    concurrentTreeSpeedupAndDeterminism dir
    reverseDialecticaLocalAbsorptionAndInFlightSurvival
    orderIndependentObstructionHarvest dir
    engineRemediationTests
    eqIfaceReuseAndOldStubsRegression
  finally close

end Test.S3Harness

def main : IO Unit := Test.S3Harness.run
