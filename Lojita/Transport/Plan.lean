import Lojita.Kernel.Driver

namespace Lojita.Transport
open Lojita.Kernel Lojita.Store

structure Proarrow where
  src : Obj
  tgt : Obj
  deriving BEq, Hashable, Repr

abbrev Memory := List (Obj × List String)

structure SpecDelta where
  child : QName
  oldIface : List SynUnit
  newIface : LeanMod
  deriving Inhabited

structure Plan where
  why : String
  origin : Option QName := none
  newMod : Option LeanMod := none
  moves : List Proarrow := []
  deriving BEq, Repr, Inhabited

def isSrc (p : Plan) (o : Obj) := p.moves.any (·.src == o)

def distinct {α : Type} [BEq α] [Hashable α] (xs : List α) : List α := Id.run do
  let mut seen : Std.HashSet α := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out.toList

def qualified (s : String) : QName := ⟨s.splitOn "."⟩

def under (parent name : QName) := parent.segments.isPrefixOf name.segments

def renameQ (a b q : QName) := QName.ofName (q.toLeanName.replacePrefix a.toLeanName b.toLeanName)

private def draftAt (p : Plan) (old : LeanMod) := p.newMod.map fun m =>
  requalify (p.origin.getD m.modName) old.modName m

private def byUnit (us : List SynUnit) : Std.HashMap QName SynUnit :=
  Std.HashMap.ofList (us.map fun u => (u.uname, u))

def externalUnits (m : LeanMod) := m.imports.flatMap (·.assumes)

private def moveSets (p : Plan) :=
  (Std.HashSet.ofList (p.moves.map (·.src)), Std.HashSet.ofList (p.moves.map (·.tgt)))

private def renames (p : Plan) : Std.HashMap QName QName := Id.run do
  let mut targets : Std.HashMap Obj (List Obj) := {}
  for a in p.moves do targets := targets.alter a.src (fun os => some (a.tgt :: os.getD []))
  let mut names := {}
  for (s, ts) in targets do
    match s, ts with
    | .unit a, [.unit b] | .ext a, [.ext b] => if a != b then names := names.insert a b
    | _, _ => pure ()
  return names

/-- Drafts and retained declarations may reference one another. Keep the
    splice order when it already elaborates and move prerequisites ahead of
    their first user otherwise. Cycles stay visible to the Lean elaborator. -/
def orderUnits (modName : QName) (units : List SynUnit) : List SynUnit := Id.run do
  let us := units.toArray
  let mut names : Std.HashMap QName Nat := {}
  for u in us, i in [:us.size] do
    for q in u.definedNames do names := names.insert q i
  let mut edges := #[]
  let mut inOrder := true
  for u in us, i in [:us.size] do
    let mut deps := #[]
    for r in u.synRefs do
      let some j := names[r]? <|> names[QName.mk (modName.segments ++ r.segments)]? | continue
      if i == j then continue
      deps := deps.push j
      if i < j then inOrder := false
    edges := edges.push deps
  if inOrder then return units
  let mut visited : Std.HashSet Nat := {}
  let mut emitted : Std.HashSet Nat := {}
  let mut out := #[]
  for i in [:us.size] do
    let mut pending := [(i,false)]
    while let (j,exit) :: rest := pending do
      pending := rest
      if emitted.contains j then continue
      if exit then
        emitted := emitted.insert j
        out := out.push us[j]!
      else
        if visited.contains j then return units
        visited := visited.insert j
        pending := edges[j]!.foldr (fun d ds => (d,false) :: ds) ((j,true) :: pending)
  return out.toList

/-- Splice at the first consumed declaration. Child imports disappear when
    every exposed endpoint is consumed or redirected. -/
def apply (p : Plan) (old : LeanMod) : LeanMod := Id.run do
  let draft := (draftAt p old).getD ⟨old.modName, [], [], []⟩
  let (src, tgt) := moveSets p
  let additions := draft.units.filter fun u => tgt.contains (.unit u.uname)
  let retainedCode := renameUnitRefs old (renames p)
  let replacedUnits := Std.HashSet.ofList (additions.map (·.uname))
  let consumed := fun (u : SynUnit) => src.contains (.unit u.uname) &&
    (replacedUnits.contains u.uname || !tgt.contains (.unit u.uname))
  let (before, rest) := retainedCode.units.span (!consumed ·)
  let imports := Std.HashMap.ofList (old.imports.map fun i => (i.imod, i))
  let replaced := Std.HashSet.ofList (draft.imports.map (·.imod))
  let mut targetedSlots : Std.HashSet QName := {}
  for a in p.moves do
    if let .ext q := a.tgt then
      let mut n := q.toLeanName
      while !n.isAnonymous do
        let slot := QName.ofName n
        if imports.contains slot then targetedSlots := targetedSlots.insert slot
        n := n.getPrefix
  let retained := old.imports.filter fun i => !replaced.contains i.imod &&
    (targetedSlots.contains i.imod || (!src.contains (.ext i.imod) &&
      (i.assumes.isEmpty || !i.assumes.all fun u => src.contains (.ext u.uname))))
  let supplied := draft.imports.map fun i =>
    if i.assumes.isEmpty then imports[i.imod]?.getD i else i
  let imports := retained ++ supplied
  let active := Std.HashSet.ofList (imports.map (·.imod))
  let dropped := old.imports.filterMap fun i => if active.contains i.imod then none else some i.imod
  let spliced := before ++ additions ++ rest.filter (!consumed ·)
  return {old with
    units := if additions.isEmpty then spliced else orderUnits old.modName spliced
    opens := distinct (opensAfterRemoval old dropped ++ draft.opens), imports}

private def sigTokens (u : SynUnit) (rs : Std.HashMap QName QName) :=
  let resolve := fun (word : String) => Id.run do
    let q := qualified word
    let refs := u.synRefs.filter fun r => q.segments.isSuffixOf r.segments
    let r := if let [r] := refs then r else q
    return toString ((renamedRef? rs r).getD r)
  -- The first two tokens identify the declaration command and its binder.
  -- References in the implementation body do not contribute to the signature.
  (u.sigSlice.splitOn "\n").map fun line => ((line.splitOn " ").drop 2).map resolve

private def kernelSignature (a b : Snapshot) (u v : SynUnit) (rs : Std.HashMap QName QName) : Bool :=
  -- Like the object parser, this decision uses Lean's local caches. Its only
  -- inputs are the checked snapshots and the move. A conversion timeout
  -- conservatively leaves the dependent on the frontier.
  let ctx : Lean.Core.Context := {
    fileName := "<signature>", fileMap := default
    options := ({} : Lean.Options).set `maxHeartbeats (200000 : Nat)}
  (unsafe unsafeIO (compareTypes.run'.toIO' ctx {env := b.env})).toOption.getD false
where
  compareTypes : Lean.MetaM Bool := do
    if u.definedNames.length != v.definedNames.length then return false
    let rename := if rs.isEmpty then id else fun n =>
      ((renamedRef? rs (QName.ofName n)).map QName.toLeanName).getD n
    -- An identical imported image already gives its constants the same meaning
    -- on both sides. A move may still rename a reference inside that image.
    let shared := if rs.isEmpty then Lean.NameSet.ofList (a.versions.toList.filterMap fun (n, ver) =>
      if b.versions.find? n == some ver then some n else none) else {}
    let unshared (s : Snapshot) (n : Lean.Name) := s.owners.contains n &&
      !shared.contains ((moduleOf? s.env n).getD s.env.mainModule)
    -- Keep the candidate realization of an old axiom symbolic on both sides.
    let assumptions := Lean.NameSet.ofList (a.axioms.toList.map rename)
    for (x,y) in u.definedNames.zip v.definedNames do
      let some old := a.env.find? x.toLeanName | return false
      let some cand := b.env.find? y.toLeanName | return false
      if old.numLevelParams != cand.numLevelParams then return false
      let oldTy ← a.mapConstants old.type (unshared a) rename
      let newTy ← b.mapConstants (cand.instantiateTypeLevelParams (old.levelParams.map Lean.Level.param))
        (fun n => unshared b n && !assumptions.contains n) id
      unless ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq oldTy newTy) do return false
    return true

private structure PlanIndex where
  locals : Std.HashMap QName SynUnit
  externals : Std.HashMap QName SynUnit
  imports : Std.HashMap QName ImportSpec
  owners : Std.HashMap QName Obj

private def indexMod (m : LeanMod) (includeOwners := true) : PlanIndex := Id.run do
  let ext := externalUnits m
  let imports := Std.HashMap.ofList (m.imports.map fun i => (i.imod,i))
  let index : PlanIndex := ⟨byUnit m.units, byUnit ext, imports, {}⟩
  unless includeOwners do return index
  let mut owners := {}
  for u in m.units do
    for r in u.synRefs do
      let mut n := r.toLeanName
      while !n.isAnonymous do
        if let some i := imports[QName.ofName n]? then
          if i.assumes.isEmpty then owners := owners.insert r (.ext r)
          break
        n := n.getPrefix
  for u in ext do
    for q in u.definedNames do owners := owners.insert q (.ext u.uname)
  for u in m.units do
    for q in u.definedNames do owners := owners.insert q (.unit u.uname)
  return {index with owners}

private def preserved (old cand : PlanIndex) (rs : Std.HashMap QName QName)
    (a b : Option Snapshot) (arrow : Proarrow) : Bool := Id.run do
  let same := fun (x y : Option SynUnit) => Id.run do
    let some u := x | return false
    let some v := y | return false
    if let (some s, some t) := (a,b) then return kernelSignature s t u v rs
    return sigTokens u rs == sigTokens v {}
  match arrow.src, arrow.tgt with
  | _, .bot => return false
  | .bot, _ | .flags, .flags => return true
  | .unit x, .unit y => return same old.locals[x]? cand.locals[y]?
  | .ext x, .ext y =>
    if let (some i, some j) := (old.imports[x]?, cand.imports[y]?) then
      let targets := byUnit j.assumes
      return i.assumes.length == j.assumes.length && i.assumes.all fun u =>
        same (some u) targets[(renamedRef? rs u.uname).getD (renameQ x y u.uname)]?
    return same old.externals[x]? cand.externals[y]? || (x == y && old.externals[x]?.isNone && cand.externals[y]?.isNone)
  | _, _ => return false

def preserves (old cand : LeanMod) (p : Plan) (arrow : Proarrow)
    (oldSnap? candSnap? : Option Snapshot := none) :=
  preserved (indexMod old false) (indexMod cand false) (renames p) oldSnap? candSnap? arrow

def frontier (old cand : LeanMod) (p : Plan) (oldSnap? candSnap? : Option Snapshot := none) : List Obj := Id.run do
  let x := indexMod old (includeOwners := oldSnap?.isNone)
  let y := indexMod cand false
  let rs := renames p
  let mut changed : Std.HashSet Obj := {}
  let mut changedImports : Std.HashSet Lean.Name := {}
  for a in p.moves do
    unless preserved x y rs oldSnap? candSnap? a do
      changed := changed.insert a.src
      if let .ext q := a.src then
        if let some i := x.imports[q]? then changedImports := changedImports.insert i.imod.toLeanName
  if changed.isEmpty then return []
  let edges : List (Obj × Obj) := match oldSnap? with
    | some snap => snap.graph.semArrows
    | none => old.units.flatMap fun (u : SynUnit) => u.synRefs.map fun r => (.unit u.uname, x.owners[r]?.getD (.ext r))
  let affected := fun t => Id.run do
    if changed.contains t then return true
    if let .ext q := t then
      let mut n := q.toLeanName
      while !n.isAnonymous && !changedImports.isEmpty do
        if changedImports.contains n then return true
        n := n.getPrefix
    return false
  let deps := Std.HashSet.ofList (edges.filterMap fun (s,t) => if affected t then some s else none)
  let src := Std.HashSet.ofList (p.moves.map (·.src))
  return old.units.filterMap fun u =>
    let o := Obj.unit u.uname
    if deps.contains o && !src.contains o then some o else none

inductive PlanProblem where
  | unknownSrc (o : Obj)
  | unknownTgt (o : Obj)
  | lostUnit (o : Obj)
  | orphanUnit (o : Obj)
  | unsettled (o : Obj)
  | invalidMove (o : Obj)
  | duplicateUnit (o : Obj)
  deriving BEq, Repr

def validate (old : LeanMod) (p : Plan) (cand : LeanMod) (oldSnap? candSnap? : Option Snapshot := none) : List PlanProblem := Id.run do
  let x := indexMod old
  let rewritten := renameUnitRefs old (renames p)
  let expected := byUnit rewritten.units
  let y := indexMod cand
  let existsObj := fun (i : PlanIndex) => fun
    | .unit q => i.locals.contains q
    | .ext q => i.externals.contains q || i.imports.contains q || (i.owners[q]? matches some (.ext _))
    | .flags | .bot => true
  let mut errors := #[]
  let mut seen : Std.HashSet Proarrow := {}
  for a in p.moves do
    unless existsObj x a.src do errors := errors.push (.unknownSrc a.src)
    unless existsObj y a.tgt do errors := errors.push (.unknownTgt a.tgt)
    if seen.contains a || (a.src == .bot && a.tgt == .bot) then errors := errors.push (.invalidMove a.src)
    seen := seen.insert a
  let (src,tgt) := moveSets p
  for u in rewritten.units do
    unless src.contains (.unit u.uname) || y.locals[u.uname]?.any (·.rawSource == u.rawSource) do
      errors := errors.push (.lostUnit (.unit u.uname))
  let mut names := {}
  for u in cand.units do
    if (names : Std.HashSet QName).contains u.uname then errors := errors.push (.duplicateUnit (.unit u.uname))
    names := names.insert u.uname
    unless tgt.contains (.unit u.uname) || expected[u.uname]?.any (·.rawSource == u.rawSource) do
      errors := errors.push (.orphanUnit (.unit u.uname))
  if let some draft := draftAt p old then
    for u in draft.units do
      unless tgt.contains (.unit u.uname) || x.locals[u.uname]?.any (·.rawSource == u.rawSource) do
        errors := errors.push (.orphanUnit (.unit u.uname))
  return errors.toList ++ (frontier old cand p oldSnap? candSnap?).map .unsettled

def memoryIndex (mem : Memory) : Std.HashMap Obj (Array String) := Id.run do
  let mut notes := {}
  for (o, ns) in mem do
    notes := notes.alter o (fun prev => some (ns.foldl Array.push (prev.getD #[])))
  return notes

def inherit (p : Plan) (mem : Memory) : Memory := Id.run do
  let notes := memoryIndex mem
  let (sources, targets) := moveSets p
  let mut incoming : Std.HashMap Obj (Array Obj) := {}
  for a in p.moves do incoming := incoming.alter a.tgt fun xs => some ((xs.getD #[]).push a.src)
  let mut out := (mem.filter fun (o,_) => !targets.contains o && (o == .bot || !sources.contains o)).toArray
  for t in distinct (p.moves.map (·.tgt)) do
    let src := incoming[t]?.getD #[]
    let mut acc := if t == .bot || (src.contains .bot && !sources.contains t) then notes[t]?.getD #[] else #[]
    for s in src do
      unless s == .bot && t == .bot do acc := acc ++ notes[s]?.getD #[]
    out := out.push (t,(acc.push p.why).toList)
  return out.toList

/-- Route only named endpoints. An unrelated private note in a split child stays private. -/
def routeChildren (p : Plan) (mem : Memory) (children : List QName) : Std.HashMap QName Memory := Id.run do
  let slots := Std.HashSet.ofList (children.map QName.toLeanName)
  let notes := memoryIndex mem
  let mut streams : Std.HashMap Obj (Array String) := {}
  let mut targets : Std.HashMap QName (Array Obj) := {}
  for a in p.moves do
    let (.ext u, .ext v) := (a.src, a.tgt) | continue
    let mut owner := v.toLeanName
    while !owner.isAnonymous && !slots.contains owner do owner := owner.getPrefix
    if owner.isAnonymous || owner.isPrefixOf u.toLeanName then continue
    let some ns := notes[Obj.ext u]? <|> notes[Obj.unit u]? | continue
    let o := Obj.unit v
    unless streams.contains o do
      targets := targets.alter (QName.ofName owner) (fun os => some ((os.getD #[]).push o))
    streams := streams.alter o (fun prev => some ((prev.getD #[]) ++ ns))
  return targets.map fun _ os => os.toList.map fun o => (o, ((streams[o]?.getD #[]).push p.why).toList)

def routeChildMemory (p : Plan) (mem : Memory) (child : QName) : Memory :=
  (routeChildren p mem [child])[child]?.getD []

def crossChildMemory (p : Plan) (mem : Memory) (child : QName) : List String :=
  (routeChildMemory p mem child).flatMap Prod.snd

def encName (q : QName) : SExpr :=
  if q.segments.isEmpty || q.segments.any (·.contains '.') then
    .list [.sym "q", .list (q.segments.map .str), .str ""]
  else .str (String.intercalate "." q.segments)

def strVal : SExpr → Option String | .str s => some s | _ => none

def decName : SExpr → Option QName
  | .str s | .list (.sym "q" :: .str s :: _) => some (qualified s)
  | .list (.sym "q" :: .list parts :: _) => QName.mk <$> parts.mapM strVal
  | _ => none

def encNames (qs : List QName) : SExpr := .list (qs.map encName)
def decNames : SExpr → Option (List QName) | .list qs => qs.mapM decName | _ => none

def encObj : Obj → SExpr
  | .unit q => .list [.sym "unit", encName q]
  | .ext q => .list [.sym "ext", encName q]
  | .flags => .sym "flags"
  | .bot => .sym "bot"

def decObj : SExpr → Option Obj
  | .list [.sym "unit", q] => Obj.unit <$> decName q
  | .list [.sym "ext", q] => Obj.ext <$> decName q
  | .sym "flags" => some .flags
  | .sym "bot" => some .bot
  | _ => none

def encMove (a : Proarrow) : SExpr := .list [.sym "move", encObj a.src, encObj a.tgt]
def decMove : SExpr → Option Proarrow
  | .list [.sym "move", s, t] => return ⟨← decObj s, ← decObj t⟩
  | _ => none

def encodeMemory (mem : Memory) : SExpr := .list (.sym "memory" :: mem.map fun (o,ns) =>
  .list (.sym "note" :: encObj o :: ns.map .str))

def decodeMemory : SExpr → Option Memory
  | .list (.sym "memory" :: entries) => entries.mapM fun
    | .list (.sym "note" :: o :: ns) => return (← decObj o, ← ns.mapM strVal)
    | _ => none
  | _ => none

def encodePlan (p : Plan) : SExpr := .list [.sym "plan", .str p.why,
  .list (.sym "origin" :: p.origin.toList.map encName),
  .list (.sym "new" :: p.newMod.toList.map (fun m => .str (encodeCanonical m))),
  .list (.sym "moves" :: p.moves.map encMove)]

def decodePlan : SExpr → Option Plan
  | .list [.sym "plan", .str why, .list (.sym "origin" :: os), .list (.sym "new" :: ms), .list (.sym "moves" :: moves)] => do
    let origin ← os.mapM decName
    let mods ← ms.mapM (fun e => strVal e >>= decodeCanonical)
    guard (origin.length ≤ 1 && mods.length ≤ 1)
    return ⟨why, origin.head?, mods.head?, ← moves.mapM decMove⟩
  | _ => none

def PlanProblem.code : PlanProblem → String
  | .unknownSrc _ => "unknownSrc"
  | .unknownTgt _ => "unknownTgt"
  | .lostUnit _ => "lostUnit"
  | .orphanUnit _ => "orphanUnit"
  | .unsettled _ => "frontier_incomplete"
  | .invalidMove _ => "invalidMove"
  | .duplicateUnit _ => "duplicateUnit"

end Lojita.Transport
