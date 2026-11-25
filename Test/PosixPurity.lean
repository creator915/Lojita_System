import Lean

open Lean

namespace G1

private def origin (env : Environment) (n : Name) : Name := Id.run do
  let some i := env.getModuleIdxFor? n | return .anonymous
  return env.header.moduleNames[i.toNat]!

private def model (m : Name) := [`LojitaCtx.Posix, `LojitaCtx.Io].any (·.isPrefixOf m)
private def shipped (m : Name) := [`Init, `Std, `Lean].contains m.getRoot
private def baseAxiom (n : Name) := [``propext, ``Classical.choice, ``Quot.sound].contains n

private def route (path : List Name) := String.intercalate " -> " (path.reverse.map toString)
private def scope (cc : Bool) := if cc then "compiler" else "logical"

private structure Rule where
  layer : String
  owner : String
  evidence : String

private structure Policy where
  entries : Std.HashMap (String × String) (List Rule)
  parents : Std.HashMap String (List (String × String))

private def table (file header : String) : IO (List (List String)) := do
  let contents ← IO.FS.readFile s!"Test/audit/lean-4.36.0-{file}.tsv"
  let lines := contents.splitOn "\n" |>.filter fun s => !s.isEmpty && !s.startsWith "#"
  unless lines.head? == some header do throw <| IO.userError s!"invalid {file} header"
  return lines.tail.map (·.splitOn "\t")

private def loadPolicy : IO Policy := do
  let mut entries := {}
  let mut parents := {}
  for row in ← table "trust" "scope\tkind\tname\tmodule\tevidence\treason" do
    let [layer, kind, name, owner, evidence, why] := row | throw <| IO.userError "malformed trust row"
    unless ["both","logical","compiler"].contains layer && ["unsafe","extern","implemented_by","rewrite","artifact"].contains kind &&
        shipped owner.toName && !name.isEmpty && !evidence.isEmpty && !why.isEmpty do
      throw <| IO.userError s!"invalid trust row for {name}"
    let key := (kind,name)
    let old : List Rule := entries[key]?.getD []
    if old.any (fun r => r.layer == layer || r.layer == "both" || layer == "both") then
      throw <| IO.userError s!"duplicate trust rule {kind} {name}"
    entries := entries.insert key (⟨layer, owner, evidence⟩ :: old)
  for row in ← table "parents" "child\tparent\tmodule" do
    let [child, parent, owner] := row | throw <| IO.userError "malformed restricted edge"
    let old : List (String × String) := parents[child]?.getD []
    if old.contains (parent,owner) then throw <| IO.userError s!"duplicate restricted edge {parent} -> {child}"
    parents := parents.insert child ((parent,owner)::old)
  return ⟨entries, parents⟩

private def Policy.approved (p : Policy) (env : Environment) (cc : Bool) (kind : String)
    (n : Name) (evidence : Option String := none) := Id.run do
  let mod := origin env n
  return shipped mod && (p.entries[(kind,n.toString)]?.getD []).any fun r =>
    (r.layer == "both" || r.layer == scope cc) && r.owner == mod.toString &&
      evidence.all (· == r.evidence)

private def externCode (entries : List ExternEntry) : String :=
  ";".intercalate <| entries.map fun
    | .standard b fn => s!"standard:{b}:{fn}"
    | .adhoc b => s!"adhoc:{b}"
    | .inline b pat => s!"inline:{b}:{pat}"
    | .opaque => "opaque"

private def originalReason (env : Environment) (n : Name) (d : ConstantInfo) :=
  if n == ``sorryAx then "sorry"
  else if (d matches .axiomInfo _) && !baseAxiom n then "axiom"
  else if isExtern env n then "extern" else if d.isUnsafe then "unsafe" else ""

/-- Reproduce both historical walks without subtracting any approved exceptions.
    Every original violation gets its own path, including the original implemented_by edges. -/
private def raw (env : Environment) (roots : Array Name) (cc : Bool) : IO Unit := do
  let mut todo := roots.map fun n => (n,[n])
  let mut seen : NameSet := {}
  let mut rows : Array String := #[]
  let mut counts : Std.TreeMap String Nat := Std.TreeMap.ofList [("axiom",0),("sorry",0),("extern",0),("unsafe",0)]
  let mut projectHits := 0
  let mut rewrites := 0
  let mut i := 0
  while let some (n,path) := todo[i]? do
    i := i+1
    if seen.contains n then continue
    seen := seen.insert n
    let some d := env.find? n | throw <| IO.userError s!"missing {n}"
    let why := originalReason env n d
    unless why.isEmpty do
      if model (origin env n) then projectHits := projectHits+1
      counts := counts.insert why (counts[why]?.getD 0 + 1)
      rows := rows.push s!"G1 RAW {scope cc} [{why}] {route path}"
    let mut deps := d.getUsedConstantsAsSet
    if let some impl := Compiler.getImplementedBy? env n then deps := deps.insert impl
    if cc then
      if let some r := (Compiler.CSimp.ext.getState env).map.find? n then
        rewrites := rewrites+1
        deps := (deps.insert r.toDeclName).insert r.thmName
    for dep in deps do unless seen.contains dep do todo := todo.push (dep, dep :: path)
  IO.println s!"G1 RAW {scope cc}: roots={roots.size}, reachable={seen.size}, forbidden={rows.size} {counts.toList}, project-forbidden={projectHits}, csimp={rewrites}"
  for row in rows do IO.println row

/-- The saved well-founded equations can name a proof which is inlined in the
    compiled companion. Kernel proof irrelevance applies only after checking
    both terms are proofs of definitionally equal propositions in the same context. -/
private partial def sameBody (env : Environment) (parent : Name) (actual expected : Expr) : MetaM Bool := do
  let a := actual.consumeMData
  let b := expected.consumeMData
  if a.eqv b then return true
  if let some p := b.getAppFn.constName? then
    if parent.isPrefixOf p && (env.find? p).any (· matches .thmInfo _) then
      if (← Meta.isProof a) && (← Meta.isProof b) then
        return ← Meta.withTransparency .reducible <| Meta.isDefEq (← Meta.inferType a) (← Meta.inferType b)
  let visit := sameBody env parent
  match a, b with
  | .app f x, .app g y => return (← visit f g) && (← visit x y)
  | .lam n ta ba bi, .lam _ tb bb _ | .forallE n ta ba bi, .forallE _ tb bb _ =>
    unless ← visit ta tb do return false
    Meta.withLocalDecl n bi ta fun x => visit (ba.instantiate1 x) (bb.instantiate1 x)
  | .letE n ta va ba _, .letE _ tb vb bb _ =>
    unless (← visit ta tb) && (← visit va vb) do return false
    Meta.withLetDecl n ta va fun x => visit (ba.instantiate1 x) (bb.instantiate1 x)
  | .proj n i x, .proj m j y => return n == m && i == j && (← visit x y)
  | _, _ => return false

/-- Check the actual compiler companion of a structural or well-founded total definition against its
    stored recursion equations. An opaque partial definition has no such justification. -/
private def totalCompanion (env : Environment) (impl : ConstantInfo) : MetaM Bool := do
  let .defnInfo d := impl | return false
  let some parent := Compiler.isUnsafeRecName? d.name | return false
  let some (.defnInfo orig) := env.checked.get.find? parent | return false
  unless orig.safety == .safe && d.type == orig.type && origin env d.name == origin env parent do return false
  let some (declNames, value) :=
    (Elab.Structural.eqnInfoExt.find? env parent).map (fun e => (e.declNames, e.value)) <|>
    (Elab.WF.eqnInfoExt.find? env parent).map (fun e => (e.declNames, e.value)) | return false
  let expected := value.replace fun
    | .const f us => if declNames.contains f then some (mkConst (Compiler.mkUnsafeRecName f) us) else none
    | _ => none
  sameBody env parent d.value (← Elab.eraseRecAppSyntaxExpr expected)

private def effectful (n : Name) :=
  [`IO,`EIO,`BaseIO,`EST,`EStateM.RealWorld].any (·.isPrefixOf n)

private structure Item where
  n : Name
  path : List Name
  compiled : Bool

private structure Verdict where
  messages : Std.TreeSet String := {}
  axiomsChecked : Nat := 0
  companions : NameSet := {}
  artifacts : NameSet := {}

private abbrev CheckM := StateT Verdict IO

private def deny (kind : String) (path : List Name) (detail : String := "") : CheckM Unit := do
  modify fun v => {v with messages := v.messages.insert s!"G1 DENY [{kind}] {route path} {detail}"}

private def checkAxioms (env : Environment) (roots : Array Name) : CheckM Unit := do
  let ctx : PPContext := {env}
  for n in roots do
    let axioms ← try ctx.runCoreM (collectAxioms n) catch e => throw <| IO.userError s!"checking axioms of {n}: {e}"
    for ax in axioms do
      unless baseAxiom ax do
        let kind := if ax == ``sorryAx then "sorry" else "axiom"
        deny kind [ax,n] "(kernel collectAxioms)"
  modify fun v => {v with axiomsChecked := roots.size}

private def restrictedEdge (policy : Policy) (env : Environment) (parent child : Name)
    (path : List Name) : CheckM Unit := do
  let originMod := origin env parent
  if let some allowed := policy.parents[child.toString]? then
    let theoremHere := (env.find? parent).any (· matches .thmInfo _)
    unless allowed.contains (parent.toString, originMod.toString) && (shipped originMod || theoremHere) do
      deny (if child == `lcProof then "axiom" else "escape") (child::path) "(unreviewed restricted edge)"
  else if !shipped originMod then
    if [`panic,`panicCore,`panicWithPos,`panicWithPosWithDecl,`getObjTagNat,`unsafeCast,
        `getElem!,`Option.get!,`List.get!Internal].contains child then
      deny "escape" (child::path) "(direct runtime primitive)"
    if let some d := env.find? child then
      if shipped (origin env child) && (d.isUnsafe || d.isPartial) then
        deny "unsafe" (child::path) "(direct use of compiler implementation)"

private def reviewed (env : Environment) (roots : Array Name) (policy : Policy) (cc : Bool) : CheckM Unit := do
  let mut todo := roots.map fun n => (⟨n, [n], false⟩ : Item)
  let mut seen : Std.HashSet (Name × Bool) := {}
  let ctx : PPContext := {env}
  let mut i := 0
  while let some it := todo[i]? do
    i := i+1
    let n := it.n
    if seen.contains (n,it.compiled) then continue
    seen := seen.insert (n,it.compiled)
    let some d := env.find? n | throw <| IO.userError s!"missing declaration {n}"
    let official := shipped (origin env n)
    if n == ``sorryAx then deny "sorry" it.path
    if (d matches .axiomInfo _) && !baseAxiom n && n != ``sorryAx then
      if n == `lcProof && it.compiled && policy.approved env cc "artifact" n (some "compiler-proof-marker") then
        modify fun v => {v with artifacts := v.artifacts.insert n}
      else deny "axiom" it.path
    if effectful n then deny "effect" it.path
    if let some ext := getExternAttrData? env n then
      unless policy.approved env cc "extern" n (some (externCode ext.entries)) do
        deny "extern" it.path (externCode ext.entries)
      if d.isUnsafe && !it.compiled then deny "unsafe" it.path "(logical path)"
    else if d.isUnsafe && n != `lcProof then
      unless it.compiled && policy.approved env cc "unsafe" n do deny "unsafe" it.path
    if d.isPartial then
      let valid ← try ctx.runMetaM (totalCompanion env d) catch e => throw <| IO.userError s!"checking recursive body of {n}: {e}"
      if !official && valid then
        modify fun v => {v with companions := v.companions.insert n}
      else deny "partial" it.path
    if !official then
      if let some dest := getExportNameFor? env n then deny "export" it.path s!"(native symbol {dest})"
      if Compiler.hasCSimpAttribute env n then deny "rewrite" it.path "(unreviewed csimp equation)"
      let recName := Compiler.mkUnsafeRecName n
      if let some body := env.find? recName then
        if body.isPartial || body.isUnsafe then
          todo := todo.push ⟨recName, recName :: it.path, true⟩
    for child in d.getUsedConstantsAsSet do
      restrictedEdge policy env n child it.path
      if !seen.contains (child,it.compiled) then todo := todo.push ⟨child,child::it.path,it.compiled⟩
    if let some impl := Compiler.getImplementedBy? env n then
      unless policy.approved env cc "implemented_by" n (some impl.toString) && shipped (origin env impl) do
        deny "implemented_by" (impl::it.path)
      todo := todo.push ⟨impl,impl::it.path,true⟩
    if cc then
      if let some r := (Compiler.CSimp.ext.getState env).map.find? n then
        let proof := r.thmName
        let target := r.toDeclName
        unless policy.approved env cc "rewrite" n (some s!"{target}|{proof}") &&
            shipped (origin env target) && shipped (origin env proof) do
          deny "rewrite" (proof::it.path) s!"(target {target})"
        todo := todo.push ⟨target,target::it.path,true⟩ |>.push ⟨proof,proof::it.path,true⟩

private def options : List String → List Name → List Name → IO (List Name × List Name)
  | [], mods, roots => pure (mods.reverse, roots.reverse)
  | "--module"::m::xs, mods, roots => options xs (m.toName::mods) roots
  | "--root"::n::xs, mods, roots => options xs mods (n.toName::roots)
  | _, _, _ => throw <| IO.userError "usage: --module MOD --root NAME (repeatable)"

private def packageOrigins (dir : System.FilePath) (mods : Array Name) : IO Unit := do
  for mod in mods do
    if shipped mod || mod.getRoot == `Lake then
      let actual ← IO.FS.realPath (← findOLean mod)
      let expected := modToFilePath dir mod "olean"
      unless actual == expected do throw <| IO.userError s!"G1 DENY [origin] {mod} at {actual}, expected {expected}"

private unsafe def run (args : List String) : IO UInt32 := do
  unless versionString == "4.36.0" && githash == "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9" do
    throw <| IO.userError s!"G1 DENY [origin] unpinned Lean {versionString} {githash}"
  let sysroot ← IO.FS.realPath (← getBuildDir)
  let declared ← IO.FS.realPath (← findSysroot)
  unless sysroot == declared do throw <| IO.userError s!"G1 DENY [origin] inconsistent compiler roots {sysroot}, {declared}"
  initSearchPath sysroot
  let lib ← IO.FS.realPath (← getLibDir sysroot)
  packageOrigins lib #[`Init,`Std,`Lean,`Lake]
  let (mods, selected) ← options args [] []
  unless mods.isEmpty == selected.isEmpty do throw <| IO.userError "both --module and --root are required"
  let imports := if mods.isEmpty then [`LojitaCtx] else mods
  enableInitializersExecution
  let env ← importModules (imports.map fun m => {module := m}).toArray {} (loadExts := true) (level := .private)
  packageOrigins lib env.header.moduleNames
  let mut roots := selected.toArray
  if roots.isEmpty then
    for dir in ["LojitaCtx/Posix","LojitaCtx/Io"] do
      for file in ← (System.FilePath.mk dir).walkDir do
        if file.extension == some "lean" then
          let mod := ((file.withExtension "").components).foldl Name.str Name.anonymous
          unless env.header.moduleNames.contains mod do throw <| IO.userError s!"G1 missing module {mod}"
    let projectLib ← IO.FS.realPath ".lake/build/lib/lean"
    for mod in env.header.moduleNames do
      if mod.getRoot == `LojitaCtx then
        let actual ← IO.FS.realPath (← findOLean mod)
        let expected := modToFilePath projectLib mod "olean"
        unless actual == expected do throw <| IO.userError s!"G1 DENY [origin] {mod} at {actual}, expected {expected}"
    for (n,_) in env.constants.toList do
      if model (origin env n) then roots := roots.push n
  unless !roots.isEmpty && roots.all env.contains do throw <| IO.userError "missing G1 roots"
  let policy ← loadPolicy
  raw env roots false
  raw env roots true
  let (_, verdict) ← (do
    -- A native export in an imported module may interpose on a primitive even
    -- without an outgoing constant reference from the functional model.
    if selected.isEmpty then
      for (n,_) in env.constants.toList do
        unless shipped (origin env n) || (origin env n).getRoot == `Lake do
          if let some symbol := getExportNameFor? env n then deny "export" [n] s!"(native symbol {symbol})"
    checkAxioms env roots
    reviewed env roots policy false
    reviewed env roots policy true).run {}
  for msg in verdict.messages.toList do IO.println msg
  IO.println s!"G1 reviewed: roots={roots.size}, kernel axiom checks={verdict.axiomsChecked}, verified recursion companions={verdict.companions.size}, compiler-only markers={verdict.artifacts.size}, denied={verdict.messages.size}"
  return if verdict.messages.isEmpty then 0 else 1

end G1

unsafe def main (args : List String) : IO UInt32 := G1.run args
