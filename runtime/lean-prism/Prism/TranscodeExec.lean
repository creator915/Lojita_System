import Prism.ExecFields
import Prism.ExecRecords
import Prism.ExecGhost

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Prism

namespace Exec

open Chk Lean.Parser.Term
open Lean (Term TSyntax Ident mkIdent)
open Lean.Parser.Command (declId)

/-- Agda generalizes a universe in a local signature at the enclosing declaration. -/
private partial def clauseLevels : Clause → List String
  | .clause _ rhs ds =>
    (match rhs with | .withRHS _ cs => cs.flatMap clauseLevels | _ => []) ++
    ds.flatMap fun
      | .sig _ _ t => collectLevelVarsInType t
      | .fun_ _ _ cs => cs.flatMap clauseLevels
      | _ => []

private def header (ctx : EmitCtx) (lvls : List String) (ty : Expr) (cs : List Clause) :
    PrismOutcome (List String × Array Binder × Option Term) := do
  let (hidden, result) := splitHidden ty
  let slots := hidden.flatMap fun (.bind _ xs t) =>
    if resultHeadCanon t == some ["Agda","Primitive","Level"] then [] else xs
  let bs ← telescope ctx lvls hidden
  let colors := (CatStructure.executionPorts ty cs).toList.drop (hidden.foldl (fun k (.bind _ xs _) => k + xs.length) 0)
  let ann ← if isMetaExpr result then pure none else some <$> execSignature ctx lvls result colors cs
  return (slots, bs, ann)

private partial def headPath : LHS → List String
  | .head q _ => q.full
  | .proj _ l _ | .with_ l _ _ => headPath l

private def localPath (ctx : EmitCtx) (n : String) (cs : List Clause) :=
  ((cs.head?).map fun (.clause l _ _) => headPath l).getD (ctx.modPrefix ++ ["_",n])

private def localIdent (path : List String) : Ident :=
  varId ("where_" ++ toString path.length ++ "_" ++ path.getLastD "")

private partial def headPats : LHS → List (Arg Pat)
  | .head _ ps => ps
  | .proj _ l _ | .with_ l _ _ => headPats l

private def shareClosed (cs : List Clause) : Bool :=
  let ready := match cs with
    | [.clause (.head _ _) (.rhs e) []] => immediateBinding e
    | _ => false
  !ready && cs.all (fun (.clause l _ _) => (headPats l).all (·.hid != .visible))

/-- Scope-only Agda Code can omit a solved instance argument. When neither a
    result index nor an equation needs its value the execution telescope and
    every call can erase that slot, including an explicitly supplied proof. -/
private def instanceLayout (ty : Expr) (cs : List Clause) : List (String × Bool) := Id.run do
  let formals := (CatStructure.portDomains ty).filter (·.hid == .inst)
  if formals.isEmpty then return []
  let names := formals.zipIdx.map fun (a,i) => a.label.getD ("_instance" ++ toString i)
  let indexedUses := collectVarsExpr ty
  return names.zipIdx.map fun (name,i) =>
    let demanded := cs.any fun (.clause l r ds) => Id.run do
      let used := collectVarsRhs r ++ ds.flatMap collectVarsDecl
      if used.contains name then return true
      let mut pos := 0
      for a in headPats l do
        if a.hid != .inst then continue
        pos := (a.label >>= fun n => names.findIdx? (· == n)).getD pos
        if pos == i then
          match a.thing with
          | .varP n => return used.contains n
          | .wildP | .dotP _ => return false
          | _ => return true
        pos := pos + 1
      return false
    (name, !indexedUses.contains name && !demanded)

private partial def instanceType (slots : List (String × Bool)) : Expr → Expr
  | .pi (.bind .inst ns t) rest =>
    (slots.take ns.length).foldr (fun (n,unused) r => if unused then r else .pi (.bind .hidden [n] t) r)
      (instanceType (slots.drop ns.length) rest)
  | .fun_ a rest =>
    if a.hid == .inst then
      let r := instanceType (slots.drop 1) rest
      match slots.head? with
      | some (n,false) => .pi (.bind .hidden [n] a.thing) r
      | _ => r
    else .fun_ a (instanceType slots rest)
  | .pi b rest => .pi b (instanceType slots rest)
  | e => e

private partial def instanceLhs (slots : List (String × Bool)) : LHS → LHS
  | .head q ps => .head q (projectInstances slots ps)
  | .proj q l ps => .proj q (instanceLhs slots l) ps
  | .with_ l ps extra => .with_ (instanceLhs slots l) ps extra

private def instanceView (ctx : EmitCtx) (path : List String) (ty : Expr) (cs : List Clause) : Expr × List Clause :=
  match ctx.instanceSlots[path]? with
  | some slots => (instanceType slots ty, cs.map fun (.clause l r ds) => .clause (instanceLhs slots l) r ds)
  | none => (ty,cs)

private def addInstanceSlots (ctx : EmitCtx) (path : List String) (ty : Expr) (cs : List Clause) : EmitCtx :=
  let slots := instanceLayout ty cs
  if slots.isEmpty then ctx else {ctx with instanceSlots := ctx.instanceSlots.insert path slots}

private def installInstanceSlots (ctx : EmitCtx) (modules : List CodeMod) : EmitCtx := Id.run do
  let mut ctx := ctx
  for cm in modules do
    let sigs := Std.HashMap.ofList (cm.decls.filterMap fun | .sig _ n t => some (n,t) | _ => none)
    for d in cm.decls do
      if let .fun_ _ n cs := d then
        if let some ty := sigs[n]? then ctx := addInstanceSlots ctx (cm.modName.full ++ [n]) ty cs
  return ctx

private def localContext (ctx : EmitCtx) (units : List ModUnit) : PrismOutcome EmitCtx := do
  let mut scope := ctx
  for u in units do
    let .funUnit _ n t cs := u.kind | .bot "unsupported local data declaration"
    let path := localPath ctx n cs
    let sym : SymInfo := {localName := n, canonPath := path, kind := .defSym, leanName := (localIdent path).getId.toString}
    scope := addInstanceSlots scope path t cs
    let (t,_) := instanceView scope path t cs
    let labels := (splitHidden t).1.flatMap fun (.bind _ ns _) => ns.map leanMangleIdent
    scope := {scope.withLocal sym with implicitIndex := scope.implicitIndex.insert path labels}
  return scope

private def pats (ctx : EmitCtx) (used : List String) (ps : List (Arg Pat)) : PrismOutcome (Array Term) :=
  ps.toArray.mapM fun p => pattern ctx (wildcardUnusedPat used p.thing)

private structure RowVariable where
  name : String
  port : Nat
  root : Bool
  deferred : Bool

private partial def rowVariables (ctx : EmitCtx) (port : Nat) (p : Pat)
    (root := true) (deferred := false) : List RowVariable :=
  match p with
  | .varP n => [⟨n,port,root,deferred⟩]
  | .asP n sub => ⟨n,port,root,deferred⟩ :: rowVariables ctx port sub root deferred
  | .conP q ps =>
    let paths := q.full :: q.canonAlts
    let pair := paths.contains ["Agda","Builtin","Sigma","_,_"]
    ps.zipIdx.flatMap fun (a,i) =>
      let delayed := pair || paths.any fun path => (ctx.deferredFields[path]?.getD []).contains i
      rowVariables ctx port a.thing false delayed
  | .recP fs => fs.flatMap fun (_,sub) => rowVariables ctx port sub false true
  | _ => []

private structure EquationRow where
  patterns : Array Term
  body : Term
  variables : List RowVariable

/-- Each source RHS occurs in one lexical definition, shared by its ordered
    demand test and by the terminal exhaustive match. Empty rows are functions
    of Unit as well, so preparing the equation never evaluates its RHS. -/
private def splitBody (split : CatStructure.DemandSplit) (rows : Array EquationRow)
    (result : Term) : PrismOutcome Term := do
  let vars := (List.range split.arity).toArray.map fun i => ident ("port" ++ toString i)
  let mut arms := #[]
  let mut branches := #[]
  let mut handlers := #[]
  let covered := split.tests.back?.any (fun last => last.all (!·))
  for (row,i) in rows.zipIdx do
    if covered then
      branches := branches.push row.body
      continue
    let handler := ident ("equationRhs" ++ toString i)
    let mut binders : Array (TSyntax ``funBinder) := #[]
    let mut inputs : Array Term := #[]
    let some tests := split.tests[i]? | .bot "missing clause demand"
    for binding in row.variables do
      let x := varId binding.name
      let b ← if binding.root then do
        let some port := vars[binding.port]? | .bot "missing equation variable"
        if split.delayed.contains binding.port && tests[binding.port]? == some true then
          `(funBinder| ($x:ident : type_of% (Thunk.get $port:ident)))
        else `(funBinder| ($x:ident : type_of% $port:ident))
      else if binding.deferred then `(funBinder| ($x:ident : Thunk _))
      else `(funBinder| $x:ident)
      binders := binders.push b
      inputs := inputs.push (← `(agda_exec_arg% (agda_exec_val% $x:ident)))
    let rhs ← `(fun $binders:funBinder* (_ : Unit) => ($(row.body) : $result))
    handlers := handlers.push (handler,rhs)
    let call ← `($handler:ident $inputs* ())
    branches := branches.push call
    arms := arms.push (← `(matchAltExpr| | $(row.patterns):term,* => $call))
  let mut fallback : Option Term := none
  unless covered do
    let mut discrs := #[]
    for (v,k) in vars.zipIdx do
      let t ← if split.delayed.contains k then `(Thunk.get $v:ident) else pure (v : Term)
      discrs := discrs.push (← `(matchDiscr| $t:term))
    fallback := some (← `(match $discrs:matchDiscr,* with $arms:matchAlt*))
  for ((row,i),success₀) in (rows.zipIdx.zip branches).reverse do
    let some tests := split.tests[i]? | .bot "missing clause demand"
    let next := ident ("nextRow" ++ toString i)
    let mut success := success₀
    for (p,k) in row.patterns.zipIdx.reverse do
      let some v := vars[k]? | .bot "clause pattern outside telescope"
      if tests[k]? == some true then
        let input ← if split.delayed.contains k then `(Thunk.get $v:ident) else pure (v : Term)
        success ← `(match $input:term with | $p => $success | _ => $next:ident ())
      else
        success ← `(match $v:ident with | $p => $success)
    fallback ← match fallback with
      | none => pure (some success)
      | some rest => some <$> `(let $next:ident := fun (_ : Unit) => $rest; $success)
  let some start := fallback | .bot "empty ordered clause matrix"
  let mut body := start
  for (name,rhs) in handlers.reverse do body ← `(let $name:ident := $rhs; $body)
  `(fun $vars:ident* => set_option match.ignoreUnusedAlts true in $body)

mutual

  private partial def value (ctx : EmitCtx) (lvls slots : List String) (cs : List Clause) (ty : Expr) :
      PrismOutcome Term := do
    let mut arms := #[]
    let mut rows := #[]
    for .clause l r ws in cs do
      let .head _ ps := l | .bot "copattern requires a record result"
      let (hp,vp) := ps.span (·.hid != .visible)
      if vp.any (·.hid != .visible) then .bot "interleaved executable clause patterns"
      let t ← match r with
        | .absurdRHS => do
          let some arg := vp.findSome? (fun a => replaceFirstAbsurdPat a.thing)
            | continue
          let ps := vp.map fun a => {a with thing := (replaceFirstAbsurdPat a.thing).getD a.thing}
          let ps ← pats ctx ["_abs_bot"] ps
          let _ := arg
          let h := varId "_abs_bot"
          arms := arms.push (← `(matchAltExpr| | $ps:term,* => nomatch $h:ident))
          continue
        | _ => rhs ctx lvls r ws
      let t ← aliasLets slots hp t
      if vp.isEmpty then return t
      let used := collectVarsRhs r ++ ws.flatMap collectVarsDecl
      let ps ← pats ctx used vp
      arms := arms.push (← `(matchAltExpr| | $ps:term,* => $t))
      let names := vp.zipIdx.flatMap fun (a,i) =>
        rowVariables ctx i (wildcardUnusedPat used a.thing)
      rows := rows.push ⟨ps,t,names⟩
    if arms.isEmpty then .bot "empty executable clause matrix"
    if let some split := CatStructure.branchDemand ty cs then
      let rec codomain : Expr → Expr
        | .pi _ b | .fun_ _ b => codomain b
        | b => b
      return ← splitBody split rows (← execTypeAlias ctx lvls (codomain ty))
    `(fun $arms:matchAlt*)

  private partial def rhs (ctx : EmitCtx) (lvls : List String) (r : RHS) (ws : List Decl)
      (outer : List (Arg Pat) := []) : PrismOutcome Term := do
    if !ws.isEmpty then
      let (_, units) ← extractModUnits {modName := mkQ (ctx.modPrefix ++ ["_"]), params := [], decls := ws}
      let scope ← localContext ctx units
      let mut body ← rhs scope lvls r [] outer
      -- Dependency order for a let telescope runs from the enclosing binder inward.
      for ids in (computeUnitSCCs units).reverse do
        let group := ids.filterMap (units[·]?)
        if let [u] := group then
          if let .funUnit _ n t [.clause (.head q []) (.rhs e) []] := u.kind then
            if !mentionsQName q.full e then
              let nm := localIdent (localPath ctx n [.clause (.head q []) (.rhs e) []])
              let v ← expr scope lvls e
              let ann ← if isMetaExpr t then pure none else some <$> expr scope lvls t
              let (ann,v) ← shareBinding (!immediateBinding e) ann v
              body ← `(let $nm:ident $[: $ann]? := $v; $body)
              continue
        let mut decls := #[]
        for u in group do
          let .funUnit _ n t cs := u.kind | .bot "unsupported local declaration"
          let path := localPath ctx n cs
          let nm := localIdent path
          let (t, cs) := instanceView scope path t cs
          let (slots,bs,ann) ← header scope lvls t cs
          let v ← value scope lvls slots cs t
          let (ann,v) ← shareBinding (shareClosed cs) ann v
          decls := decls.push (← `(letRecDecl| $nm:ident $bs:bracketedBinder* $[: $ann]? := $v))
        body ← `(let rec $decls:letRecDecl,*; $body)
      return body
    match r with
    | .rhs e => expr ctx lvls e
    | .rewriteRHS _ inner => rhs ctx lvls inner [] outer
    | .absurdRHS => .bot "unbound absurd pattern"
    | .withRHS es cs =>
      let discrs ← es.toArray.mapM fun e => do
        let t ← expr ctx lvls e
        `(matchDiscr| $t:term)
      let mut arms := #[]
      for .clause l sub ds in cs do
        let .with_ _ allP extra := l | .bot "malformed with clause"
        let ps := if allP.length == es.length then allP else allP.drop outer.length
        if ps.length != es.length then .bot "wrong with-clause arity"
        let used := collectVarsRhs sub ++ ds.flatMap collectVarsDecl
        if sub matches .absurdRHS then
          let ps ← pats ctx ["_abs_bot"] (ps.map fun a => {a with thing := (replaceFirstAbsurdPat a.thing).getD a.thing})
          let h := varId "_abs_bot"
          arms := arms.push (← `(matchAltExpr| | $ps:term,* => nomatch $h:ident))
        else
          let mut t ← rhs ctx lvls sub ds (outer ++ ps)
          let extra := extra.filter (·.hid == .visible)
          if !extra.isEmpty then
            let ep ← pats ctx used extra
            t ← `(fun | $ep:term,* => $t)
          let ps ← pats ctx used ps
          arms := arms.push (← `(matchAltExpr| | $ps:term,* => $t))
      `(match $discrs:matchDiscr,* with $arms:matchAlt*)
end

private def executableFunction (ctx : EmitCtx) (n : String) (ty : Expr) (cs : List Clause)
    (recursive : Bool) : PrismOutcome Cmd := do
  let (ty,cs) := instanceView ctx (ctx.modPrefix ++ [n]) ty cs
  let levels := (collectLevelVarsInType ty ++ cs.flatMap clauseLevels).eraseDups
  let (slots, bs, ann) ← header ctx levels ty cs
  let name ← declName ctx (leanMangleIdent n) levels
  let body ← if codomainIsSet ty then
    if let [.clause (.head _ []) (.rhs e) []] := cs then execTypeAlias ctx levels e
    else value ctx levels slots cs ty
  else if cs.any (fun (.clause l _ _) => l matches .proj ..) then
    ExecRecords.copatternBody ctx levels slots ty cs
  else value ctx levels slots cs ty
  let body ← if resultHeadCanon ty == some ["Agda","Builtin","Equality","_≡_"] then
    `(agda_exec_proof% $body)
  else pure body
  if codomainIsSet ty || (isMetaExpr ty && cs.any (fun | .clause _ (.rhs e) _ => looksLikeTypeRhs e | _ => false)) then
    `(abbrev $name:declId $bs:bracketedBinder* $[: $ann]? := $body)
  else
    let (ann,body) ← shareBinding (shareClosed cs) ann body
    if recursive then
      `(partial def $name:declId $bs:bracketedBinder* $[: $ann]? := $body)
    else
      `(def $name:declId $bs:bracketedBinder* $[: $ann]? := $body)

def lower (deps : List (CodeMod × ExportedModule)) (cm : CodeMod) (em : ExportedModule)
    (plan : SlicePlan) (entry : Bool) (deferred : DeferredFields) : PrismOutcome (Array Cmd) := do
  let ctx := {buildBaseEmitCtx deps cm em .erasedExec with deferredFields := deferred}
  let ctx := installInstanceSlots ctx (cm :: deps.map Prod.fst)
  let units := plan.units.toArray
  let mut commands := #[]
  for ids in plan.sccs do
    let group := ids.filterMap (units[·]?)
    let mut block := #[]
    for u in group do
      match u.kind with
      | .funUnit _ n ty cs =>
        let partialNeeded := group.length > 1 || cs.any (fun (.clause _ _ ds) => !ds.isEmpty) ||
          !(analyzeFunctionRecursion ctx.modPrefix n cs matches .translated .nonRecursive)
        block := block.push (← executableFunction ctx n ty cs partialNeeded)
      | .anonUnit .. => pure ()
      | .postulateUnit _ n _ => .bot s!"cannot compile executable from postulated symbol '{n}'"
      | _ => block := block.push (← Chk.unit ctx u)
    if block.size > 1 then commands := commands.push (← `(mutual $block:command* end))
    else commands := commands ++ block
    for u in group do commands := commands ++ (← ExecRecords.projections ctx u)
  if entry then
    unless units.any (fun u => u.kind matches .funUnit _ "main" ..) do .bot "missing executable main"
    let mainId := mkIdent <| (Lean.Name.mkSimple (leanModNamespace ctx.modPrefix)).str (leanMangleIdent "main")
    let entryId := ident "main"
    commands := commands.push (← `(def $entryId:ident (args : List String) : IO Unit := do
      ST.Ref.set $(mkIdent `AgdaMirror._agdaArgsRef) (some args)
      let _ ← agda_exec_val% $mainId:ident
      pure ()))
  return commands

end Exec

def transcodeExec (deps : List (CodeMod × ExportedModule)) (cm : CodeMod) (em : ExportedModule)
    (plan : SlicePlan) (deferred : DeferredFields) (emitMainEntry := false) : Except String (Array Chk.Cmd) :=
  Chk.out <| Exec.lower deps cm em plan emitMainEntry deferred

end Prism
