import Lean
import AgdaMirror.AxiomGuard
import Prism.CatStructure
import Prism.ExecPorts
import Prism.FactorMutual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Prism

/-- Validate unused generalizable names with one private, kernel-checked
    telescope. References between their declared types use canonical names.
    A reference outside this telescope still requires Agda generalization. -/
def checkedVariableView (cm : CodeMod) : PrismOutcome (CodeMod × Option String) := do
  let variables := cm.decls.flatMap fun | .variable_ vs => vs | _ => []
  if variables.isEmpty then return (cm, none)
  let names := variables.map fun (n, _) => cm.modName.full ++ [n]
  let decls := cm.decls.filter fun | .variable_ _ => false | _ => true
  if decls.any (fun d => (collectDeclQNames d).any names.contains) then
    .bot "used generalized variable requires Agda"
  let occupied := renderSExpr (encodeCodeMod cm)
  let mut fresh := "PrismVariableCheck"
  while occupied.contains fresh do fresh := fresh ++ "X"
  let mut replacements := []
  let mut bs := #[]
  for ((_, ty), (path, i)) in variables.zip (names.zipIdx) do
    let localName := fresh ++ toString i
    bs := bs.push (.bind .hidden [localName] (CatStructure.fieldTy replacements ty))
    replacements := (path, Expr.var localName) :: replacements
  let ty := bs.toList.foldr Expr.pi (.set 1)
  let mods : Mods := {isPrivate := true}
  let lhs := LHS.head (mkQ (cm.modName.full ++ [fresh])) []
  let check := [Decl.sig mods fresh ty, .fun_ mods fresh [.clause lhs (.rhs (.set 0)) []]]
  return ({cm with decls := decls ++ check}, some fresh)

namespace Chk

open Lean (TSyntax Syntax Term Ident mkIdent)
open Lean.Parser.Term
open Lean.Parser.Command (declId ctor structSimpleBinder declVal)
abbrev Cmd := TSyntax `command
abbrev Binder := TSyntax ``bracketedBinder
abbrev IdDecl := TSyntax ``declId

-- The input is already scope checked. All source binders and references are
-- supplied explicitly as identifiers and every mirror constant has a fixed name.
instance : Lean.MonadQuotation PrismOutcome where
  getRef := pure .missing
  withRef _ k := k
  getCurrMacroScope := pure Lean.firstFrontendMacroScope
  getContext := pure `Prism.Chk
  withFreshMacroScope k := k

def ident (s : String) := mkIdent (Lean.Name.mkSimple s)
def varId (s : String) := ident (leanMangleIdent s)
private def levelId (s : String) := ident ("u_" ++ s)
def binderIdent (s : String) : PrismOutcome (TSyntax ``Lean.Parser.Term.binderIdent) := do
  if s == "_" then `(Lean.Parser.Term.binderIdent| _) else return ⟨(varId s).raw⟩

private def symbol (ctx : EmitCtx) (q : QName) : PrismOutcome Term := do
  -- The few StdScope exports implemented as combinators have direct syntax
  -- constructors too. No surface Lean text enters the checker.
  match q.full with
  | ["Agda","Primitive","Prop"] =>
    if ctx.mode == .erasedExec then `(Prop) else .bot "Prop requires Agda verification"
  | ["Data","List","Base","[_]"] => `(fun x => List.cons x List.nil)
  | ["Function","Base","case_of_"] => `(fun x f => f x)
  | ["IO","Base","Main"] => `($(mkIdent `AgdaMirror.AgdaIO) $(mkIdent `AgdaMirror.PolyTop))
  | ["IO","Base","run"] | ["IO","Base","IO","lift"] => `(fun x => x)
  | _ => return mkIdent (← resolveLeanQName ctx q).toName

def reference (ctx : EmitCtx) (q : QName) : PrismOutcome Term := do
  let alts := (q.full :: q.canonAlts).eraseDups.filterMap fun path =>
    match symbol ctx (mkQ path) with | .translated t => some t.raw | _ => none
  match alts with
  | [] => symbol ctx q
  | [s] => return ⟨s⟩
  | _ => return ⟨Lean.mkNode Lean.choiceKind alts.toArray⟩

def makeBinder (h : Hiding) (names : List String) (ty : Term) : PrismOutcome Binder := do
  let xs := (← names.mapM binderIdent).toArray
  let shell : Binder ← match h with
    | .visible => `(bracketedBinder| (_ : $ty))
    | .hidden => `(bracketedBinder| {_ : $ty})
    | .inst => .bot "instance binder requires Agda"
  return ⟨shell.raw.setArg 1 (Lean.mkNullNode (xs.map (·.raw)))⟩

-- Lean re-elaborates a hole even inside a single bracketed binder. Reference
-- the first binder's inferred type for the rest of an Agda metavariable group.
private def bindGroup (h : Hiding) (xs : List String) (ty : Expr) (domain : Term) :
    PrismOutcome (Array Binder) := do
  if isMetaExpr ty then
    if let x :: y :: ys := xs then
      let anchor := if x == "_" then "_groupDomain" else x
      let first ← makeBinder h [anchor] domain
      let other ← makeBinder h (y :: ys) (← `(type_of% $(varId anchor)))
      return #[first, other]
  return #[← makeBinder h xs domain]

private def literal : Lit → PrismOutcome Term
  | .natL n => `(agda_nat% $(Syntax.mkNatLit n))
  | .strL s => `($(mkIdent `AgdaMirror.Utf8.encode) (agda_chars% $(Syntax.mkStrLit s)))
  | .charL c => `(Char.ofNat $(Syntax.mkNatLit c.toNat))

def fields (ctx : EmitCtx) (fs : List (String × Term)) (inPattern := false) : PrismOutcome (Array (TSyntax ``structInstField)) := do
  let names := fs.map Prod.fst
  let fs ← fs.mapM fun (n, t) => do
    if ctx.mode == .erasedExec && ctx.recMeta.any (fun r => r.isCoind &&
        names.all (r.fields.map Prod.fst |>.contains ·)) then
      let f := ident ("_thunk_" ++ leanMangleIdent n)
      if inPattern then `(structInstField| $f:ident := $t)
      else `(structInstField| $f:ident := agda_exec_arg% $t)
    else
      let f := ident (resolveRecFieldIdent ctx names n)
      if ctx.mode == .erasedExec && !inPattern then
        `(structInstField| $f:ident := agda_exec_arg% $t)
      else `(structInstField| $f:ident := $t)
  return fs.toArray

private def natPat (n : Nat) : PrismOutcome Term := do
  -- Agda 2.6.3 expandLitPattern expands up to 20 successors and rejects larger literals.
  if n > 20 then return ← .syntaxErr s!"natural literal {n} exceeds Agda’s maximum pattern literal 20"
  let mut p ← `(Nat.zero)
  for _ in [:n] do p ← `(Nat.succ $p)
  return p

partial def pattern (ctx : EmitCtx) : Pat → PrismOutcome Term
  | .varP x => return varId x
  | .wildP => `(_)
  | .litP (.natL n) => natPat n
  | .litP (.strL s) => return ⟨(Syntax.mkStrLit s).raw⟩
  | .litP (.charL c) => return ⟨(Syntax.mkCharLit c).raw⟩
  | .asP x p => do
    let p ← pattern ctx p
    `($(varId x):ident@$p)
  | .conP q ps => do
    let head ← reference ctx q
    let mut args := #[]
    let slots := ctx.implicitIndex[q.full]?.getD []
    -- Constructor *patterns* start after the parameters of their datatype.
    let params := ctx.implicitIndex[q.full.dropLast ++ ["__params"]]?
    let mut idx := (params.getD []).length
    for a in ps do
      let p ← pattern ctx a.thing
      match a.hid with
      | .visible => args := args.push p
      | .hidden =>
        if params.isNone || !q.canonAlts.isEmpty then .bot "unresolved hidden constructor pattern"
        if let some n := a.label then
          let some j := slots.findIdx? (· == leanMangleIdent n) | .bot "unknown hidden constructor binder"
          if j < idx then .bot "out-of-order hidden constructor binder"
          idx := j
        let some label := slots[idx]? | .bot "missing hidden constructor binder"
        let arg ← `(namedArgument| ($(ident label):ident := $p))
        args := args.push ⟨arg.raw⟩
        idx := idx + 1
      | .inst => .bot "instance constructor pattern requires Agda"
    if args.isEmpty then return head
    `($head $args*)
  | .recP fs => do
    let fs ← fields ctx (← fs.mapM fun (n,p) => do return (n, ← pattern ctx p)) (inPattern := true)
    `({ $fs:structInstField,* })
  | .dotP _ => if ctx.mode == .erasedExec then `(_) else .bot "dot pattern requires Agda"
  | _ => .bot "projection or absurd subpattern requires Agda"

private def stdLabel (ctx : EmitCtx) (q : List String) (label : String) :=
  if !ctx.modPrefix.isPrefixOf q && (lookupStdModule (String.intercalate "." q.dropLast)).isSome
  then label else leanMangleIdent label

private def levelBinder (e : Expr) := match e with
  | .def_ q => q.full == ["Agda","Primitive","Level"]
  | _ => false

/-- Recognize large, closed values without changing constructor resolution
    for terms with binders, implicit arguments, or overloaded names. -/
private partial def constructorTree (ctx : EmitCtx) (e : Expr) : Option (Nat × Term) := do
  if let .lit (.natL n) := e then
    let .translated t := literal (.natL n) | none
    return (1,t)
  let (.con q,args) := unrollApps e | none
  guard (q.canonAlts.isEmpty && ctx.modPrefix.isPrefixOf q.full && args.all (·.hid == .visible))
  let .translated head := symbol ctx q | none
  let children ← args.mapM (constructorTree ctx ·.thing)
  let size := children.foldl (fun n c => n + c.1) 1
  let terms := children.toArray.map Prod.snd
  if terms.isEmpty then return (size,head)
  let .translated tree := show PrismOutcome Term from `($head $terms*) | none
  return (size,tree)

/-- Build a non-dependent product's type and its value with the same field
    layout. Nested pairs retain their constructor spine for the pattern compiler. -/
private partial def deferredProduct (ctx : EmitCtx) (visit : Expr → PrismOutcome Term)
    (e : Expr) (typePosition : Bool) : PrismOutcome Term := do
  let parts (v : Expr) : Option (QName × Expr × Expr) := do
    let (head, [⟨.visible,_,a⟩,⟨.visible,_,b⟩]) := unrollApps v | none
    let q ← match head with
      | .def_ q => if typePosition && q.full == ["Data","Product","_×_"] then some q else none
      | .con q => if !typePosition && q.full == ["Agda","Builtin","Sigma","_,_"] then some q else none
      | _ => none
    return (q,a,b)
  unless ctx.mode == .erasedExec && !ctx.usesDepSigma do return ← visit e
  let some (q,a,b) := parts e | return ← visit e
  let component (v : Expr) : PrismOutcome Term := do
    if (parts v).isSome then return ← deferredProduct ctx visit v typePosition
    let t ← visit v
    if typePosition then `(agda_exec_defer% $t) else `(agda_exec_field% $t)
  let pair ← reference ctx q
  let left ← component a
  let right ← component b
  `($pair $left $right)

def immediateBinding : Expr → Bool
  | .lit _ | .con _ | .lam .. | .lamT .. | .lamCase _ => true
  | _ => false

def shareBinding (share : Bool) (ann : Option Term) (v : Term) : PrismOutcome (Option Term × Term) := do
  if !share then return (ann,v)
  let ann ← ann.mapM fun t => `(agda_exec_binding_type% $t)
  return (ann, ← `(agda_exec_binding% $v))

partial def expr (ctx : EmitCtx) (lvls : List String) : Expr → PrismOutcome Term
  | .var "_" | .meta_ => `(_)
  | .var x =>
    if ctx.mode == .erasedExec then `(agda_exec_val% $(varId x):ident) else return varId x
  | .con q => do
    if ctx.mode == .erasedExec then
      return ← `(agda_exec_val% $(← reference ctx q))
    if q.canonAlts.isEmpty && q.full == ["Agda","Builtin","Equality","_≡_","refl"] then `(agda_refl%)
    else reference ctx q
  | .def_ q => do
    let t ← reference ctx q
    if ctx.mode == .erasedExec then `(agda_exec_val% $t) else return t
  | .lit (.natL n) => if ctx.mode == .erasedExec then `(($(Syntax.mkNatLit n) : Nat)) else literal (.natL n)
  | .lit (.strL s) => if ctx.mode == .erasedExec then pure ⟨(Syntax.mkStrLit s).raw⟩ else literal (.strL s)
  | .lit l => literal l
  | .set n => do
    let l : TSyntax `level := ⟨(Syntax.mkNatLit n).raw⟩
    `(Type $l)
  | .hole => .syntaxErr "unsolved interaction hole"
  | .dot e => expr ctx lvls e
  | .absurdLam .visible => `(fun x => nomatch x)
  | .absurdLam .hidden => `(fun {x} => nomatch x)
  | .absurdLam .inst => .bot "instance lambda requires Agda"
  | .lamCase cs => do
    if ctx.mode != .erasedExec then .bot "extended lambda requires Agda"
    let mut arms := #[]
    let mut inspected := #[]
    for .clause l r ws in cs do
      if r matches .absurdRHS then continue
      let .head _ ps := l | .bot "copattern in extended lambda"
      let .rhs body := r | .bot "with in extended lambda"
      unless ws.isEmpty do .bot "local declarations in extended lambda"
      let used := collectVarsExpr body
      let pats ← (ps.filter (·.hid == .visible)).toArray.mapM fun a => pattern ctx (wildcardUnusedPat used a.thing)
      inspected := inspected.push ((ps.filter (·.hid == .visible)).map fun a =>
        match a.thing with | .varP _ | .wildP => false | _ => true)
      let t ← expr ctx lvls body
      arms := arms.push (← `(matchAltExpr| | $pats:term,* => $t))
    if arms.isEmpty then return ← `(fun x => nomatch (agda_exec_head% x))
    let vars := (List.range (inspected[0]?.getD []).length).toArray.map fun k => ident ("lambdaPort" ++ toString k)
    let discrs ← vars.zipIdx.mapM fun (v,k) => do
      let t ← if inspected.any (fun cols => cols[k]? == some true) then `(agda_exec_head% $v:ident) else pure (v : Term)
      `(matchDiscr| $t:term)
    `(fun $vars:ident* => match $discrs:matchDiscr,* with $arms:matchAlt*)
  | e@(.app ..) => do
    let (h, args) := unrollApps e
    let path := match h with | .con q | .def_ q => q.full | _ => []
    let args := if ctx.mode == .erasedExec then projectInstances (ctx.instanceSlots[path]?.getD []) args else args
    if args.isEmpty then return ← expr ctx lvls h
    if ctx.mode == .erasedExec then
      if let .def_ q := h then
        let vs := args.filter (·.hid == .visible)
        match q.full, vs with
        | ["Data","Bool","Base","if_then_else_"], [c,l,r] =>
          let test ← expr ctx lvls c.thing
          let lhs ← expr ctx lvls l.thing
          let rhs ← expr ctx lvls r.thing
          return ← `(match $test:term with | Bool.true => $lhs | Bool.false => $rhs)
        | ["Data","Bool","Base","_∧_"], [l,r] =>
          let lhs ← expr ctx lvls l.thing
          let rhs ← expr ctx lvls r.thing
          return ← `(match $lhs:term with | Bool.true => $rhs | Bool.false => Bool.false)
        | ["Data","Bool","Base","_∨_"], [l,r] =>
          let lhs ← expr ctx lvls l.thing
          let rhs ← expr ctx lvls r.thing
          return ← `(match $lhs:term with | Bool.true => Bool.true | Bool.false => $rhs)
        | _, _ => pure ()
    if ctx.mode != .erasedExec && (h matches .con _) then
      if let some (size,t) := constructorTree ctx e then
        if size >= 24 then return ← `(agda_ground% $t)
    -- The scalar list of an authored literal is already decoded. On this
    -- closed input the UTF-8 roundtrip computes to precisely these scalars.
    if let (.def_ q, [⟨.visible, _, .lit (.strL literal)⟩]) := (h,args) then
      if ctx.mode != .erasedExec && q.full == ["Agda","Builtin","String","primStringToList"] &&
          ctx.symIndex[q.full]?.any (·.leanName == "AgdaMirror.agdaToList") then
        return ← `(agda_chars% $(Syntax.mkStrLit literal))
    if let (.set 0, [⟨.visible, _, .var u⟩]) := (h, args) then
      if lvls.contains u then
        let l : TSyntax `level := ⟨(levelId u).raw⟩
        return ← `(Type $l)
    let q := match h with | .def_ q | .con q => q.full | _ => []
    let hd ← match h with
      | .con q | .def_ q => reference ctx q
      | .var x => if ctx.mode == .erasedExec then `(agda_exec_head% $(varId x):ident) else expr ctx lvls h
      | _ => expr ctx lvls h
    let mut acc : Array Term := #[]
    let mut idx := 0
    for a in args do
      let t ← expr ctx lvls a.thing
      match a.hid with
      | .visible =>
        acc := acc.push (← if ctx.mode == .erasedExec then `(agda_exec_arg% $t) else pure t)
      | .hidden =>
        let label := a.label.map (stdLabel ctx q) <|> (ctx.implicitIndex[q]? >>= (·[idx]?))
        let some lab := label | .bot "unknown implicit argument label"
        if lab == "_" then .bot "positional implicit argument lacks a label"
        let arg ← `(namedArgument| ($(ident lab):ident := $t))
        acc := acc.push ⟨arg.raw⟩
        idx := idx+1
      | .inst => .bot "instance application requires Agda"
    let t ← `($hd $acc*)
    if ctx.mode == .erasedExec then `(agda_exec_val% $t) else return t
  | .lam a body => do
    let b ← makeBinder a.hid [a.thing] (← `(_))
    let t ← expr ctx lvls body
    `(fun $(⟨b.raw⟩):funBinder => $t)
  | .lamT (.bind h xs ty) body => do
    let dom ← expr ctx lvls ty
    let bs := (← bindGroup h xs ty dom).map fun b => (⟨b.raw⟩ : TSyntax ``funBinder)
    let t ← expr ctx lvls body
    let strict ← `(fun $bs:funBinder* => $t)
    if ctx.mode != .erasedExec || h != .visible then return strict
    let lazyBs := (← bindGroup h xs ty (← `(agda_exec_defer% $dom))).map fun b => (⟨b.raw⟩ : TSyntax ``funBinder)
    let lazyFn ← `(fun $lazyBs:funBinder* => $t)
    `(agda_exec_fun% ($strict) ($lazyFn))
  | .pi (.bind h xs ty) body => do
    if levelBinder ty then return ← expr ctx (xs ++ lvls) body
    let bs ← bindGroup h xs ty (← expr ctx lvls ty)
    let mut t ← expr ctx lvls body
    for b in bs.reverse do t ← `($b:bracketedBinder → $t)
    return t
  | .fun_ a body => do
    let dom ← expr ctx lvls a.thing
    let t ← expr ctx lvls body
    if a.hid == .visible then `($dom → $t)
    else
      let b ← makeBinder a.hid ["_"] dom
      `($b:bracketedBinder → $t)
  | .let_ bs body => do
    let mut t ← expr ctx lvls body
    for b in bs.reverse do
      match b with
      | .letBind x ty val =>
        if ctx.mode != .erasedExec && isMetaExpr ty && mentionsQName ["Agda","Builtin","Sigma","_,_"] val then
          .bot "untyped dependent pair in let requires Agda"
        let v ← if isMetaExpr ty then deferredProduct ctx (expr ctx lvls) val false
                else expr ctx lvls val
        let ann ← if isMetaExpr ty then pure none else some <$> deferredProduct ctx (expr ctx lvls) ty true
        let (ann,v) ← shareBinding (ctx.mode == .erasedExec && !immediateBinding val) ann v
        t ← `(let $(varId x):ident $[: $ann]? := $v; $t)
      | .letPat p val =>
        let v ← expr ctx lvls val
        let p ← pattern ctx p
        t ← `(match $v:term with | $p => $t)
    return t
  | .recUpd src fs => do
    let src ← expr ctx lvls src
    let fs ← fields ctx (← fs.mapM fun (n, v) => do return (n, ← expr ctx lvls v))
    `({ $src with $fs:structInstField,* })
  | .rec_ fs => do
    let fs ← fields ctx (← fs.mapM fun (n, v) => do return (n, ← expr ctx lvls v))
    `({ $fs:structInstField,* })

def execTypeAlias (ctx : EmitCtx) (lvls : List String) (ty : Expr) : PrismOutcome Term :=
  deferredProduct ctx (expr ctx lvls) ty true

private partial def lazyProductPattern : Pat → Bool
  | .varP _ | .wildP => true
  | .asP _ p => lazyProductPattern p
  | .conP q ps => q.full == ["Agda","Builtin","Sigma","_,_"] && ps.all (lazyProductPattern ·.thing)
  | _ => false

private def hasProductPattern (clauses : List Clause) (pos : Nat) : Bool := Id.run do
  for .clause l _ _ in clauses do
    let .head _ ps := l | return false
    let some a := (ps.filter (·.hid == .visible))[pos]? | return false
    unless lazyProductPattern a.thing do return false
  return !clauses.isEmpty

/-- Materialize a function telescope from its formal port colors. -/
partial def execSignature (ctx : EmitCtx) (lvls : List String) (ty : Expr)
    (colors : List CatStructure.EvalColor) (clauses : List Clause := []) (visible : Nat := 0) :
    PrismOutcome Term := do
  let callbackType (dom : Expr) :=
    ((dom matches .fun_ ..) || (dom matches .pi ..)) && !CatStructure.erasedDomain dom
  let callback (dom : Expr) := execSignature ctx lvls dom (CatStructure.executionPorts dom []).toList
  match ty with
  | .fun_ a body =>
    let dom ← if a.hid == .visible && callbackType a.thing then callback a.thing
              else if a.hid == .visible && hasProductPattern clauses visible then execTypeAlias ctx lvls a.thing
              else expr ctx lvls a.thing
    let dom ← if colors.head? == some .thunked then `(agda_exec_defer% $dom) else pure dom
    let rest ← execSignature ctx lvls body (colors.drop 1) clauses (visible + (if a.hid == .visible then 1 else 0))
    if a.hid == .visible then `($dom → $rest)
    else
      let b ← makeBinder a.hid ["_"] dom
      `($b:bracketedBinder → $rest)
  | .pi (.bind h xs t) body =>
    let next := if h == .visible then visible + xs.length else visible
    let mut rest ← execSignature ctx lvls body (colors.drop xs.length) clauses next
    if levelBinder t then return rest
    let dom ← if h == .visible && callbackType t then callback t else expr ctx lvls t
    for (x,i) in xs.zipIdx.reverse do
      let d ← if colors[i]? == some .thunked then `(agda_exec_defer% $dom) else pure dom
      let b ← makeBinder h [x] d
      rest ← `($b:bracketedBinder → $rest)
    return rest
  | _ => execTypeAlias ctx lvls ty

def declName (ctx : EmitCtx) (n : String) (lvls : List String := []) : PrismOutcome IdDecl := do
  let nm := mkIdent <| (Lean.Name.mkSimple (leanModNamespace ctx.modPrefix)) ++ n.toName
  if lvls.isEmpty then `(declId| $nm:ident)
  else
    let us := lvls.toArray.map levelId
    `(declId| $nm:ident.{$us:ident,*})

def telescope (ctx : EmitCtx) (lvls : List String) (params : List Bind) : PrismOutcome (Array Binder) := do
  let mut bs := #[]
  for .bind h xs ty in params do
    if !levelBinder ty then bs := bs ++ (← bindGroup h xs ty (← expr ctx lvls ty))
  return bs

def splitHidden : Expr → List Bind × Expr
  | .pi b@(.bind .hidden _ _) body =>
    let (bs, r) := splitHidden body
    (b :: bs, r)
  | e => ([], e)

def aliasLets (formals : List String) (ps : List (Arg Pat)) (body : Term) : PrismOutcome Term := do
  let mut idx := 0
  let mut aliases := #[]
  for p in ps do
    if p.hid != .hidden then .bot "instance clause binder requires Agda"
    if let some lab := p.label then
      let some j := formals.findIdx? (· == lab) | .bot "unknown named implicit pattern"
      idx := j
    let some slot := formals[idx]? | .bot "unknown positional implicit pattern"
    match p.thing with
    | .varP x => if x != slot && slot != "_" then aliases := aliases.push (x,slot)
    | .wildP => pure ()
    | _ => .bot "implicit constructor pattern requires Agda"
    idx := idx + 1
  let mut t := body
  for (x,y) in aliases.reverse do t ← `(let $(varId x):ident := $(varId y); $t)
  return t

private partial def clauseBody (ctx : EmitCtx) (lvls : List String) (body : Expr) : List Decl → PrismOutcome Term
  | [] => expr ctx lvls body
  | .open_ .. :: ds | .import_ .. :: ds | .fixity .. :: ds => clauseBody ctx lvls body ds
  | .sig _ n ty :: .fun_ _ m [.clause (.head q ps) (.rhs v) []] :: ds => do
    if n != m || mentionsQName q.full v then .bot "recursive where clause requires Agda"
    let nm := varId ("where_" ++ n)
    let mut rhs ← expr ctx lvls v
    for a in ps.reverse do
      let .varP x := a.thing | .bot "where pattern requires Agda"
      if a.hid != .visible then .bot "implicit where pattern requires Agda"
      rhs ← `(fun $(varId x):ident => $rhs)
    let sym : SymInfo := ⟨n,q.full,.defSym,defaultAgdaFixity,nm.getId.toString,0⟩
    let inner ← clauseBody (ctx.withLocal sym) lvls body ds
    let ann ← if isMetaExpr ty then pure none else some <$> expr ctx lvls ty
    `(let $nm:ident $[: $ann]? := $rhs; $inner)
  | _ => .bot "complex where clause requires Agda"

private def eqCore := ["Relation","Binary","PropositionalEquality","Core"]

private def strLit? : Expr → Bool | .lit (.strL _) => true | _ => false

/-- During checking of a congruence the result of the function is compared
    before the proof argument can instantiate the endpoints. An open primitive
    String append is stuck in Agda; its ByteArray representation is opaque to
    that conversion. Propagate each known endpoint through transitivity. -/
private partial def checkEndpoints (lhs rhs : Option Expr) (proof : Expr) : PrismOutcome Unit := do
  let (.def_ q, args) := unrollApps proof | return ()
  let vs := args.filter (·.hid == .visible) |>.map (·.thing)
  if q.full == eqCore ++ ["trans"] then
    if let [p₁,p₂] := vs then
      checkEndpoints lhs none p₁
      checkEndpoints none rhs p₂
  if q.full == eqCore ++ ["cong"] && (lhs.any strLit? || rhs.any strLit?) then
    if let [fn, _] := vs then
      let lambda := match fn with
        | .lam a body => some (a.thing,body)
        | .lamT (.bind _ [x] _) body => some (x,body)
        | _ => none
      let some (x,body) := lambda | return ()
      let (.def_ f, operands) := unrollApps body | return ()
      let appends := [["Data","String","Base","_++_"], ["Agda","Builtin","String","primStringAppend"]]
      if appends.contains f.full && operands.any (fun op => (collectVarsExpr op.thing).contains x) then
        -- Explicit endpoints fix this metavariable before the proof is checked.
        let mut supplied := []
        let mut idx := 0
        let slots := ["A", "B", "x", "y"]
        for arg in args do
          if arg.hid == .hidden then
            let slot := arg.label.getD (slots[idx]?.getD "")
            unless isMetaExpr arg.thing do supplied := slot :: supplied
            idx := (slots.findIdx? (· == slot)).getD idx + 1
        if (lhs.any strLit? && !supplied.contains "x") || (rhs.any strLit? && !supplied.contains "y") then
          .syntaxErr "Agda conversion blocked: neutral primStringAppend against a String literal"

private def resultType : Expr → Expr
  | .pi _ b | .fun_ _ b => resultType b
  | e => e

private def verifyConversion (ty proof : Expr) : PrismOutcome Unit := do
  let (.def_ q, args) := unrollApps (resultType ty) | return ()
  if q.full == ["Agda","Builtin","Equality","_≡_"] then
    if let [l,r] := args.filter (·.hid == .visible) then checkEndpoints l.thing r.thing proof

private def unpackRewrite : RHS → PrismOutcome (List Expr × Expr)
  | .rhs e => pure ([],e)
  | .rewriteRHS ps (.rhs body) => pure (ps,body)
  | _ => .bot "with or nested rewrite clause requires Agda"

private def factorRules (ctx : EmitCtx) : PrismOutcome (Array Ident) :=
  ctx.factoredEquations.toArray.mapM fun path => do
    return mkIdent (← resolveLeanQName ctx (mkQ path)).toName

/-- Each rewrite transports the expected type using the actual equality proof.
    Unfold the head of an equality endpoint if its defining clause exposes the
    redex. The final exact always checks the authored right-hand side. -/
private def rewriteBody (ctx : EmitCtx) (lvls : List String) (ty : Expr) (eqs : List Expr) (body : Term) :
    PrismOutcome Term := do
  if eqs.isEmpty then return body
  let (.def_ eq, endpoints) := unrollApps (resultType ty) | .bot "dependent rewrite requires Agda"
  if eq.full != ["Agda","Builtin","Equality","_≡_"] then .bot "dependent rewrite requires Agda"
  let mut heads ← factorRules ctx
  for a in endpoints do
    if let .def_ q := (unrollApps a.thing).1 then
      if ctx.modPrefix.isPrefixOf q.full then
        let id := mkIdent (← resolveLeanQName ctx q).toName
        unless heads.any (·.getId == id.getId) do heads := heads.push id
  let mut steps := #[]
  for p in eqs do
    if !ctx.factoredEquations.isEmpty then
      if let .var x := p then
        let h := varId x
        steps := steps.push (← `(tactic| try simp only [$[$heads:ident],*] at $h:ident ⊢))
    let proof ← expr ctx lvls p
    let eqProof ← `($(mkIdent `AgdaMirror.agdaIdToEq) $proof)
    let direct ← if heads.isEmpty then `(tactic| rewrite [$eqProof:term]) else
      `(tactic| first | rewrite [$eqProof:term] | rewrite (config := {transparency := .default}) [$eqProof:term] | (try dsimp only [$[$heads:ident],*]; rewrite (config := {transparency := .default}) [$eqProof:term]))
    let h := ident "_agdaRewriteEq"
    let exposed ← `(tactic| (
      have $h:ident := $eqProof:term
      set_option smartUnfolding false in conv at $h:ident => lhs; whnf
      set_option smartUnfolding false in conv => arg 1; whnf
      set_option smartUnfolding false in conv => arg 2; whnf
      rewrite (config := {transparency := .default}) [$h:ident]))
    let target ← `(tactic| (
      set_option smartUnfolding false in conv => arg 1; whnf
      rewrite (config := {transparency := .default}) [$eqProof:term]))
    steps := steps.push (← `(tactic| first | $direct:tactic | $target:tactic | $exposed:tactic))
  steps := steps.push (← `(tactic| exact $body))
  `(by $[$steps:tactic];*)

private abbrev domains := CatStructure.portDomains

/-- Equation alternatives include implicit discriminants in binder order. Agda
    patterns can omit them, including intervening fields of a named telescope. -/
private def alignDiscriminants : List (Arg Expr) → List (Arg Pat) → PrismOutcome (List (Arg Pat))
  | _, [] => pure []
  | [], _ => .bot "interleaved patterns extend past the function telescope"
  | d :: ds, ps@(p :: tail) => do
    if d.hid == .hidden && (p.hid == .visible || p.label.any (fun n => d.label != some n)) then
      return ⟨.hidden, none, .wildP⟩ :: (← alignDiscriminants ds ps)
    if d.hid != p.hid || d.hid == .inst then .bot "inconsistent equation telescope"
    return p :: (← alignDiscriminants ds tail)

/-- Match a computation together with a named equality about its result. Keep
    the branch equation so both the proof's type and the goal compute under
    the same constructor. The second pattern eliminates that very proof. -/
private def equalityWith (ctx : EmitCtx) (lvls : List String) (parent : LHS)
    (ty : Expr) (targets : List Expr) (clauses : List Clause) : PrismOutcome Term := do
  let [scrutinee, .var witness] := targets | .bot "paired with needs a named equality"
  let .head _ ps := parent | .bot "nested equality split requires Agda"
  let binders := domains ty
  unless ps.all (·.hid == .visible) && binders.all (·.hid == .visible) do
    .bot "paired with has a hidden argument"
  let some i := ps.findIdx? (fun p => match p.thing with | .varP x => x == witness | _ => false)
    | .bot "with equality is not a parent argument"
  let some binder := binders[i]? | .bot "with equality outside telescope"
  let (.def_ eq, endpoints) := unrollApps binder.thing | .bot "paired with needs an equality"
  unless eq.full == ["Agda","Builtin","Equality","_≡_"] do .bot "paired with needs an equality"
  let h := varId witness
  let branchEq := ident "_agdaWithEq"
  let goalArgs := (unrollApps (resultType ty)).2
  let mut rules ← factorRules ctx
  for e in scrutinee :: (endpoints ++ goalArgs).map (·.thing) do
    if let .def_ q := (unrollApps e).1 then
      if ctx.modPrefix.isPrefixOf q.full then
        let rule := mkIdent (← resolveLeanQName ctx q).toName
        unless rules.any (·.getId == rule.getId) do rules := rules.push rule
  let simplify ← `(tactic| (try simp only [$[$rules:ident],*] at $branchEq:ident;
                            try simp only [$[$rules:ident],*, $branchEq:ident] at $h:ident ⊢))
  let mut arms := #[]
  for .clause lhs rhs wheres in clauses do
    let .with_ base [⟨.visible, _, p@(.conP ..)⟩, ⟨.visible, _, proofPat⟩] [] := lhs
      | .bot "paired with needs two evidence patterns"
    unless encLHS base == encLHS parent && wheres.isEmpty do .bot "refined outer equality telescope"
    let p ← pattern ctx p
    let body ← match proofPat, rhs with
      | .conP ctor [], .rhs b => do
        unless ctor.full == ["Agda","Builtin","Equality","_≡_","refl"] && ctor.canonAlts.isEmpty do
          .bot "paired with needs a reflexivity pattern"
        verifyConversion ty b
        let v ← expr ctx lvls b
        `(by $simplify:tactic; cases $(mkIdent `AgdaMirror.agdaIdToEq) $h:ident; exact $v)
      | .absurdP, .absurdRHS => `(by $simplify:tactic; exact nomatch $h:ident)
      | _, _ => .bot "paired with needs a reflexivity or absurd equality pattern"
    arms := arms.push (← `(matchAltExpr| | $p => $body))
  let t ← expr ctx lvls scrutinee
  `(match $branchEq:ident : $t:term with $arms:matchAlt*)

/-- Match an Agda decision while retaining its equation. A dependent branch
    may rewrite its goal by the equation and by the proof named in the source. -/
private def decisionWith (ctx : EmitCtx) (lvls : List String) (parent : LHS)
    (ty : Expr) (targets : List Expr) (clauses : List Clause) : PrismOutcome Term := do
  let [scrutinee] := targets | .bot "dependent decision needs a single scrutinee"
  let (.def_ equality, endpoints) := unrollApps (resultType ty)
    | .bot "dependent decision needs an equality result"
  unless equality.full == ["Agda","Builtin","Equality","_≡_"] do
    .bot "dependent decision needs an equality result"
  let branchEq := ident "_agdaWithEq"
  let mut rules ← ctx.factoredWalks.toArray.mapM fun path => do
    return mkIdent (← resolveLeanQName ctx (mkQ path)).toName
  for a in endpoints do
    if let .def_ q := (unrollApps a.thing).1 then
      if ctx.modPrefix.isPrefixOf q.full then
        rules := rules.push (mkIdent (← resolveLeanQName ctx q).toName)
  rules := rules.push branchEq
  let discr ← expr ctx lvls scrutinee
  let mut arms := #[]
  for .clause lhs rhs wheres in clauses do
    let .with_ base [⟨.visible, _, p@(.conP q _)⟩] [] := lhs | .bot "dependent decision pattern"
    unless encLHS base == encLHS parent && wheres.isEmpty &&
        (q.full == ["Relation","Nullary","yes"] || q.full == ["Relation","Nullary","no"]) do
      .bot "dependent split needs decision constructors"
    let (proofs, b) ← unpackRewrite rhs
    verifyConversion ty b
    let rhs ← if let .con q := b then reference ctx q else expr ctx lvls b
    let value ← rewriteBody ctx lvls ty proofs rhs
    let pat ← pattern ctx p
    let mut normalizations := #[]
    for proof in proofs do
      if let .var x := proof then
        let h := varId x
        normalizations := normalizations.push (← `(tactic| try dsimp only [$[$rules:ident],*] at $h:ident))
    let tacs := #[← `(tactic| try simp only [$[$rules:ident],*])] ++ normalizations ++ #[← `(tactic| exact $value)]
    arms := arms.push (← `(matchAltExpr| | $pat => by $[$tacs:tactic];*))
  `(match $branchEq:ident : $discr:term with $arms:matchAlt*)

/-- A boolean with-split can refine an equality argument into an absurd pattern.
    Name the scrutinee equation and transport the *authored* argument and goal
    through it in both branches before checking the branch term. -/
private def refinedBoolWith (ctx : EmitCtx) (lvls : List String) (parent : LHS)
    (ty : Expr) (targets : List Expr) (clauses : List Clause) : PrismOutcome Term := do
  let [scrutinee] := targets | .bot "dependent multi-scrutinee with requires Agda"
  let .head name outer := parent | .bot "extended with parent requires Agda"
  let some (.clause (.with_ (.head _ impossible) _ []) .absurdRHS []) :=
    clauses.find? (fun | .clause _ .absurdRHS [] => true | _ => false)
    | .bot "dependent with needs a refined argument"
  let some pos := impossible.findIdx? (fun a => a.thing matches .absurdP)
    | .bot "dependent with needs a named absurd argument"
  let some ⟨hid, label, .varP x⟩ := outer[pos]? | .bot "refined with argument must be a variable"
  let hyp := varId x
  let syntheticEq := ident "_agdaWithEq"
  let discr ← expr ctx lvls scrutinee
  let scrutineeHead := resultHeadCanon scrutinee
  let mut rules : Array Ident := #[mkIdent `AgdaMirror.agdaOr, mkIdent `AgdaMirror.agdaIte]
  for path in (collectExprQNames ty).eraseDups do
    if some path != scrutineeHead then
      if let some f := ctx.symIndex[path]? then
        if f.kind == .defSym then rules := rules.push (mkIdent f.leanName.toName)
  rules := rules.push syntheticEq
  let simplify ← `(tactic| simp only [$[$rules:ident],*] at $hyp:ident ⊢)
  let mut arms := #[]
  for .clause lhs rhs wheres in clauses do
    let .with_ (.head f nested) [⟨.visible, _, .conP ctor []⟩] [] := lhs
      | .bot "dependent with needs boolean constructor patterns"
    unless f.full == name.full && wheres.isEmpty && nested.length == outer.length &&
        (ctor.full == ["Agda","Builtin","Bool","Bool","true"] ||
         ctor.full == ["Agda","Builtin","Bool","Bool","false"]) do
      .bot "dependent with telescope requires Agda"
    let pat ← reference ctx ctor
    let body ← match rhs with
      | .rhs b => do
        unless encLHS (.head f nested) == encLHS parent do .bot "dependent with refines a live argument"
        verifyConversion ty b
        expr ctx lvls b
      | .absurdRHS => do
        let expected := outer.set pos ⟨hid, label, .absurdP⟩
        unless encLHS (.head f nested) == encLHS (.head name expected) do
          .bot "dependent with refines multiple arguments"
        `(nomatch $hyp:ident)
      | _ => .bot "nested dependent with needs Agda"
    let arm ← `(matchAltExpr| | $pat => by $simplify:tactic; exact $body)
    arms := arms.push arm
  `(match $syntheticEq:ident : $discr:term with $arms:matchAlt*)

/-- A with-abstraction that leaves the parent telescope intact is an ordinary
    match. Compare the complete parent patterns before exposing its variables. -/
private partial def withBody (ctx : EmitCtx) (lvls : List String) (parent : LHS)
    (result : Expr) (targets : List Expr) (clauses : List Clause) : PrismOutcome Term := do
  if targets.isEmpty || clauses.isEmpty then .bot "empty with-abstraction"
  let mut arms := #[]
  for .clause lhs r ws in clauses do
    let .with_ base ps [] := lhs | .bot "extended with-clause needs Agda"
    if encLHS base != encLHS parent || ps.length != targets.length || ps.any (·.hid != .visible) then
      .bot "refinement of the enclosing with telescope needs Agda"
    let value ← match r with
      | .rhs body => do
        verifyConversion result body
        clauseBody ctx lvls body ws
      | .withRHS es cs => do
        unless ws.isEmpty do .bot "nested with-local declarations need Agda"
        withBody ctx lvls lhs result es cs
      | _ => .bot "dependent with branch needs Agda"
    let used := collectVarsRhs r ++ ws.flatMap collectVarsDecl
    let pats := (← ps.mapM fun p => pattern ctx (wildcardUnusedPat used p.thing)).toArray
    arms := arms.push (← `(matchAltExpr| | $pats:term,* => $value))
  let scrutinees ← targets.toArray.mapM fun e => do
    let t ← expr ctx lvls e
    `(matchDiscr| $t:term)
  `(match $scrutinees:matchDiscr,* with $arms:matchAlt*)

/-- Lean's noConfusion compilation of a literal Nat equality may use
    propext. For two closed literals, the kernel reduces Nat's constructive
    decision procedure directly. Equal literals cannot supply this refutation. -/
private def absurdElim (pat : Option Pat) (domain : Option (Arg Expr)) (h : Ident) : PrismOutcome Term := do
  if let (some .absurdP, some d) := (pat, domain) then
    let (head,args) := unrollApps d.thing
    if let .def_ q := head then
      if q.full == ["Agda","Builtin","Equality","_≡_"] && q.canonAlts.isEmpty then
        if let [Expr.lit (.natL a), Expr.lit (.natL b)] := (args.filter (·.hid == .visible)).map (·.thing) then
          if a != b then
            let x := Syntax.mkNatLit a
            let y := Syntax.mkNatLit b
            return ← `(False.elim ((of_decide_eq_true rfl : ($x:num : Nat) ≠ $y:num)
              ($(mkIdent `AgdaMirror.agdaIdToEq) $h:ident)))
  `(nomatch $h:ident)

/-- Preserve the enclosing patterns and eliminate the particular absurd
    discriminant. For Agda equality, a refl pattern can refine the parameter
    on its left as well as its index on the right. Transport along the actual
    equality before checking that the absurd argument has no constructors. -/
private def absurdArm (ctx : EmitCtx) (slots : List String) (result : Expr) (ps : List (Arg Pat)) :
    PrismOutcome (TSyntax ``matchAltExpr) := do
  let (hp,vp) := ps.span (·.hid != .visible)
  if vp.any (·.hid != .visible) || hasInterleavedImplicitBeforeK vp.length result then
    .bot "interleaved absurd clause requires Agda"
  let some pos := vp.findIdx? (fun a => (replaceFirstAbsurdPat a.thing).isSome)
    | .bot "missing absurd pattern"
  let mut pats := #[]
  let mut steps := #[]
  for (a,i) in vp.zipIdx do
    if let .conP q [] := a.thing then
      if q.full == ["Agda","Builtin","Equality","_≡_","refl"] && q.canonAlts.isEmpty then
        let h := ident ("reflPattern" ++ toString i)
        steps := steps.push (← `(tactic| cases $(mkIdent `AgdaMirror.agdaIdToEq) $h:ident))
        pats := pats.push (h : Term)
        continue
    let p := if i == pos then (replaceFirstAbsurdPat a.thing).getD a.thing else a.thing
    pats := pats.push (← pattern ctx (wildcardUnusedPat ["_abs_bot"] p))
  let elim ← absurdElim (vp[pos]?.map (·.thing)) ((domains result).filter (·.hid == .visible))[pos]? (varId "_abs_bot")
  let t ← if steps.isEmpty then pure elim else do
    steps := steps.push (← `(tactic| exact $elim))
    `(by $[$steps:tactic];*)
  let rhs ← aliasLets slots hp t
  `(matchAltExpr| | $pats:term,* => $rhs)

private def function (ctx : EmitCtx) (name leanName : String) (sigTy : Expr) (cs : List Clause)
    (structural : Option Nat := none) : PrismOutcome Cmd := do
  let recInfo ← if let some i := structural then pure (.structuralArg i) else analyzeFunctionRecursion ctx.modPrefix name cs
  let lvls := collectLevelVarsInType sigTy
  let (hidden, result) := splitHidden sigTy
  let slots := hidden.flatMap fun (.bind _ xs ty) => if levelBinder ty then [] else xs
  let bs ← telescope ctx lvls hidden
  let nm ← declName ctx leanName lvls
  let ann ← if isMetaExpr result then pure none else some <$> expr ctx lvls result
  let mut arms : Array (TSyntax ``matchAlt) := #[]
  let mut arity : Option Nat := none
  let live := cs.filter fun (.clause _ r _) => match r with | .absurdRHS => false | _ => true
  for .clause l r ws in cs do
    let .head _ ps := l | .bot "copattern or with clause requires Agda"
    if let .absurdRHS := r then
      if !ws.isEmpty then .bot "absurd clause with local declarations requires Agda"
      arms := arms.push ⟨(← absurdArm ctx slots result ps).raw⟩
      continue
    if let .withRHS es branches := r then
      if !ws.isEmpty then
        .bot "dependent with telescope needs Agda"
      let (hp,vp) := ps.span (·.hid != .visible)
      if vp.length > ((domains result).filter (·.hid == .visible)).length ||
          vp.any (·.hid != .visible) || hasInterleavedImplicitBeforeK vp.length result ||
          arity.any (· != vp.length) then .bot "interleaved with telescope needs Agda"
      arity := some vp.length
      let dependent := !(collectVarsExpr (resultType result)).isEmpty
      let body ← if dependent then
        if es.length == 2 then equalityWith ctx lvls l result es branches
        else if branches.any (fun | .clause _ .absurdRHS _ => true | _ => false) then
          refinedBoolWith ctx lvls l result es branches
        else decisionWith ctx lvls l result es branches
      else withBody ctx lvls l result es branches
      let rhs ← aliasLets slots hp body
      if vp.isEmpty then
        unless cs.length == 1 do .bot "overlapping nullary with clauses"
        return ← `(noncomputable def $nm:declId $bs:bracketedBinder* $[: $ann]? := $rhs)
      let pats := (← vp.mapM fun p => pattern ctx (if dependent then p.thing else wildcardUnusedPat (collectVarsRhs r) p.thing)).toArray
      arms := arms.push (← `(matchAltExpr| | $pats:term,* => $rhs))
      continue
    let (eqs,body) ← unpackRewrite r
    if !ws.isEmpty && live.length != 1 then .bot "complex local declarations require Agda"
    let (hp, vp) := ps.span (·.hid != .visible)
    let vp ← if vp.any (·.hid != .visible) || hasInterleavedImplicitBeforeK vp.length result then
      alignDiscriminants (domains result) vp
    else pure vp
    if arity.any (· != vp.length) then .bot "varying clause arities require Agda"
    arity := some vp.length
    verifyConversion result body
    let t ← if !eqs.isEmpty && ws.isEmpty then
      if let .con q := body then reference ctx q else expr ctx lvls body
    else clauseBody ctx lvls body ws
    let rhs ← aliasLets slots hp (← rewriteBody ctx lvls result eqs t)
    let typeAlias := (match recInfo with | .nonRecursive => true | _ => false) &&
      (codomainIsSet result || isMetaExpr result && looksLikeTypeRhs body) &&
      cs.length == 1 && ps.all (fun a => match a.thing with | .varP _ | .wildP => true | _ => false)
    if vp.isEmpty then
      if live.length != 1 then .bot "overlapping nullary clauses"
      if typeAlias then return ← `(abbrev $nm:declId $bs:bracketedBinder* $[: $ann]? := $rhs)
      return ← `(noncomputable def $nm:declId $bs:bracketedBinder* $[: $ann]? := $rhs)
    let used := eqs.flatMap collectVarsExpr ++ collectVarsExpr body ++ ws.flatMap collectVarsDecl
    let ps := (← vp.mapM fun a => pattern ctx (wildcardUnusedPat used a.thing)).toArray
    arms := arms.push (← `(matchAltExpr| | $ps:term,* => $rhs))
    if typeAlias then return ← `(abbrev $nm:declId $bs:bracketedBinder* $[: $ann]? $arms:matchAlt*)
  match recInfo with
  | .nonRecursive =>
    `(noncomputable def $nm:declId $bs:bracketedBinder* $[: $ann]? $arms:matchAlt*)
  | .structuralArg i =>
    let vars := (List.range (arity.getD 0)).toArray.map fun j => ident ("recArg" ++ toString j)
    let visible := ((domains result).take vars.size).zipIdx.filter fun (d,_) => d.hid == .visible
    let position := (visible[i]?.map Prod.snd).getD i
    let some v := vars[position]? | .bot "structural parameter outside clause"
    `(noncomputable def $nm:declId $bs:bracketedBinder* $[: $ann]? $arms:matchAlt*
      termination_by structural $vars:ident* => $v)

private def axiomCmd (ctx : EmitCtx) (name : String) (ty : Expr) : PrismOutcome Cmd := do
  if isMetaExpr ty then .bot "boundary declaration requires an explicit signature"
  let lvls := collectLevelVarsInType ty
  let nm ← declName ctx name lvls
  let (hidden, rest) := splitHidden ty
  let bs ← telescope ctx lvls hidden
  let t ← expr ctx lvls rest
  `(axiom $nm:declId $bs:bracketedBinder* : $t)

def unit (ctx : EmitCtx) (u : ModUnit) (structural : Option Nat := none) : PrismOutcome Cmd := do
  match u.kind with
  | .funUnit m n ty cs =>
    if m.termCheck != .check then .bot "termination pragma requires Agda"
    function ctx n (leanMangleIdent n) ty cs structural
  | .anonUnit i ty cs => function ctx "_" ("_ag_anon_test_" ++ toString i) ty cs
  | .postulateUnit _ n ty => axiomCmd ctx (leanMangleIdent n) ty
  | .patSynUnit n args _ rhs =>
    let nm ← declName ctx (leanMangleIdent n)
    let bs ← args.toArray.mapM fun a => do makeBinder .visible [a] (← `(_))
    let t ← expr ctx [] rhs
    `(@[match_pattern] abbrev $nm:declId $bs:bracketedBinder* := $t)
  | .dataUnit n params sort _ ctors =>
    if ctx.usesDepSigma && ctors.any (fun (_, ty) => mentionsDepSigmaWithTarget [ctx.modPrefix ++ [n]] ty) then
      .bot "nested dependent Sigma inductive requires Agda"
    let nm ← declName ctx (leanMangleIdent n)
    let bs ← telescope ctx [] params
    let s ← expr ctx [] sort
    let cs ← ctors.toArray.mapM fun (c, ty) => do
      let path := ctx.modPrefix ++ [n,c]
      let t ← if let some ds := ctx.deferredFields[path]? then
        execSignature ctx [] ty ((CatStructure.portDomains ty).zipIdx.map fun (_,i) =>
          if ds.contains i then .thunked else .strictVal)
      else expr ctx [] ty
      `(ctor| | $(varId c):ident : $t)
    `(inductive $nm:declId $bs:bracketedBinder* : $s where $cs:ctor*)
  | .recUnit n params sort _ rd fs =>
    if rd.coind && ctx.mode != .erasedExec then .bot "coinductive record requires Agda"
    let nm ← declName ctx (leanMangleIdent n)
    let ctor := (rd.constr.map varId).getD (ident "mk")
    let bs ← telescope ctx [] params
    let s ← expr ctx [] sort
    let mut seen := []
    let mut fds := #[]
    for ((f, ty), i) in fs.zipIdx do
      let t ← expr ctx [] (substSelfRecFields (ctx.modPrefix ++ [n]) seen ty)
      let (field, domain) ← if rd.coind then do
        pure (ident ("_thunk_" ++ leanMangleIdent f), ← `(agda_exec_defer% $t))
      else if (ctx.deferredFields[ctx.modPrefix ++ [n]]?).any (·.contains i) then
        pure (varId f, ← `(agda_exec_defer% $t))
      else pure (varId f, t)
      fds := fds.push (← `(structSimpleBinder| $field:ident : $domain)).raw
      seen := f :: seen
    let fields : TSyntax ``Lean.Parser.Command.structFields := ⟨Lean.mkNode ``Lean.Parser.Command.structFields #[Lean.mkNullNode fds]⟩
    `(structure $nm:declId $bs:bracketedBinder* : $s where
        $ctor:ident :: $fields:structFields)

def unitKey (u : ModUnit) : String :=
  match u.kind with
  | .funUnit _ n .. | .postulateUnit _ n .. | .dataUnit n .. | .recUnit n .. | .patSynUnit n .. => n
  | .anonUnit i .. => "_#" ++ toString i

private def bodies (cm : CodeMod) : List String := Id.run do
  let mut names := []
  let mut anon := 0
  for d in cm.decls do
    match d with
    | .sig _ "_" _ => anon := anon + 1
    | .fun_ _ "_" _ => names := ("_#" ++ toString (anon - 1)) :: names
    | .fun_ _ n _ | .dataDef _ n .. | .recDef _ n .. | .patSyn n .. => names := n :: names
    | _ => pure ()
  return names

private def mkBoundary (ctx : EmitCtx) (n : String) (ty : Expr) : PrismOutcome (QName × Cmd) := do
  let q := mkQ (ctx.modPrefix ++ [n])
  return (q, ← axiomCmd ctx (leanMangleIdent n) ty)

-- Expand a projected record shell into its type, constructor and projections.
-- The parameterized projection module shares the same receiver at every field.
private partial def signatures (scope : List String) (params : List Bind) : List Decl → List (List String × Expr)
  | [] => []
  | .sig _ n ty :: ds => (scope ++ [n],params.foldr Expr.pi ty) :: signatures scope params ds
  | .module_ n bs inner :: ds => Id.run do
    let nested := scope ++ [n]
    let rest := signatures scope params ds
    let some (.bind .visible ["_"] dom) := bs.getLast? |
      return signatures nested (params ++ bs) inner ++ rest
    -- In the projected Code, preceding fields in the same parameterized
    -- module have the receiver in scope. Flattening the module introduces
    -- that receiver as an explicit argument to each previous projection.
    let used := inner.flatMap collectVarsDecl ++ bs.flatMap fun (.bind _ xs _) => xs
    let rec fresh (k : Nat) : String :=
      let x := "_receiver" ++ toString k
      if used.contains x then fresh (k + 1) else x
    let receiver := fresh 0
    let ps := params ++ bs.dropLast ++ [.bind .visible [receiver] dom]
    let mut previous := []
    let mut fields := #[]
    for d in inner do
      if let .sig _ f ty := d then
        let path := nested ++ [f]
        let sig := ps.foldr Expr.pi (CatStructure.fieldTy previous ty)
        fields := fields.push (path,sig)
        previous := (path, Expr.app (.def_ (mkQ path)) (visArg (.var receiver))) :: previous
    return fields.toList ++ rest
  | _ :: ds => signatures scope params ds

private def boundaryUnit (ctx : EmitCtx) (u : ModUnit) : PrismOutcome Unit := do
  match u.kind with
  | .funUnit _ f ty _ | .postulateUnit _ f ty => discard <| mkBoundary ctx f ty
  | .anonUnit .. => return ()
  | .dataUnit .. => .bot "inductive recursion requires Agda"
  | .recUnit n params sort _ _ fs =>
    if hasDependentRecordFields (ctx.modPrefix ++ [n]) fs then .bot "dependent coinductive projections require Agda"
    discard <| telescope ctx [] params
    discard <| expr ctx [] sort
    for (_,ty) in fs do discard <| expr ctx [] ty
  | .patSynUnit .. => discard <| unit ctx u

def out {α : Type} : PrismOutcome α → Except String α
  | .translated a => .ok a
  | .bot e | .syntaxErr e => .error e

open CatStructure

private def unitPorts (u : ModUnit) : Array EvalColor :=
  match u.kind with
  | .funUnit _ _ ty cs | .anonUnit _ ty cs => formalPorts ty cs
  | .postulateUnit _ _ ty => formalPorts ty
  | .dataUnit _ bs sort _ ctors => formalPorts (bs.foldr Expr.pi sort) ++ ctors.toArray.flatMap (formalPorts ·.2)
  | .recUnit _ bs sort _ _ _ => formalPorts (bs.foldr Expr.pi sort)
  | .patSynUnit _ args .. => args.toArray.map fun _ => .thunked

private def lower (depMods : List (CodeMod × ExportedModule)) (cm : CodeMod) (em : ExportedModule)
    (plan : PushoutSplitPlan) (inherited : Array Lean.Name) (schedule : Option SlicePlan) :
    Except String LeanOpenSlice := do
  let mut ctx := buildBaseEmitCtx depMods cm em .hybridCheck
  let (units, sccs, variables) ← match schedule with
    | some p => pure (p.units.toArray, p.sccs, p.checkedVariable?)
    | none => do
      let (view, variables) ← out (checkedVariableView cm)
      let (_, units) ← out (extractModUnits view)
      pure (units.toArray, computeUnitSCCs units, variables)
  let leanBodies := variables.toList ++ bodies plan.leanSliceSpec
  let shared := bodies plan.sharedBase
  let projected := signatures cm.modName.full [] plan.leanSliceSpec.decls
  let mut base := #[]
  let mut boundary := #[]
  let mut guards := #[]
  let mut ordered := #[]
  if requiresSafeAgda cm && units.any (fun u => u.kind matches .postulateUnit ..) then
    throw "postulates are not permitted in a --safe module"
  unless cm.modName.full == plan.leanSliceSpec.modName.full do throw "Lean projection has a different originating module"
  let ports := Std.HashMap.ofList plan.leanBoundaryPorts.toList
  for scc in sccs do
    let group ← scc.mapM fun id => do
      let some u := units[id]? | throw "invalid SCC unit"
      pure u
    let staged := group.length > 1 && group.all (fun u => leanBodies.contains (unitKey u))
    let indices := if staged then structuralArguments ctx.modPrefix group else none
    let factor := if staged && indices.isNone then FactorMutual.stage? ctx group else none
    if let some f := factor then
      ctx := {ctx with factoredWalks := ctx.factoredWalks ++ (f.helpers.take 1).flatMap (·.definedCanons)
                       factoredEquations := ctx.factoredEquations ++
        (f.helpers ++ f.members ++ f.wrappers).flatMap (·.definedCanons)}
    let stages := match factor with
      | some f => (f.helpers.map fun u => ([u],[],true)) ++ [(f.members,f.indices,true)] ++
          (f.wrappers.map fun u => ([u],[],false))
      | none => [(group,indices.getD [],false)]
    for (stage,indices,synth) in stages do
      let mut commands := #[]
      for u in stage do
        let name := unitKey u
        let origin := mkQ (cm.modName.full ++ [name])
        if synth || leanBodies.contains name then
          let code ← out (unit ctx u (indices.lookup name))
          let sort := match u.kind with
            | .dataUnit .. | .recUnit .. => DeclSort.baseTypeDecl
            | _ => if shared.contains name then DeclSort.pureSigHelperDecl else DeclSort.sweetBodyDecl
          let d : LeanPreTCCmd := ⟨code, origin, sort, unitPorts u⟩
          if shared.contains name then base := base.push d
          guards := guards.push d
          commands := commands.push d
        else
          for path in u.definedCanons do
            let some ty := projected.lookup path | continue
            let q := mkQ path
            let some actual := ports[path]? | throw s!"undeclared boundary in Lean projection: {fullDot q}"
            let relative := actual.replacePrefix (.mkSimple (leanModNamespace cm.modName.full)) .anonymous
            match axiomCmd ctx relative.toString ty with
            | .syntaxErr e => throw e
            | .bot _ => continue -- a nonrepresentable port has no declaration at the Lean boundary
            | .translated cmd =>
              let d : LeanPreTCCmd := ⟨cmd, q, .boundaryHoleDecl, formalPorts ty⟩
              boundary := boundary.push d
              commands := commands.push d
      if commands.size > 1 && commands.all (·.declSort != .boundaryHoleDecl) then
        let cmds := commands.map (·.syntaxOf)
        let block ← out (show PrismOutcome Cmd from `(mutual $cmds:command* end))
        if let some head := commands[0]? then ordered := ordered.push {head with syntaxOf := block}
      else ordered := ordered ++ commands
  let localPorts := boundary.filterMap fun d => ports[d.origin.full]?
  let allowed := (inherited ++ localPorts).toList.eraseDups.toArray
  return ⟨cm.modName, ⟨base⟩, boundary, allowed, guards.map (fun d => ⟨d⟩), ordered⟩

end Chk

def probeFastUnit (ctx : EmitCtx) (u : ModUnit) : PrismOutcome Unit := do
  discard <| Chk.unit ctx u

def probeBoundaryUnit := Chk.boundaryUnit

/-- Same-phase checking functor on the canonical pushout projection. -/
def transcodeChk (depMods : List (CodeMod × ExportedModule)) (cm : CodeMod) (em : ExportedModule)
    (plan : CatStructure.PushoutSplitPlan) (inherited : Array Lean.Name := #[])
    (schedule : Option SlicePlan := none) :
    Except String CatStructure.LeanOpenSlice :=
  Chk.lower depMods cm em plan inherited schedule

end Prism
