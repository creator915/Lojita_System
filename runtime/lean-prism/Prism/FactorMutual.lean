import Prism.LoweringContext

set_option autoImplicit false

namespace Prism

/-- Select a structural parameter per function. On every edge the actual
    argument must be a strict constructor subpattern of the caller's parameter. -/
def structuralArguments (scope : List String) (units : List ModUnit) : Option (List (String × Nat)) := do
  let fs ← units.mapM fun u => do
    let .funUnit _ n _ cs := u.kind | none
    let some (.clause (.head _ ps) _ _) := cs.head? | none
    pure (n, cs, (ps.filter (·.hid == .visible)).length)
  let rec choose (remaining picked : List (String × List Clause × Nat)) : Option (List (String × Nat)) :=
    match remaining with
    | [] => some (picked.map fun (n,_,i) => (n,i))
    | (n,cs,arity) :: rest => (List.range arity).findSome? fun i => do
      guard (cs.all (checkCallAt (scope ++ [n]) i i))
      guard <| picked.all fun (m,ds,j) =>
        cs.all (checkCallAt (scope ++ [m]) i j) && ds.all (checkCallAt (scope ++ [n]) j i)
      choose rest ((n,cs,i) :: picked)
  choose fs []

namespace FactorMutual

private structure Factor where
  walk : QName
  outer : QName
  aux : QName
  arity : Nat
  fixedIx : Nat
  cb : String
  param : String

private def apps (head : Expr) (args : List (Arg Expr)) := args.foldl Expr.app head

private def Factor.invoke (f : Factor) (args : List (Arg Expr)) : Option Expr := do
  let fixed ← args[f.fixedIx]?
  let callback := Expr.lam (visArg f.param) (apps (.def_ f.outer) [visArg (.var f.param), fixed])
  return apps (.def_ f.aux) (visArg callback :: args)

/-- In the list traversal, substitute a callback for calls that share its fixed
    argument. At callers, close the callback over the actual fixed argument. -/
private partial def transform (f : Factor) (fixed : Option String) (e : Expr) : Option Expr := do
  unless mentionsQName f.walk.full e || (fixed.isSome && mentionsQName f.outer.full e) do return e
  match e with
  | .app .. =>
    let (head,args) := unrollApps e
    let args ← args.mapM fun a => do return {a with thing := ← transform f fixed a.thing}
    if let .def_ q := head then
      if q.full == f.walk.full then
        guard (q.canonAlts.isEmpty && args.length == f.arity && args.all (·.hid == .visible))
        if let some x := fixed then
          let some a := args[f.fixedIx]? | none
          guard (encExpr a.thing == encExpr (.var x))
          return apps (.def_ f.aux) (visArg (.var f.cb) :: args)
        return ← f.invoke args
      if q.full == f.outer.full then
        if let some x := fixed then
          let [a,b] := args | none
          guard (q.canonAlts.isEmpty && a.hid == .visible && b.hid == .visible && encExpr b.thing == encExpr (.var x))
          return .app (.var f.cb) a
    return apps (← transform f fixed head) args
  | .lam a b =>
    guard (fixed != some a.thing)
    return .lam a (← transform f fixed b)
  | _ => none

private def rootParams : LHS → List (Arg Pat)
  | .head _ ps => ps
  | .with_ parent .. | .proj _ parent .. => rootParams parent

private def lhsAux (f : Factor) : LHS → Option LHS
  | .head q ps => do
    guard (q.full == f.walk.full)
    return .head f.aux (visArg (.varP f.cb) :: ps)
  | .with_ base ps [] => return .with_ (← lhsAux f base) ps []
  | _ => none

private partial def transClause (f : Factor) (inWalk : Bool) : Clause → Option Clause
  | .clause l r [] => do
    let fixed ← if inWalk then do
      let p ← (rootParams l)[f.fixedIx]?
      let .varP x := p.thing | none
      if let .with_ _ ps extra := l then
        guard (!((ps ++ extra).flatMap fun a => patAllVars a.thing).contains x)
      pure (some x)
    else pure none
    let r ← match r with
      | .rhs e => pure (.rhs (← transform f fixed e))
      | .withRHS es cs => pure (.withRHS (← es.mapM (transform f fixed)) (← cs.mapM (transClause f inWalk)))
      | _ => none
    return .clause (← if inWalk then lhsAux f l else pure l) r []
  | _ => none

private partial def firstOrder : Expr → List Expr × Expr
  | .fun_ ⟨.visible,none,t⟩ b => let (ds,r) := firstOrder b; (t::ds,r)
  | t => ([],t)

private partial def containsName (n : String) : SExpr → Bool
  | .str s | .sym s => n == s
  | .list xs => xs.any (containsName n)
  | .num _ => false

/-- The staged SCC contains a standalone structural traversal, a structurally
    decreasing mutual group over newer subtrees, and the original traversal's
    public definition. All three are ordinary checked definitions. -/
structure Stages where
  helpers : List ModUnit
  members : List ModUnit
  indices : List (String × Nat)
  wrappers : List ModUnit

/-- A structural recursor inspects its major premise before doing any other
    work. Agda can instead return from an earlier equation without inspecting
    that argument. Preserve those equations in a first-order dispatcher. -/
private structure Front where
  name : QName
  core : QName
  dispatch : Option QName
  arity : Nat

private def Front.call (front : Front) (args : List (Arg Expr)) : Expr :=
  let body := apps (.def_ front.core) args
  match front.dispatch with
  | some d => apps (.def_ d) (visArg body :: args)
  | none => body

private partial def useFronts (fs : List Front) (e : Expr) : Option Expr := do
  unless fs.any (fun f => mentionsQName f.name.full e) do return e
  match e with
  | .app .. =>
    let (h,args) := unrollApps e
    let args ← args.mapM fun a => do return {a with thing := ← useFronts fs a.thing}
    if let .def_ q := h then
      if let some f := fs.find? (·.name.full == q.full) then
        guard (q.canonAlts.isEmpty && args.length == f.arity && args.all (·.hid == .visible))
        return f.call args
    return apps (← useFronts fs h) args
  | .lam a b => return .lam a (← useFronts fs b)
  | _ => none

private def renameLHS (n : QName) (extra : List (Arg Pat)) : LHS → Option LHS
  | .head _ ps => some (.head n (extra ++ ps))
  | .with_ p ws [] => return .with_ (← renameLHS n extra p) ws []
  | _ => none

private partial def coreClause (n : QName) (fs : List Front) : Clause → Option Clause
  | .clause lhs rhs [] => do
    let rr ← match rhs with
      | .rhs e => pure (.rhs (← useFronts fs e))
      | .withRHS es cs => pure (.withRHS (← es.mapM (useFronts fs)) (← cs.mapM (coreClause n fs)))
      | _ => none
    return .clause (← renameLHS n [] lhs) rr []
  | _ => none

private def renameUnit (u : ModUnit) (m : Mods) (n : QName) (t : Expr) (cs : List Clause) :=
  {u with kind := .funUnit m n.shown t cs, definedCanons := [n.full], valueCanons := [n.full]}

private def fronts (ctx : EmitCtx) (members : List ModUnit) (ix : List (String × Nat)) :
    Option (List ModUnit × List ModUnit × List (String × Nat) × List ModUnit) := do
  let q := fun n => mkQ (ctx.modPrefix ++ [n])
  let names := members.flatMap (·.valueCanons)
  let specs ← members.mapM fun u => do
    let .funUnit m n ty cs := u.kind | none
    let (ds,r) := firstOrder ty
    let i ← ix.lookup n
    let pre := cs.takeWhile fun c => match c with
      | .clause (.head _ ps) (.rhs _) [] =>
        let p := ps[i]?.map (·.thing)
        (p.any fun pat => pat matches .varP _ | .wildP) && !names.any (fun name => mentionsClause name c)
      | _ => false
    let core := q (n ++ "_structuralCore")
    let front := q (n ++ "_equationFront")
    guard (!ctx.symIndex.contains core.full && !ctx.symIndex.contains front.full)
    let f : Front := ⟨q n,core,if pre.isEmpty then none else some front,ds.length⟩
    let fb := "prismFallbackValue"
    guard (!u.rawDecls.any (fun d => containsName fb (encDecl d)))
    let ds ← if pre.isEmpty then pure [] else do
      let initial ← pre.mapM fun c => do
        let .clause l v ws := c
        pure (.clause (← renameLHS front [visArg .wildP] l) v ws)
      let fallback := Clause.clause (.head front (visArg (.varP fb) :: ds.map (fun _ => visArg .wildP))) (.rhs (.var fb)) []
      pure [renameUnit u m front (.fun_ (visArg r) ty) (initial ++ [fallback])]
    let vars := (List.range f.arity).map fun k => "prismFrontArg" ++ toString k
    let call := f.call (vars.map fun x => visArg (.var x))
    let wrapper := renameUnit u m f.name ty [.clause (.head f.name (vars.map fun x => visArg (.varP x))) (.rhs call) []]
    return (f,i,ds,wrapper)
  let fs := specs.map Prod.fst
  let cores ← (members.zip fs).mapM fun (u,f) => do
    let .funUnit m _ ty cs := u.kind | none
    return renameUnit u m f.core ty (← cs.mapM (coreClause f.core fs))
  return (specs.flatMap fun (_,_,ds,_) => ds,cores,specs.map fun (f,i,_,_) => (f.core.shown,i),
    specs.map fun (_,_,_,w) => w)

private def tryUnit (ctx : EmitCtx) (us : List ModUnit) (u : ModUnit) : Option Stages := do
  let .funUnit mods walk ty cs := u.kind | none
  guard (mods.termCheck == .check)
  let rest := us.filter (·.uid != u.uid)
  let [v] := rest.filter (fun a => a.valueCanons.any (fun n => cs.any (mentionsClause n))) | none
  let .funUnit _ outer vty _ := v.kind | none
  let ([input, fixedTy],result) := firstOrder vty | none
  let (doms,_) := firstOrder ty
  let aux := walk ++ "_structuralWalk"
  let q := fun n => mkQ (ctx.modPrefix ++ [n])
  guard (!(ctx.symIndex.contains (q aux).full))
  let cb := "prismStructuralCallback"
  let param := "prismCallbackArg"
  let args := (List.range doms.length).map fun i => "prismWalkArg" ++ toString i
  let occupied := us.flatMap fun a => a.rawDecls.map encDecl
  guard (!((cb :: param :: args).any fun n => occupied.any (containsName n)))
  (List.range doms.length).findSome? fun fixedIx => do
    guard (doms[fixedIx]?.map encExpr == some (encExpr fixedTy))
    let f : Factor := ⟨q walk, q outer, q aux, doms.length, fixedIx, cb, param⟩
    let cty := Expr.fun_ (visArg input) result
    let hs ← cs.mapM (transClause f true)
    let helper := {u with kind := .funUnit mods aux (.fun_ (visArg cty) ty) hs,
                          definedCanons := [(q aux).full], valueCanons := [(q aux).full]}
    let members ← rest.mapM fun a => do
      let .funUnit m n t ds := a.kind | none
      let ds ← ds.mapM (transClause f false)
      return {a with kind := .funUnit m n t ds}
    let ix ← structuralArguments ctx.modPrefix members
    let wrapperBody ← f.invoke (args.map fun n => visArg (.var n))
    let c := Clause.clause (.head (q walk) (args.map fun n => visArg (.varP n))) (.rhs wrapperBody) []
    let wrapper := {u with kind := .funUnit mods walk ty [c]}
    let (pres,cores,indices,ws) ← fronts ctx members ix
    return ⟨helper :: pres,cores,indices,ws ++ [wrapper]⟩

def stage? (ctx : EmitCtx) (us : List ModUnit) : Option Stages :=
  us.findSome? (tryUnit ctx us)

end FactorMutual
end Prism
