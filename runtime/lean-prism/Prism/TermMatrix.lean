import Prism.Outcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.TermMatrix`: Static Structural Recursion Verifier

Why this pass is essential for soundness:
Lean 4's default `def` elaborator falls back to `WellFounded.fix` + `omega`,
which can silently accept arithmetic recursion like `f n = f (n - 1)` that
Agda's structural Foetus termination checker REJECTS!

This pass inspects every function `f`:
1. **Non-recursive** (`f` does not reference `f` in any clause RHS/`where`) ->
   emitted as plain non-recursive Lean `def` (`recParam = none`).
2. **Single-parameter strict constructor subterm recursion** (there exists a
   parameter index `k` such that every recursive call `f a₀ ... aₘ` inside a
   clause matching pattern `pₖ` passes a strict syntactic constructor subterm
   of `pₖ` at position `k`, and functions in a mutual group do not cycle
   across distinct definitions) -> emitted with `termination_by structural param_k`!
3. **Any other recursion** (e.g., `f (n ∸ 1)`, mutual recursion across multiple
   functions, or multi-parameter lexicographic descent like Ackermann) ->
   returns `PrismOutcome.bot` so `leanPrism` routes to `LegacyAgda`'s exact
   Foetus checker (never turning non-terminating Agda into valid Lean 4!).
-/

namespace Prism

-- Collect all strict subterm variable names bound inside a constructor pattern `p`.
partial def patAllVars : Pat → List String
  | .varP x      => [x]
  | .conP _ args => args.flatMap (fun a => patAllVars a.thing)
  | .asP x p     => x :: patAllVars p
  | .recP fs     => fs.flatMap (fun (_, p) => patAllVars p)
  | _            => []

-- Strict subterm variables of `p`: variables strictly *inside* at least one `conP`.
def patStrictSubVars : Pat → List String
  | .conP _ args => args.flatMap (fun a => patAllVars a.thing)
  | .asP _ p     => patStrictSubVars p
  | _            => []

-- Flatten nested `Expr.app` into `(headExpr, visibleArgs)` (and record if hidden args precede).
partial def unrollApps : Expr → Expr × List (Arg Expr)
  | .app f a =>
      let (hd, args) := unrollApps f
      (hd, args ++ [a])
  | e => (e, [])

-- Check if target `q` appears anywhere in `Expr`.
mutual
  partial def mentionsQName (target : List String) : Expr → Bool
    | .def_ q      => q.full == target
    | .con q       => q.full == target
    | .app f a     => mentionsQName target f || mentionsQName target a.thing
    | .lam _ e     => mentionsQName target e
    | .lamT b e    => mentionsBind target b || mentionsQName target e
    | .lamCase cs  => cs.any (mentionsClause target)
    | .pi b e      => mentionsBind target b || mentionsQName target e
    | .fun_ a e    => mentionsQName target a.thing || mentionsQName target e
    | .let_ bs e   => bs.any (mentionsLet target) || mentionsQName target e
    | .rec_ fs     => fs.any (fun (_, v) => mentionsQName target v)
    | .recUpd r fs => mentionsQName target r || fs.any (fun (_, v) => mentionsQName target v)
    | .dot e       => mentionsQName target e
    | _            => false

  partial def mentionsBind (target : List String) : Bind → Bool
    | .bind _ _ t => mentionsQName target t

  partial def mentionsLet (target : List String) : LetBind → Bool
    | .letBind _ t e => mentionsQName target t || mentionsQName target e
    | .letPat _ e    => mentionsQName target e

  partial def mentionsRHS (target : List String) : RHS → Bool
    | .rhs e           => mentionsQName target e
    | .absurdRHS       => false
    | .withRHS es cs   => es.any (mentionsQName target) || cs.any (mentionsClause target)
    | .rewriteRHS es r => es.any (mentionsQName target) || mentionsRHS target r

  partial def mentionsClause (target : List String) : Clause → Bool
    | .clause _ r ws => mentionsRHS target r || ws.any (mentionsDecl target)

  partial def mentionsDecl (target : List String) : Decl → Bool
    | .sig _ _ e        => mentionsQName target e
    | .fun_ _ _ cs      => cs.any (mentionsClause target)
    | .dataSig _ _ bs e => bs.any (mentionsBind target) || mentionsQName target e
    | .dataDef _ _ _ cs => cs.any (fun (_, e) => mentionsQName target e)
    | .recSig _ _ bs e  => bs.any (mentionsBind target) || mentionsQName target e
    | .recDef _ _ _ _ fs => fs.any (fun (_, e) => mentionsQName target e)
    | .module_ _ bs ds  => bs.any (mentionsBind target) || ds.any (mentionsDecl target)
    | _                 => false
end

-- Verify that EVERY occurrence of `selfFull` in `e` is a direct visible call whose
-- `visIdx`-th visible argument is `Expr.var v` for some `v ∈ strictVars` (and `v` not shadowed).
mutual
  partial def allCallsStructural (selfFull : List String) (visIdx : Nat)
      (strictVars : List String) : Expr → Bool
    | .var _ | .con _ | .lit _ | .set _ | .hole | .meta_ | .absurdLam _ => true
    | .def_ q => q.full != selfFull   -- unapplied reference to `self` is non-structural!
    | e@(.app _ _) =>
        let (hd, args) := unrollApps e
        let argsOK := args.all (fun a => allCallsStructural selfFull visIdx strictVars a.thing)
        match hd with
        | .def_ q =>
            if q.full == selfFull then
              let visArgs := args.filter (fun a => a.hid == .visible)
              match visArgs[visIdx]? with
              | some argK =>
                  match argK.thing with
                  | .var v => strictVars.contains v && argsOK
                  | _      => false
              | none => false
            else
              allCallsStructural selfFull visIdx strictVars hd && argsOK
        | _ => allCallsStructural selfFull visIdx strictVars hd && argsOK
    | .lam a body =>
        let sv := strictVars.filter (· != a.thing)
        allCallsStructural selfFull visIdx sv body
    | .lamT (.bind _ xs t) body =>
        let sv := strictVars.filter (fun v => !xs.contains v)
        allCallsStructural selfFull visIdx strictVars t &&
        allCallsStructural selfFull visIdx sv body
    | .lamCase _ => false
    | .pi (.bind _ xs t) body =>
        let sv := strictVars.filter (fun v => !xs.contains v)
        allCallsStructural selfFull visIdx strictVars t &&
        allCallsStructural selfFull visIdx sv body
    | .fun_ a body =>
        allCallsStructural selfFull visIdx strictVars a.thing &&
        allCallsStructural selfFull visIdx strictVars body
    | .let_ bs body =>
        checkLetsStructural selfFull visIdx strictVars bs body
    | .rec_ fs =>
        fs.all (fun (_, v) => allCallsStructural selfFull visIdx strictVars v)
    | .recUpd r fs =>
        allCallsStructural selfFull visIdx strictVars r &&
        fs.all (fun (_, v) => allCallsStructural selfFull visIdx strictVars v)
    | .dot e => allCallsStructural selfFull visIdx strictVars e

  partial def checkLetsStructural (selfFull : List String) (visIdx : Nat)
      (strictVars : List String) (bs : List LetBind) (body : Expr) : Bool :=
    match bs with
    | [] => allCallsStructural selfFull visIdx strictVars body
    | .letBind x t e :: rest =>
        allCallsStructural selfFull visIdx strictVars t &&
        allCallsStructural selfFull visIdx strictVars e &&
        checkLetsStructural selfFull visIdx (strictVars.filter (· != x)) rest body
    | .letPat p e :: rest =>
        let bound := patAllVars p
        allCallsStructural selfFull visIdx strictVars e &&
        checkLetsStructural selfFull visIdx (strictVars.filter (fun v => !bound.contains v)) rest body
end

def checkClauseAt (selfFull : List String) (visIdx : Nat) : Clause → Bool
  | .clause (.head _ pats) rhs ws =>
      if ws.any (mentionsDecl selfFull) then
        false
      else
        let visPats := pats.filter (fun a => a.hid == .visible)
        match rhs with
        | .absurdRHS => true
        | .rhs body =>
            if !mentionsQName selfFull body then
              true
            else
              match visPats[visIdx]? with
              | none => false
              | some patK =>
                  let sv := patStrictSubVars patK.thing
                  !sv.isEmpty && allCallsStructural selfFull visIdx sv body
        | _ => false
  | _ => false

inductive RecAnalysis : Type where
  | nonRecursive  : RecAnalysis
  | structuralArg : Nat → RecAnalysis   -- 0-based visible parameter index
  deriving Repr, BEq

def analyzeFunctionRecursion (modPrefix : List String) (fnName : String)
    (clauses : List Clause) : PrismOutcome RecAnalysis :=
  let selfFull := modPrefix ++ [fnName]
  let isRec := clauses.any (mentionsClause selfFull)
  if !isRec then
    .translated .nonRecursive
  else
    let maxArity :=
      match clauses.head? with
      | some (.clause (.head _ pats) _ _) => (pats.filter (fun a => a.hid == .visible)).length
      | _ => 0
    let candidates := List.range maxArity
    match candidates.find? (fun k => clauses.all (checkClauseAt selfFull k)) with
    | some k => .translated (.structuralArg k)
    | none   => .bot s!"function '{fnName}' uses non-trivial or non-structural recursion; routing to Agda Foetus checker"

end Prism
