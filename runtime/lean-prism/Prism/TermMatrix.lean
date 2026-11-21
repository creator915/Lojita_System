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

-- Include constructor subpatterns as well as their bound variables. A recursive
-- call on (z ∷ zs) under (y ∷ (z ∷ zs)) decreases just like a call on a named tail.
partial def strictSubpatterns : Pat → List Pat
  | .conP _ args => args.flatMap fun a => a.thing :: strictSubpatterns a.thing
  | .asP _ p => strictSubpatterns p
  | .recP fields => fields.flatMap fun (_, p) => p :: strictSubpatterns p
  | _ => []

-- Flatten nested `Expr.app` into `(headExpr, visibleArgs)` (and record if hidden args precede).
partial def unrollApps : Expr → Expr × List (Arg Expr)
  | .app f a =>
      let (hd, args) := unrollApps f
      (hd, args ++ [a])
  | e => (e, [])

private partial def matchesSubpattern (e : Expr) : Pat → Bool
  | .varP x => match e with | .var y => x == y | _ => false
  | .asP x p => matchesSubpattern e (.varP x) || matchesSubpattern e p
  | .litP l => match e with | .lit r => l == r | _ => false
  | .conP q ps =>
    let (head, args) := unrollApps e
    match head with
    | .con c => c.full == q.full && c.canonAlts == q.canonAlts && ps.length == args.length &&
      (ps.zip args).all fun (p, arg) =>
        p.hid == arg.hid && p.label == arg.label && matchesSubpattern arg.thing p.thing
    | _ => false
  | _ => false

private def withoutShadowed (subterms : List Pat) (bound : List String) : List Pat :=
  subterms.filter fun p => !(patAllVars p).any bound.contains

private def refersTo (q : QName) (target : List String) : Bool :=
  q.full == target || q.canonAlts.contains target

-- Check if target `q` appears anywhere in `Expr`.
mutual
  partial def mentionsQName (target : List String) : Expr → Bool
    | .def_ q      => refersTo q target
    | .con q       => refersTo q target
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
-- `visIdx`-th visible argument is an unshadowed strict subpattern.
mutual
  partial def allCallsStructural (selfFull : List String) (visIdx : Nat)
      (subterms : List Pat) : Expr → Bool
    | .var _ | .con _ | .lit _ | .set _ | .hole | .meta_ | .absurdLam _ => true
    | .def_ q => !refersTo q selfFull   -- unapplied reference to `self` is non-structural!
    | e@(.app _ _) =>
        let (hd, args) := unrollApps e
        let argsOK := args.all (fun a => allCallsStructural selfFull visIdx subterms a.thing)
        match hd with
        | .def_ q =>
            if refersTo q selfFull then
              let visArgs := args.filter (fun a => a.hid == .visible)
              match visArgs[visIdx]? with
              | some argK =>
                  subterms.any (matchesSubpattern argK.thing) && argsOK
              | none => false
            else
              allCallsStructural selfFull visIdx subterms hd && argsOK
        | _ => allCallsStructural selfFull visIdx subterms hd && argsOK
    | .lam a body =>
        let sv := withoutShadowed subterms [a.thing]
        allCallsStructural selfFull visIdx sv body
    | .lamT (.bind _ xs t) body =>
        let sv := withoutShadowed subterms xs
        allCallsStructural selfFull visIdx subterms t &&
        allCallsStructural selfFull visIdx sv body
    | .lamCase _ => false
    | .pi (.bind _ xs t) body =>
        let sv := withoutShadowed subterms xs
        allCallsStructural selfFull visIdx subterms t &&
        allCallsStructural selfFull visIdx sv body
    | .fun_ a body =>
        allCallsStructural selfFull visIdx subterms a.thing &&
        allCallsStructural selfFull visIdx subterms body
    | .let_ bs body =>
        checkLetsStructural selfFull visIdx subterms bs body
    | .rec_ fs =>
        fs.all (fun (_, v) => allCallsStructural selfFull visIdx subterms v)
    | .recUpd r fs =>
        allCallsStructural selfFull visIdx subterms r &&
        fs.all (fun (_, v) => allCallsStructural selfFull visIdx subterms v)
    | .dot e => allCallsStructural selfFull visIdx subterms e

  partial def checkLetsStructural (selfFull : List String) (visIdx : Nat)
      (subterms : List Pat) (bs : List LetBind) (body : Expr) : Bool :=
    match bs with
    | [] => allCallsStructural selfFull visIdx subterms body
    | .letBind x t e :: rest =>
        allCallsStructural selfFull visIdx subterms t &&
        allCallsStructural selfFull visIdx subterms e &&
        checkLetsStructural selfFull visIdx (withoutShadowed subterms [x]) rest body
    | .letPat p e :: rest =>
        let bound := patAllVars p
        allCallsStructural selfFull visIdx subterms e &&
        checkLetsStructural selfFull visIdx (withoutShadowed subterms bound) rest body
end

private partial def rhsStructural (self : List String) (index : Nat) (subterms : List Pat) : RHS → Bool
  | .rhs body => allCallsStructural self index subterms body
  | .absurdRHS => true
  | .rewriteRHS eqs r => eqs.all (allCallsStructural self index subterms) && rhsStructural self index subterms r
  | .withRHS es cs =>
    es.all (allCallsStructural self index subterms) && cs.all fun
      | .clause (.with_ _ ps extra) body [] =>
        let shadow := (ps ++ extra).flatMap (fun p => patAllVars p.thing)
        rhsStructural self index (withoutShadowed subterms shadow) body
      | _ => false

def checkCallAt (callee : List String) (callerArg calleeArg : Nat) : Clause → Bool
  | .clause (.head _ pats) rhs ws =>
    !ws.any (mentionsDecl callee) &&
      let visible := pats.filter (fun a => a.hid == .visible)
      let smaller := visible[callerArg]?.map (fun p => strictSubpatterns p.thing)
      rhsStructural callee calleeArg (smaller.getD []) rhs
  | _ => false

def checkClauseAt (selfFull : List String) (visIdx : Nat) : Clause → Bool :=
  checkCallAt selfFull visIdx visIdx

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
