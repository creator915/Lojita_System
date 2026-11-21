import Prism.Outcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.MixfixDAG`: Exact Agda Partial-Order Mixfix Precedence & Associativity Checker

Implements Agda's partial-order precedence rules (Danielsson & Norell):
1. Operators without an explicit `infix`/`infixl`/`infixr` declaration have
   `FixLevel.unrelated` and CANNOT mix unparenthesized with any other operator.
2. Operators at numeric levels `p₁` vs `p₂` bind according to `p₁ > p₂` or `p₁ < p₂`.
3. Operators at EQUAL numeric level `p₁ == p₂` require BOTH to be `infixL`
   (left-associative) or BOTH to be `infixR` (right-associative). If either is
   `infixN` (e.g., `a ≡ b ≡ c`) or they disagree (`infixL` vs `infixR`, e.g.,
   `a + b ∧ c`), parsing immediately fails with `.syntaxErr`.
-/

namespace Prism

inductive FixLevel : Type where
  | unrelated : FixLevel
  | related   : Int → Assoc → FixLevel
  deriving Repr, BEq

-- Agda 2.6.3 `defaultFixity`: unannotated mixfix operators have `infix 20` (`Related 20 NonAssoc`)!
def defaultAgdaFixity : FixLevel :=
  .related 20 .infixN

inductive MixShape : Type where
  | closedOp  : List String → MixShape               -- e.g. `[_]` -> parts `["[", "]"]` (1 internal hole)
  | prefixOp  : List String → FixLevel → MixShape    -- e.g. `¬_` -> `["¬"]`, `if_then_else_` -> `["if", "then", "else"]`
  | infixOp   : List String → FixLevel → MixShape    -- e.g. `_+_` -> `["+"]`
  | postfixOp : List String → FixLevel → MixShape    -- e.g. `_!` -> `["!"]`
  deriving Repr, BEq

structure OpEntry : Type where
  opName  : String
  qname   : QName
  isCon   : Bool
  shape   : MixShape
  deriving Repr, BEq

def analyzeMixfix (name : String) (q : QName) (isCon : Bool) (fx : FixLevel) : Option OpEntry :=
  if name == "_" || !name.contains '_' then
    none
  else
    let rawParts := name.splitOn "_"
    let startsHole := name.startsWith "_"
    let endsHole := name.endsWith "_"
    let nonEmptyParts := rawParts.filter (fun s => !s.isEmpty)
    if nonEmptyParts.isEmpty then
      none
    else
      let shape :=
        match startsHole, endsHole with
        | false, false => .closedOp nonEmptyParts
        | false, true  => .prefixOp nonEmptyParts fx
        | true,  true  => .infixOp nonEmptyParts fx
        | true,  false => .postfixOp nonEmptyParts fx
      some { opName := name, qname := q, isCon := isCon, shape := shape }

-- Compare an outer/left operator `fx₁` against an inner/right competing operator `fx₂`.
inductive PrecRel : Type where
  | leftTighter   -- `(a op₁ b) op₂ c`
  | rightTighter  -- `a op₁ (b op₂ c)`
  | ambiguous     -- Agda parse ambiguity error!
  deriving Repr, BEq

def compareInfixPrec (fx1 fx2 : FixLevel) : PrecRel :=
  match fx1, fx2 with
  | .unrelated, _ => .ambiguous
  | _, .unrelated => .ambiguous
  | .related p1 a1, .related p2 a2 =>
      if p1 > p2 then .leftTighter
      else if p1 < p2 then .rightTighter
      else
        match a1, a2 with
        | .infixL, .infixL => .leftTighter
        | .infixR, .infixR => .rightTighter
        | _, _             => .ambiguous

-- Compare prefix `p_ a op₂ b`: can `p_` swallow `(a op₂ b)` (`rightTighter`, when `prec(p) < prec(op₂)`
-- or equal right-assoc), or does `(p a) op₂ b` win (`leftTighter`, when `prec(p) > prec(op₂)`)?
def comparePrefixInfix (fxPre fxInf : FixLevel) : PrecRel :=
  match fxPre, fxInf with
  | .unrelated, _ => .ambiguous
  | _, .unrelated => .ambiguous
  | .related pPre aPre, .related pInf aInf =>
      if pPre > pInf then .leftTighter
      else if pPre < pInf then .rightTighter
      else
        match aPre, aInf with
        | .infixR, .infixR => .rightTighter
        | _, _             => .ambiguous

end Prism
