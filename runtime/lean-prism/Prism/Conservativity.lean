import Prism.TranscodeChk
import Prism.KernelDriver

namespace Prism.Conservativity

private def ref (s : String) := Expr.def_ (mkQ (s.splitOn "."))
private def ctor (s : String) := Expr.con (mkQ (s.splitOn "."))
private def app (f a : Expr) := Expr.app f (visArg a)
private def lam (xs : List String) (e : Expr) := xs.foldr (fun x => Expr.lam (visArg x)) e
private def arrow (a b : Expr) := Expr.fun_ (visArg a) b
private def pi (x : String) (t body : Expr) := Expr.pi (.bind .visible [x] t) body

private def testModule (name : String) (type body : Expr) : CodeMod :=
  let imports := ["Context.Taboo", "Agda.Builtin.Unit", "Agda.Builtin.Equality", "Agda.Builtin.Sigma",
                  "Agda.Builtin.Bool", "Agda.Builtin.Nat", "Data.Unit", "Data.Empty", "Data.Nat", "Data.Bool",
                  "Data.Sum.Base", "Data.Product", "Relation.Binary.PropositionalEquality"]
  ⟨mkQ [name], [], (imports.map fun s => .import_ (mkQ (s.splitOn ".")) true {} []) ++ [.sig {} "proof" type, .fun_ {} "proof"
    [.clause (.head (mkQ [name, "proof"]) []) (.rhs body) []]]⟩

private def lower (cm : CodeMod) (hybrid := false) : IO CatStructure.LeanOpenSlice := do
  let plan ← IO.ofExcept <| CatStructure.checkedPushoutSplit cm (fun u =>
    if hybrid && u.name.full.getLast? == some "port" then some "residual" else none)
  unless plan.agdaResidual?.isSome == hybrid do throw <| IO.userError "incorrect conservativity probe routing"
  let exports ← IO.ofExcept <| Chk.out (synthesizeExportedModule [] cm)
  let slice ← IO.ofExcept <| transcodeChk [] cm exports plan
  unless slice.fast.any (fun d => d.origin.full == cm.modName.full ++ ["proof"]) do
    throw <| IO.userError "conservativity probe has no guarded fast proof"
  return slice

private def requireRejection (label : String) (slice : CatStructure.LeanOpenSlice)
    (expected : String → Bool) : IO Unit := do
  try discard <| KernelDriver.elaborate slice #[] true
  catch ex =>
    if expected ex.toString then return
    throw <| IO.userError s!"{label}: unexpected kernel diagnostic: {ex}"
  throw <| IO.userError s!"conservativity regression: the kernel accepted {label}"

/-- The constructor supplies the actual domain being tested. Each closed proof
    attempt must reach a guarded fast declaration and fail on its type. -/
private def checkTaboos : IO Unit := do
  let refl := ctor "Agda.Builtin.Equality._≡_.refl"
  let guessFalse := app (ctor "Data.Sum.Base._⊎_.inj₁") (lam ["n"] refl)
  let eq a b := app (app (ref "Agda.Builtin.Equality._≡_") a) b
  let existsTrue := app (ref "Data.Product.∃") (lam ["n"]
    (eq (app (.var "f") (.var "n")) (ctor "Agda.Builtin.Bool.Bool.true")))
  let pair := app (app (ctor "Agda.Builtin.Sigma._,_") (.lit (.natL 0))) refl
  let guessZero := Expr.let_ [.letBind "candidate" existsTrue pair] (.var "candidate")
  let taboo := ref "Context.Taboo.SafeTaboo"
  let cases :=
    [("taboo-⊥", ctor "Agda.Builtin.Unit.tt"),
     ("taboo-primStrRefl", lam ["s"] refl), ("taboo-primCharRefl", lam ["c"] refl),
     ("taboo-strRoundtrip", lam ["s"] refl), ("taboo-listRoundtrip", lam ["cs"] refl),
     ("taboo-funExtBool", lam ["f","g","pointwise"] refl),
     ("taboo-wlpo", lam ["f"] guessFalse), ("taboo-markov", lam ["f","neg"] guessZero)]
  let mismatch := fun (s : String) => s.toLower.contains "type mismatch"
  for (name,body) in cases do
    let cm := testModule "TabooProbe" taboo (app (ctor ("Context.Taboo.SafeTaboo." ++ name)) body)
    requireRejection name (← lower cm) mismatch
  -- The repository constructor uses an existential positive branch. Also
  -- exercise the weaker disjunction with negation and the Boolean-domain
  -- instance of function extensionality directly.
  let nat := ref "Agda.Builtin.Nat.Nat"
  let bool := ref "Agda.Builtin.Bool.Bool"
  let allFalse := pi "n" nat (eq (app (.var "f") (.var "n")) (ctor "Agda.Builtin.Bool.Bool.false"))
  let weak := pi "f" (arrow nat bool) (app (app (ref "Data.Sum.Base._⊎_") allFalse)
    (arrow allFalse (ref "Data.Empty.⊥")))
  requireRejection "weak WLPO" (← lower (testModule "WeakWLPO" weak (lam ["f"] guessFalse))) mismatch
  let pointwise := pi "b" bool (eq (app (.var "f") (.var "b")) (app (.var "g") (.var "b")))
  let ext := pi "f" (arrow bool bool) (pi "g" (arrow bool bool) (arrow pointwise (eq (.var "f") (.var "g"))))
  requireRejection "Bool-domain funext" (← lower (testModule "BoolExt" ext (lam ["f","g","h"] refl))) mismatch

/-- Model a corrupted lowering result after F_chk assigned its guards. A clean
    control must elaborate with the same residual and the same boundary. -/
private def checkHybrid : IO Unit := do
  let bool := ref "Agda.Builtin.Bool.Bool"
  let value := ctor "Agda.Builtin.Bool.Bool.true"
  let cm := testModule "HybridAudit" (arrow (ref "Agda.Builtin.Nat.Nat") bool) (lam ["n"] value)
  let cm := {cm with decls := cm.decls ++ [.sig {} "port" bool, .fun_ {} "port"
    [.clause (.head (mkQ ["HybridAudit","port"]) []) (.rhs value) []]]}
  let slice ← lower cm true
  discard <| KernelDriver.elaborate slice #[] true
  let nm := Lean.mkIdent <| (Lean.Name.mkSimple (leanModNamespace cm.modName.full)).str (leanMangleIdent "proof")
  -- The helper of a total fast declaration is a separate kernel constant.
  let helper := Lean.mkIdent `PartialAuditHelper
  let helperCmd ← IO.ofExcept <| Chk.out (show PrismOutcome Chk.Cmd from
    `(partial def $helper:ident (n : Nat) : Bool := $helper:ident n))
  let aliasCmd ← IO.ofExcept <| Chk.out (show PrismOutcome Chk.Cmd from
    `(def $nm:ident (n : Nat) : Bool := $helper:ident n))
  let mut aliased := #[]
  for d in slice.ordered do
    if d.origin.full == cm.modName.full ++ ["proof"] then
      aliased := aliased.push {d with syntaxOf := helperCmd} |>.push {d with syntaxOf := aliasCmd}
    else aliased := aliased.push d
  requireRejection "transitive partial def" {slice with ordered := aliased}
    (fun s => s.contains "disallowed axiom" && s.contains "unsafePrimAx")
  let smuggled : PrismOutcome (List (String × Chk.Cmd)) := do
    return [
      ("propext", ← `(def $nm:ident (_ : Nat) : Bool := (fun (_ : True = True) => true) (propext Iff.rfl))),
      ("Classical.choice", ← `(noncomputable def $nm:ident (_ : Nat) : Bool := Classical.choice (show Nonempty Bool from ⟨true⟩))),
      ("Quot.sound", ← `(def $nm:ident (_ : Nat) : Bool := (fun (_ : Quot.mk (fun _ _ : Nat => True) 0 = Quot.mk _ 1) => true) (Quot.sound trivial))),
      ("sorryAx", ← `(def $nm:ident (_ : Nat) : Bool := sorryAx Bool false)),
      ("partial def", ← `(partial def $nm:ident (n : Nat) : Bool := $nm:ident n))]
  for (name,cmd) in ← IO.ofExcept (Chk.out smuggled) do
    let commands := slice.ordered.map fun d =>
      if d.origin.full == cm.modName.full ++ ["proof"] then {d with syntaxOf := cmd} else d
    requireRejection name {slice with ordered := commands} (fun s =>
      if name == "partial def" then s.contains "missing checked fast declaration"
      else if name == "sorryAx" then s.contains "declaration uses `sorry`" || (s.contains "disallowed axiom" && s.contains name)
      else s.contains "disallowed axiom" && s.contains name)

def verify (lib : String) : IO Unit := do
  KernelDriver.preload lib
  checkTaboos
  checkHybrid

end Prism.Conservativity
