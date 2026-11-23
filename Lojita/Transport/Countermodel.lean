import Lojita.Transport.Lift

namespace Lojita.Transport
open Lean Lojita.Kernel

private def countermodelLib := `LojitaCtx.Countermodel
private def bridgeName := `CountermodelCheck

private def checkModelSurface (model : LeanMod) : Except String Unit := do
  let (m, cmds) ← (readEnvelope (renderLeanMod model)).mapError toString
  unless m.imports.all (·.imod.toLeanName == countermodelLib) &&
      m.modName.toLeanName.getRoot != bridgeName do
    throw "UNAUTHORIZED_IMPORT: model may import only LojitaCtx.Countermodel"
  let mut todo := cmds.toList
  while let x :: rest := todo do
    if x.isOfKind strLitKind || x.isOfKind interpolatedStrKind then
      throw "MODEL_STRING_LITERAL: string literals are forbidden in the model"
    todo := x.getArgs.toList ++ rest

/-- Project the claim by eliminating the actual checked bundle. This works for
    anonymous claims, private definitions and reducible aliases alike. -/
def synthesizeCountermodelBridge (modelSnap : Snapshot) : Except String LeanMod := do
  let ty := mkConst (countermodelLib ++ `CountermodelBundle)
  let some q := (modelSnap.mod.units.flatMap (·.definedNames)).find? (fun q =>
    let n := q.toLeanName
    !isPrivateName n && modelSnap.constants.contains n &&
      (modelSnap.env.find? n).any (fun c => c.levelParams.isEmpty &&
        Lean.Kernel.isDefEqGuarded modelSnap.env {} c.type ty)) |
    throw "MISSING_COUNTERMODEL_BUNDLE: expected a public CountermodelBundle"
  parseLeanMod s!"import LojitaCtx.Countermodel
import {modelSnap.mod.modName}
namespace CountermodelCheck
open LojitaCtx.Countermodel
def realStringAlg : StringAlg where
  Str := String
  toList := String.toList
  fromList := String.ofList
  append := String.append
  strEq := (· == ·)
  toListInjective := String.toList_inj.mp
  fromListInjective := String.ofList_inj.mp
def realCharAlg : CharAlg where
  Chr := Char
  charToNat := Char.toNat
  natToChar := Char.ofNat
  charEq := (· == ·)
  charToNatInjective := Char.toNat_inj.mp
def VerifiedClaim : Prop :=
  match {q} with
  | .stringCountermodel claim _ _ => claim realStringAlg
  | .charCountermodel claim _ _ => claim realCharAlg
end CountermodelCheck"

def checkModelDraft (modelMod : LeanMod) : IO LeanMod := do
  IO.ofExcept (checkModelSurface modelMod)
  let snap ← checkClosedModule [] modelMod
  unless snap.declaredAxioms.isEmpty do throw (IO.userError "DISALLOWED_AXIOM_VIOLATION: model")
  for n in snap.constants do
    if let some c := snap.env.find? n then
      if c.getUsedConstantsAsSet.any (fun dep => dep.getRoot == `String) then
        throw (IO.userError s!"MODEL_PRIMITIVE: native String in {n}")
  IO.ofExcept (synthesizeCountermodelBridge snap)

def checkCountermodel (closedBases : List LeanMod) (specMod modelMod refuteMod : LeanMod) : IO Snapshot := do
  unless refuteMod.imports.any (·.imod.toLeanName == bridgeName) do
    throw (IO.userError "UNAUTHORIZED_IMPORT: witness must import CountermodelCheck")
  let bridge ← checkModelDraft modelMod
  let deps := closedBases ++ [modelMod, bridge]
  witnessBoundary deps specMod refuteMod
  checkRefutation deps (stubOf specMod) refuteMod [`CountermodelCheck.VerifiedClaim]

end Lojita.Transport
