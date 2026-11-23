import Lojita.Harness.Core

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport

def planPreview (t : NodeTask) (old : Frozen) (p : Plan) (subspecs : List LeanMod := []) : IO GateReport :=
  Prod.fst <$> checkCandidateGates t old p subspecs

def checkPlanJSON (t : NodeTask) (old : Frozen) (p : Plan) (subspecs : List LeanMod := []) : IO String :=
  return (Lean.toJson (← planPreview t old p subspecs)).compress

end Lojita.Harness
