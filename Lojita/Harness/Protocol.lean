import Lojita.Harness.NodeTransport
import Lojita.Harness.Submission

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport

structure NodeTask where
  delta : SpecDelta
  baseModules : List LeanMod := []
  transports : Bindings := []
  maybeLift : Option (LeanMod × LiftSpec) := none
  /-- A merge can assign more than one vertical obligation to the same child. -/
  otherLifts : List (LeanMod × LiftSpec) := []
  allowedAncestors : Option (List QName) := none
  parentFlags : List String := []
  contextText : String := ""
  drafts : DraftStore := {}

def NodeTask.lifts (t : NodeTask) := t.maybeLift.toList ++ t.otherLifts

inductive Verdict where
  | ok
  | contradiction (proof : LeanMod)
  | liftObstruction (why : String) (culprits : List QName) (proof : LeanMod)
  | countermodel (why : String) (model proof : LeanMod)
  deriving BEq, Repr, Inhabited

structure NarrowingCertificate where
  kind : String
  witness : String
  cause : String
  detour : String
  deriving BEq, Repr, Inhabited, Lean.ToJson

instance : ToString NarrowingCertificate where
  toString c := s!"[KIND] {c.kind}\n[WITNESS] {c.witness}\n[CAUSE] {c.cause}\n[DETOUR] {c.detour}"

structure AIRequest where
  task : NodeTask
  old : LeanMod
  memory : Memory
  diagnostic : Option NarrowingCertificate
  home : Option Frozen := none

end Lojita.Harness
