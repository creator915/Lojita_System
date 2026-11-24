import Lojita.Harness.NodeTransport
import Lojita.Harness.Submission

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport

structure NodeTask where
  delta : SpecDelta
  baseModules : List LeanMod := []
  /-- Pinned vertical environment of the saved code, used only to check its history. -/
  oldBaseModules : Option (List LeanMod) := none
  /-- A partial home may borrow missing slots from a different complete commit. -/
  otherChildHistory : Option (List String × List LeanMod) := none
  transports : Bindings := []
  maybeLift : Option (LeanMod × LiftSpec) := none
  /-- A merge can assign more than one vertical obligation to the same child. -/
  otherLifts : List (LeanMod × LiftSpec) := []
  allowedAncestors : Option (List QName) := none
  parentFlags : List String := []
  contextText : String := ""
  drafts : DraftStore := {}

def NodeTask.lifts (t : NodeTask) := t.maybeLift.toList ++ t.otherLifts

def NodeTask.snapshotModules (t : NodeTask) : List LeanMod :=
  t.transports.flatMap fun (h,_) => Lojita.Harness.snapshotModules h
    (if h.code.modName == t.delta.child then t.oldBaseModules.getD t.baseModules else t.baseModules) t.baseModules

def NodeTask.allowedImports (t : NodeTask) : List QName :=
  let vertical := t.allowedAncestors.getD ((t.baseModules.map (·.modName)) ++ t.lifts.map (·.1.modName))
  distinct (vertical ++ t.transports.flatMap fun (h,_) =>
    h.code.modName :: (exported h).map (oldSnapshotPrefix ·.modName))

/-- Stubs and the candidate occupy their own names in the checking environment.
    Old snapshots are materialized only for a draft that imports one. -/
def NodeTask.checkingDeps (t : NodeTask) (owner : QName) (slots : List QName) (useSnapshots := false) :=
  let shadowed := Std.HashSet.ofList (owner :: slots)
  let sources := t.transports.flatMap (exported ·.1) ++ t.lifts.map Prod.fst
  mergeModules ((t.baseModules ++ sources).filter (fun m => !shadowed.contains m.modName) ++
    (if useSnapshots then t.snapshotModules else []))

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
