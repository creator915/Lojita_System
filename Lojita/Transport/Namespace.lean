import Lojita.Transport.Plan

namespace Lojita.Transport
open Lojita.Kernel

inductive NamespaceProblem where
  | invalidSlotSegment (s : String)
  | duplicateChildSlot (s : String)
  | metaNamespaceCollision (q : QName)
  | forbiddenSiblingOrExternalImport (q : QName)
  deriving Repr, BEq

def validSegment (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun x => x.isAlphanum || x == '_') &&
    !["code", "memory", "spec", "ai", "child", "dump", "lean", "import", "open", "namespace", "end"].contains s

def checkTaskImports (owner : QName) (owned bases : List QName) (m : LeanMod) : List NamespaceProblem := Id.run do
  let allowed := Std.HashSet.ofList (owned ++ bases)
  let mut problems := #[]
  unless ordinaryPath m.modName && m.modName == owner do problems := problems.push (.metaNamespaceCollision m.modName)
  for i in m.imports do
    if !allowedImport i.imod then problems := problems.push (.metaNamespaceCollision i.imod)
    else if i.imod.toLeanName.getRoot != `LojitaCtx && !allowed.contains i.imod then
      problems := problems.push (.forbiddenSiblingOrExternalImport i.imod)
  return problems.toList

def checkOwnedNames (parent : QName) (owned retained bases : List QName) : List NamespaceProblem := Id.run do
  let mut seen : Std.HashSet String := {}
  let known := Std.HashSet.ofList retained
  let external := Std.HashSet.ofList bases
  let mut problems := #[]
  for q in owned do
    let slot := q.segments.getLast?.getD ""
    if !validSegment slot then problems := problems.push (.invalidSlotSegment slot)
    if seen.contains slot then problems := problems.push (.duplicateChildSlot slot)
    seen := seen.insert slot
    let epochChild := match parent.segments, q.segments with
      | ["Gen", a, "Root"], ["Gen", b, k] => a == b && k != "Root"
      | _, _ => false
    if !ordinaryPath q then problems := problems.push (.metaNamespaceCollision q)
    else if !known.contains q && (external.contains q || (parent.segments.head? == some "Gen" &&
        !(q.segments == parent.segments ++ [slot] || epochChild))) then
      problems := problems.push (.forbiddenSiblingOrExternalImport q)
  return problems.toList

def checkOwnedImports (parent : QName) (owned retained bases : List QName) (m : LeanMod) :=
  checkOwnedNames parent owned retained bases ++ checkTaskImports parent owned bases m

end Lojita.Transport
