import Lojita.Transport.Plan
import Lojita.Ownership.IO

namespace Lojita.Harness
open Lojita.Kernel Lojita.Transport Lojita.Ownership

inductive HomeShape where
  | node (children : List (String × HomeShape))

inductive Frozen where
  | frozen (code : LeanMod) (memory : Memory) (spec : LeanMod) (children : List (String × Frozen))
  deriving Inhabited

def Frozen.code : Frozen → LeanMod | .frozen c _ _ _ => c
def Frozen.memory : Frozen → Memory | .frozen _ m _ _ => m
def Frozen.spec : Frozen → LeanMod | .frozen _ _ s _ => s
def Frozen.children : Frozen → List (String × Frozen) | .frozen _ _ _ cs => cs

abbrev Leaves : Ctx := [("code", .file LeanMod), ("memory", .file Memory), ("spec", .file LeanMod)]
abbrev Home (kids : Ctx) : Ctx := kids ++ Leaves

mutual
  def HomeCtx (sh : HomeShape) : Ctx :=
    match sh with | .node ks => KidsCtx ks
  termination_by structural sh

  def KidsCtx (ks : List (String × HomeShape)) : Ctx :=
    match ks with
    | [] => []
    | (n, sh) :: rest => (n, .dir (Home (HomeCtx sh))) :: KidsCtx rest
  termination_by structural ks
end

abbrev HomeSt (sh : HomeShape) := St.dir (Home (HomeCtx sh))
abbrev HomeValue := (sh : HomeShape) × ModelIO (HomeSt sh)

mutual
  def freezeHome (sh : HomeShape) : ModelIO (HomeSt sh) → Frozen :=
    match sh with | .node ks => freezeKids ks []
  termination_by structural sh

  private def freezeKids (ks : List (String × HomeShape)) (acc : List (String × Frozen)) :
      ModelsIO (Home (KidsCtx ks)) → Frozen :=
    match ks with
    | [] => fun (c,m,s,_) => .frozen c m s acc.reverse
    | (n,sh) :: rest => fun (v,vs) => freezeKids rest ((n, freezeHome sh v) :: acc) vs
  termination_by structural ks
end

mutual
  def thawHome (f : Frozen) : HomeValue :=
    match f with
    | .frozen c m s ks =>
      let ⟨ss, v⟩ := thawKids ks (c,m,s,())
      ⟨.node ss, v⟩
  termination_by structural f

  private def thawKids (ks : List (String × Frozen)) (leaves : ModelsIO Leaves) :
      (ss : List (String × HomeShape)) × ModelsIO (Home (KidsCtx ss)) :=
    match ks with
    | [] => ⟨[], leaves⟩
    | (n,f) :: rest =>
      let ⟨sh,v⟩ := thawHome f
      let ⟨ss,vs⟩ := thawKids rest leaves
      ⟨(n,sh) :: ss, (v,vs)⟩
  termination_by structural ks
end

/- Consume a directory from the head. Each position is visited once, even
    when several thousand children share the same parent. -/
mutual
  def drainHome {Ψ : List Spec} (sh : HomeShape) : Prog Ψ (HomeSt sh) (.dir []) Frozen :=
    match sh with | .node ks => drainKids ks []
  termination_by structural sh

  private def drainKids {Ψ : List Spec} (ks : List (String × HomeShape)) (acc : List (String × Frozen)) :
      Prog Ψ (.dir (Home (KidsCtx ks))) (.dir []) Frozen :=
    match ks with
    | [] =>
      .focus (.here rfl) read fun c => .step (.unlink (.here rfl) rfl) fun _ =>
      .focus (.here rfl) read fun m => .step (.unlink (.here rfl) rfl) fun _ =>
      .focus (.here rfl) read fun s => .step (.unlink (.here rfl) rfl) fun _ =>
      .done (.frozen c m s acc.reverse)
    | (n,sh) :: rest => .focus (.here rfl) (drainHome sh) fun f =>
      .step (.rmdir (.here rfl) rfl) fun _ => drainKids rest ((n,f) :: acc)
  termination_by structural ks
end

end Lojita.Harness
