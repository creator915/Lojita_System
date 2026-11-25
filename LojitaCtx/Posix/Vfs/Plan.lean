import LojitaCtx.Posix.Vfs.Graph

namespace LojitaCtx.Posix

/-- Directory navigation is independent of the contents of regular files and
    of leaf dentries that cannot be traversed as path prefixes. -/
structure Nav where
  parent : Nat → Option Nat
  step : Nat → Seg → Option Nat
  link : Nat → Option Bytes

def InodeTable.parentOf (t : InodeTable) (id : Nat) : Option Nat := do
  let .dir parent _ := (← t.nodes[id]?).payload | none
  return parent

def InodeTable.entryAt (t : InodeTable) (id : Nat) (s : Seg) : Option Nat := do
  let .dir _ es := (← t.nodes[id]?).payload | none
  es[s]?

def InodeTable.linkAt (t : InodeTable) (id : Nat) : Option Bytes := do
  let .symlink bs := (← t.nodes[id]?).payload | none
  return bs

def InodeTable.nav (t : InodeTable) : Nav where
  parent := t.parentOf
  link := t.linkAt
  step i s := do
    let j ← t.entryAt i s
    if (t.parentOf j).isSome || (t.linkAt j).isSome then some j else none

structure NavClosed (g : Nav) (root : Nat) (S : Nat → Prop) : Prop where
  parent : ∀ i j, i ≠ root → S i → g.parent i = some j → S j
  step : ∀ i s j, S i → g.step i s = some j → S j

abbrev NavReach (g : Nav) (r start n : Nat) :=
  ∀ S, NavClosed g r S → S r → S start → S n

structure Plan (g : Nav) (r start fuel : Nat) where
  parent : Nat
  reach : NavReach g r start parent
  name : Seg
  remaining : Nat
  bounded : remaining ≤ fuel
  /-- A missing/nondirectory intermediate component needs a real errno. -/
  blocked : Bool

private def Plan.weaken {g r start f k} (p : Plan g r start f) (h : f ≤ k) :
    Plan g r start k := {p with bounded := Nat.le_trans p.bounded h}

def pathComponents (p : Bytes) := (p.splitOn 47).filter (!·.isEmpty)

def checkNamePath (p : Bytes) : Except Errno Unit := do
  if p.contains 0 then throw .EINVAL
  if p.isEmpty then throw .ENOENT
  if p.length ≥ 4096 then throw .ENAMETOOLONG

def Nav.plan (g : Nav) (r start fuel cur : Nat) (hc : NavReach g r start cur)
    (parts : List Seg) : Except Errno (Plan g r start fuel) := do
  match hp : g.parent cur with
  | none => throw .ENOTDIR
  | some parent =>
    match parts with
    | [] => return ⟨cur,hc,[46],fuel,Nat.le_refl _,false⟩
    | s :: rest =>
      if s.length > 255 then throw .ENAMETOOLONG
      if rest.isEmpty then return ⟨cur,hc,s,fuel,Nat.le_refl _,false⟩
      if s == [46] then return ← plan g r start fuel cur hc rest
      if s == [46,46] then
        if atRoot : cur = r then return ← plan g r start fuel cur hc rest
        else
          return ← plan g r start fuel parent (fun _ closed hr hs => closed.parent _ _ atRoot (hc _ closed hr hs) hp) rest
      match h : g.step cur s with
      | none => return ⟨cur,hc,s,fuel,Nat.le_refl _,true⟩
      | some dst =>
        match g.link dst with
        | none => return ← plan g r start fuel dst (fun _ c hr hs => c.step _ _ _ (hc _ c hr hs) h) rest
        | some target =>
          match hf : fuel with
          | 0 => throw .ELOOP
          | f+1 =>
            checkNamePath target
            let ⟨c,hc'⟩ : {i // NavReach g r start i} := if target.head? == some 47 then
              ⟨r,fun _ _ hr _ => hr⟩ else ⟨cur,hc⟩
            let p ← plan g r start f c hc' (pathComponents target ++ rest)
            return p.weaken (by omega)
termination_by (fuel, parts.length)
decreasing_by all_goals simp_wf <;> omega

structure PathPrefix (fuel : Nat) where
  parent : Nat
  name : Seg
  remaining : Nat
  bounded : remaining ≤ fuel
  blocked : Bool

def Nav.prepare (g : Nav) (root start fuel : Nat) (p : Bytes) : Except Errno (PathPrefix fuel) := do
  checkNamePath p
  let cur : {i // NavReach g root start i} := if p.head? == some 47 then
    ⟨root,fun _ _ hr _ => hr⟩ else ⟨start,fun _ _ _ hs => hs⟩
  let plan ← g.plan root start fuel cur.val cur.property (pathComponents p)
  return ⟨plan.parent,plan.name,plan.remaining,plan.bounded,plan.blocked⟩

theorem Nav.prepare_reach (g : Nav) (root start fuel : Nat) (p : Bytes) (a : PathPrefix fuel)
    (h : g.prepare root start fuel p = .ok a) : NavReach g root start a.parent := by
  unfold Nav.prepare at h
  cases c : checkNamePath p <;> simp [c, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  split at h
  · contradiction
  · cases h; exact (by assumption : Plan g root start fuel).reach

end LojitaCtx.Posix
