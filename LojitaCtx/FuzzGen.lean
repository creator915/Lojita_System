import LojitaCtx.Terminal

namespace LojitaCtx.FuzzGen

open LojitaCtx.Terminal

structure Seed : Type where
  seed ::
  state : Nat

def mkSeed (n : Nat) : Seed :=
  Seed.seed (n % 4294967296)

def nextNat (s : Seed) : Nat × Seed :=
  let n := (1664525 * s.state + 1013904223) % 4294967296
  Prod.mk n (Seed.seed n)

abbrev Gen (A : Type) : Type :=
  Seed → (A × Seed)

def runGen {A : Type} (g : Gen A) (s : Seed) : (A × Seed) :=
  g s

def genPure {A : Type} (a : A) (s : Seed) : (A × Seed) :=
  Prod.mk a s

def genMap {A B : Type} (f : A → B) (g : Gen A) (s : Seed) : (B × Seed) :=
  let r := g s
  Prod.mk (f r.1) r.2

def genBind {A B : Type} (g : Gen A) (f : A → Gen B) (s : Seed) : (B × Seed) :=
  let r := g s
  f r.1 r.2

def genPair {A B : Type} (a : Gen A) (b : Gen B) : Gen (A × B) :=
  genBind a fun x => genMap (fun y => Prod.mk x y) b

def genBounded (n : Nat) : Gen Nat :=
  genMap (fun k => (k % (Nat.succ n))) nextNat

def genBool : Gen Bool :=
  genMap (fun n => (n == 1)) (genBounded 1)

def genByte : Gen Byte :=
  genMap byte (genBounded 255)

def genList {A : Type} : Nat → Gen A → Gen (List A)
  | 0, _          => genPure []
  | Nat.succ n, g => genBind g (fun x => genMap (fun xs => x :: xs) (genList n g))
termination_by structural n _ => n

def genBytes (n : Nat) : Gen Bytes :=
  genBind (genBounded n) (fun k => genList k genByte)

def chooseAt {A : Type} (d : A) : Nat → List A → A
  | _, []               => d
  | 0, x :: _           => x
  | Nat.succ n, _ :: xs => chooseAt d n xs
termination_by structural _ xs => xs

def genChoose {A : Type} (d : A) (xs : List A) : Gen A :=
  genMap (fun n => chooseAt d n (d :: xs)) (genBounded (List.length xs))

def sampleMany {A : Type} : Nat → Gen A → Seed → List A
  | 0, _, _          => []
  | Nat.succ n, g, s =>
      let r := g s
      r.1 :: sampleMany n g r.2
termination_by structural n _ _ => n

abbrev Shrinker (A : Type) : Type :=
  A → List A

def shrinkNat : Nat → List Nat
  | 0 => []
  | Nat.succ n =>
    let h := Nat.succ n / 2
    0 :: ((if h == 0 then [] else [h]) ++ if n == 0 then [] else if n == h then [] else [n])

def shrinkByte (b : Byte) : List Byte :=
  List.map byte (shrinkNat (UInt8.toNat b))

def shrinkList {A : Type} (shrink : Shrinker A) : List A → List (List A)
  | [] => []
  | x :: xs =>
    xs ::
      (List.map (fun y => y :: xs) (shrink x) ++
        List.map (fun ys => x :: ys) (shrinkList shrink xs))
termination_by structural xs => xs

def shrinkBytes : Shrinker Bytes :=
  shrinkList shrinkByte

def firstFailure {A : Type} (ok : A → Bool) : List A → Option A
  | []      => .none
  | x :: xs => (if (ok x) then (firstFailure ok xs) else (.some x))
termination_by structural xs => xs

def minimize {A : Type} : Nat → Shrinker A → (A → Bool) → A → A
  | 0, _, _, x               => x
  | Nat.succ fuel, sh, ok, x =>
      match firstFailure ok (sh x) with
      | .none => x
      | .some y  => minimize fuel sh ok y
termination_by structural fuel _ _ _ => fuel

def fuzzCheck {A : Type} : Nat → Nat → Gen A → Shrinker A → (A → Bool) → Seed → Option A
  | 0, _, _, _, _, _                    => .none
  | Nat.succ count, fuel, g, sh, ok, s  =>
      let r := g s
      (if (ok r.1) then (fuzzCheck count fuel g sh ok r.2) else (.some (minimize fuel sh ok r.1)))
termination_by structural count _ _ _ _ _ => count

end LojitaCtx.FuzzGen
