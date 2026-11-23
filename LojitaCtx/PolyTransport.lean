import LojitaCtx.Blueprint

namespace LojitaCtx.PolyTransport

structure PortRel (A B : Type) where
  rel : A → B → Prop

variable {A B C D E F U V : Type}

def idPort (A : Type) : PortRel A A := ⟨Eq⟩
def equivPort (r : A → A → Prop) : PortRel A A := ⟨r⟩
def graphPort (f : A → B) : PortRel A B := ⟨fun a b => f a = b⟩
def cographPort (g : B → A) : PortRel A B := ⟨fun a b => a = g b⟩
def tensorPort (p : PortRel A B) (q : PortRel C D) : PortRel (A × C) (B × D) :=
  ⟨fun x y => p.rel x.1 y.1 ∧ q.rel x.2 y.2⟩
def splitPort (f : A → B × C) := graphPort f
def mergePort (f : A × B → C) := graphPort f
def introPort (B : Type) : PortRel Unit B := ⟨fun _ _ => True⟩
def elimPort (A : Type) : PortRel A Unit := ⟨fun _ _ => True⟩
def compPort (p : PortRel A B) (q : PortRel B C) : PortRel A C :=
  ⟨fun a c => ∃ b, p.rel a b ∧ q.rel b c⟩
def cut₁ (f : A → B × C) (g : B → D) (a : A) := Prod.map g id (f a)
def cutRel (r : A → B → C → Prop) (s : B → D → Prop) (a : A) (d : D) (c : C) :=
  ∃ b, r a b c ∧ s b d

def TransportsPoly (p : PortRel A B) (q : PortRel C D) (Dom : A → Prop)
    (f : A → C) (g : B → D) := ∀ x y, Dom x → p.rel x y → q.rel (f x) (g y)
abbrev Transports₁ (p : PortRel A B) (q : PortRel C D) (Dom : A → Prop)
    (f : A → C) (g : B → D) := TransportsPoly p q Dom f g
def Transports₂ (p : PortRel A B) (q : PortRel C D) (r : PortRel E F)
    (Dom : A → C → Prop) (f : A → C → E) (g : B → D → F) :=
  ∀ x z y w, Dom x z → p.rel x y → q.rel z w → r.rel (f x z) (g y w)

theorem composeTransportsCut {p : PortRel A B} {q : PortRel C D} {r : PortRel E F} {s : PortRel U V}
    {f : A → C × E} {g : B → D × F} {h : C → U} {k : D → V}
    (first : TransportsPoly p (tensorPort q r) (fun _ => True) f g)
    (second : TransportsPoly q s (fun _ => True) h k) :
    TransportsPoly p (tensorPort s r) (fun _ => True) (cut₁ f h) (cut₁ g k) := by
  intro x y dom rel
  obtain ⟨mid, side⟩ := first x y dom rel
  exact ⟨second _ _ trivial mid, side⟩

theorem transportLiftCube (p : U → A) (q : V → B) {Dom : U → Prop} {f g : A → B} {u : U → V}
    (base : TransportsPoly (idPort A) (idPort B) (fun _ => True) f g)
    (upper : ∀ x, Dom x → q (u x) = f (p x)) :
    ∀ x, Dom x → q (u x) = g (p x) :=
  fun x d => (upper x d).trans (base _ _ trivial rfl)

end LojitaCtx.PolyTransport
