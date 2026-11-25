namespace LojitaCtx.Blueprint

structure PortLift (Base Upper : Type) where
  project : Upper → Base

variable {A B C D U V W X : Type}

def keepPort (A : Type) : PortLift A A := ⟨id⟩
def fromEl (El : A → Type) : PortLift A (Sigma El) := ⟨Sigma.fst⟩
def FiberOf (p : PortLift B U) (b : B) := {u : U // p.project u = b}
def composeLift (p : PortLift A B) (q : PortLift B C) : PortLift A C := ⟨p.project ∘ q.project⟩

def Commutes₁ (p : PortLift A U) (q : PortLift B V)
    (Dom : U → Prop) (rel : B → B → Prop) (f : A → B) (g : U → V) : Prop :=
  ∀ u, Dom u → rel (q.project (g u)) (f (p.project u))

def Commutes₂ (p : PortLift A U) (q : PortLift B V) (r : PortLift C W)
    (Dom : U → V → Prop) (rel : C → C → Prop) (f : A → B → C) (g : U → V → W) : Prop :=
  ∀ u v, Dom u v → rel (r.project (g u v)) (f (p.project u) (q.project v))

def Commutes₃ (p : PortLift A U) (q : PortLift B V) (r : PortLift C W) (s : PortLift D X)
    (Dom : U → V → W → Prop) (rel : D → D → Prop) (f : A → B → C → D) (g : U → V → W → X) : Prop :=
  ∀ u v w, Dom u v w → rel (s.project (g u v w)) (f (p.project u) (q.project v) (r.project w))

end LojitaCtx.Blueprint
