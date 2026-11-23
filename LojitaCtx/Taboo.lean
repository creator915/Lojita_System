namespace LojitaCtx

/-- The closed string, character and logical claims that a node may exhibit. -/
inductive SafeTaboo : Type where
  | bottom (refutation : False)
  | primStrRefl (law : ∀ s : String, (s == s) = true)
  | primCharRefl (law : ∀ c : Char, (c == c) = true)
  | strRoundtrip (law : ∀ s : String, String.ofList s.toList = s)
  | listRoundtrip (law : ∀ cs : List Char, (String.ofList cs).toList = cs)
  | funExtBool (law : ∀ f g : Nat → Bool, (∀ n, f n = g n) → f = g)
  | wlpo (law : ∀ f : Nat → Bool, (∀ n, f n = false) ∨ ∃ n, f n = true)
  | markov (law : ∀ f : Nat → Bool, (¬ ∀ n, f n = false) → ∃ n, f n = true)

end LojitaCtx
