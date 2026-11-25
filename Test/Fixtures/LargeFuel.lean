namespace Gen.LargeFuel

def bigBudget : Nat := UInt64.size

def scan : Nat → List UInt8 → Nat
  | 0, _ => 0
  | fuel + 1, xs =>
    match xs with
    | [] => 0
    | _ :: rest => scan fuel rest + 1
termination_by structural fuel _ => fuel

def run (xs : List UInt8) := scan bigBudget xs

theorem runLaw (xs : List UInt8) : run xs = scan bigBudget xs := rfl

end Gen.LargeFuel
