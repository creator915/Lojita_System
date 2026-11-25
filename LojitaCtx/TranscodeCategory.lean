namespace LojitaCtx.TranscodeCategory

inductive BasePt where | star
inductive BasePolyOp : List BasePt → BasePt → Type where
  | idOp : BasePolyOp [.star] .star
  | splitOp : BasePolyOp [.star] .star
  | projectShellOp : BasePolyOp [.star] .star
  | stepOp : BasePolyOp [.star] .star
  | gluePushoutOp : BasePolyOp [.star, .star, .star] .star
  | consOp : BasePolyOp [.star, .star] .star
  | compOp {xs ys zs : List BasePt} : BasePolyOp xs .star → BasePolyOp (ys ++ .star :: zs) .star →
      BasePolyOp (ys ++ xs ++ zs) .star

inductive SliceColor where | sharedBase | sweetMod | exoMod | mixMod
inductive DeclSort where | baseType | pureSigHelper | sweetBody | exoBody | boundaryHole

def DeclSort.ctorIdx : DeclSort → Nat
  | .baseType => 0 | .pureSigHelper => 1 | .sweetBody => 2 | .exoBody => 3 | .boundaryHole => 4
deriving instance DecidableEq for DeclSort

def DeclSort.shared : DeclSort → Bool
  | .baseType | .pureSigHelper => true
  | _ => false

def Allowed : SliceColor → DeclSort → Prop
  | .sharedBase, k => k.shared
  | .sweetMod, k => k ≠ .exoBody
  | .exoMod, k => k ≠ .sweetBody
  | .mixMod, _ => True

structure DeclEntry (Sym : Type) where
  symbol : Sym
  sort : DeclSort
  sigDeps : List Sym
  bodyDeps : List Sym
  holeEmpty : sort = .boundaryHole → bodyDeps = []
  deriving DecidableEq

variable {Sym : Type}

def decl (key : Sym) (k : DeclSort) (sig body : List Sym) : DeclEntry Sym :=
  ⟨key, k, sig, if k = .boundaryHole then [] else body, fun h => by simp [h]⟩

def DeclEntry.deps (d : DeclEntry Sym) := d.sigDeps ++ d.bodyDeps
def toBoundary (d : DeclEntry Sym) : DeclEntry Sym := ⟨d.symbol, .boundaryHole, d.sigDeps, [], fun _ => rfl⟩
abbrev dom (xs : List (DeclEntry Sym)) := xs.map DeclEntry.symbol
abbrev DownClosed (xs : List (DeclEntry Sym)) := ∀ d ∈ xs, d.deps ⊆ dom xs
abbrev NoDupSyms (xs : List (DeclEntry Sym)) := (dom xs).Nodup

structure CodePoint (Sym : Type) where
  entries : List (DeclEntry Sym)
  unique : NoDupSyms entries
  closed : DownClosed entries

abbrev HasSliceColor (c : SliceColor) (m : CodePoint Sym) :=
  ∀ d ∈ m.entries, Allowed c d.sort
abbrev El (Sym : Type) (_ : BasePt) := CodePoint Sym
abbrev Colored (Sym : Type) (c : SliceColor) := {m : CodePoint Sym // HasSliceColor c m}

theorem singletonDangling : ¬DownClosed [decl true .sweetBody [false] []] := by
  intro h
  have := h _ (List.mem_singleton_self _) (a := false) (by decide)
  contradiction

private theorem keyUnique {xs : List (DeclEntry Sym)} (u : NoDupSyms xs)
    {a b : DeclEntry Sym} (ha : a ∈ xs) (hb : b ∈ xs) (eq : a.symbol = b.symbol) : a = b := by
  induction xs with
  | nil => contradiction
  | cons d ds ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp u
    rcases List.mem_cons.mp ha with rfl | ra <;> rcases List.mem_cons.mp hb with rfl | rb
    · rfl
    · exact False.elim (fresh (by rw [eq]; exact List.mem_map_of_mem rb))
    · exact False.elim (fresh (by rw [← eq]; exact List.mem_map_of_mem ra))
    · exact ih rest ra rb

private def select (m : CodePoint Sym) (p : DeclEntry Sym → Bool)
    (follows : ∀ d ∈ m.entries, p d → ∀ e ∈ m.entries, e.symbol ∈ d.deps → p e) : CodePoint Sym where
  entries := m.entries.filter p
  unique := (List.filter_sublist.map DeclEntry.symbol).nodup m.unique
  closed := by
    intro d hd s hs
    obtain ⟨member, ok⟩ := List.mem_filter.mp hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (m.closed d member hs)
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨he, follows d member ok e he hs⟩)

def checkPoint [DecidableEq Sym] (ds : List (DeclEntry Sym)) : Option (CodePoint Sym) :=
  if hu : NoDupSyms ds then
    if hc : ∀ d ∈ ds, ∀ s ∈ d.deps, s ∈ dom ds then some ⟨ds, hu, fun d hd _ hs => hc d hd _ hs⟩
    else none
  else none

abbrev Stable (ds : List (DeclEntry Sym)) (names : List Sym) :=
  ∀ d ∈ ds, d.symbol ∈ names → d.deps ⊆ names

structure Closure (ds : List (DeclEntry Sym)) (seeds : List Sym) where
  names : List Sym
  contains : seeds ⊆ names
  follows : Stable ds names
  least : ∀ zs, seeds ⊆ zs → Stable ds zs → names ⊆ zs

variable [DecidableEq Sym]

/-- Each visit consumes one enabled declaration. Duplicate seeds and cycles
    therefore terminate with the same least closed set of names. -/
private def visit (fuel : Nat) (ds : List (DeclEntry Sym)) (bound : ds.length ≤ fuel)
    (ss : List Sym) : Closure ds ss :=
  match fuel with
  | 0 => by
    have empty : ds = [] := List.length_eq_zero_iff.mp (by omega)
    exact ⟨ss, fun _ h => h, by simp [empty, Stable], fun _ sub _ => sub⟩
  | n + 1 =>
    match found : ds.find? (fun d => decide (d.symbol ∈ ss)) with
    | none => ⟨ss, fun _ h => h, by
        intro d hd h
        exact False.elim ((List.find?_eq_none.mp found d hd) (decide_eq_true h)),
        fun _ sub _ => sub⟩
    | some e =>
      have he := List.mem_of_find?_eq_some found
      have enabled : e.symbol ∈ ss := of_decide_eq_true (List.find?_some (p := fun d : DeclEntry Sym => decide (d.symbol ∈ ss)) found)
      have smaller : (ds.erase e).length ≤ n := by rw [List.length_erase_of_mem he]; omega
      let child := visit n (ds.erase e) smaller (e.deps ++ ss)
      ⟨child.names, fun _ h => child.contains (List.mem_append_right _ h), by
        intro d hd on
        by_cases eq : d = e
        · subst d; exact fun _ dep => child.contains (List.mem_append_left _ dep)
        · exact child.follows d ((List.mem_erase_of_ne eq).mpr hd) on, by
        intro zs roots stable
        apply child.least
        · intro s hs
          exact (List.mem_append.mp hs).elim (stable e he (roots enabled) ·) (roots ·)
        · exact fun d hd => stable d (List.erase_subset hd)⟩
termination_by structural fuel

def reachable (ds : List (DeclEntry Sym)) (seeds : List Sym) : Closure ds seeds :=
  visit ds.length ds (Nat.le_refl _) seeds

private def trim (m : CodePoint Sym) (ss : List Sym) : CodePoint Sym :=
  let r := reachable m.entries ss
  select m (fun d => decide (d.symbol ∈ r.names)) fun d hd ok _ _ dep =>
    decide_eq_true (r.follows d hd (of_decide_eq_true ok) dep)

private theorem trimMem (m : CodePoint Sym) (ss : List Sym) {d : DeclEntry Sym} :
    d ∈ (trim m ss).entries ↔ d ∈ m.entries ∧ d.symbol ∈ (reachable m.entries ss).names := by
  simp [trim, select]

private def clean (m : CodePoint Sym) (d : DeclEntry Sym) : Bool :=
  let names := (reachable m.entries [d.symbol]).names
  m.entries.all fun e => decide (e.symbol ∈ names → e.sort.shared = true)

private theorem cleanIff (m : CodePoint Sym) (d : DeclEntry Sym) : clean m d ↔
    ∀ e ∈ m.entries, e.symbol ∈ (reachable m.entries [d.symbol]).names → e.sort.shared = true := by
  simp only [clean, List.all_eq_true, decide_eq_true_eq]

def computeSharedBase (m : CodePoint Sym) : CodePoint Sym :=
  select m (clean m) fun d hd ok e _ dep => by
    apply (cleanIff m e).2
    intro z hz reach
    let fromD := reachable m.entries [d.symbol]
    have seed := fromD.follows d hd (fromD.contains (List.mem_singleton_self _)) dep
    exact (cleanIff m d).1 ok z hz ((reachable m.entries [e.symbol]).least fromD.names
      (by simpa using seed) fromD.follows reach)

theorem sharedColor (m : CodePoint Sym) : HasSliceColor .sharedBase (computeSharedBase m) := by
  intro d h
  obtain ⟨mem, ok⟩ := List.mem_filter.mp h
  exact (cleanIff m d).1 ok d mem ((reachable m.entries [d.symbol]).contains (by simp))

omit [DecidableEq Sym] in
private theorem stableSubmodule (m b : CodePoint Sym) (sub : b.entries ⊆ m.entries) :
    Stable m.entries (dom b.entries) := by
  intro d hd key
  obtain ⟨e, he, eq⟩ := List.mem_map.mp key
  cases keyUnique m.unique (sub he) hd eq
  exact b.closed _ he

theorem sharedGreatest (m b : CodePoint Sym) (sub : b.entries ⊆ m.entries)
    (color : HasSliceColor .sharedBase b) : b.entries ⊆ (computeSharedBase m).entries := by
  intro d hd
  apply List.mem_filter.mpr ⟨sub hd, (cleanIff m d).2 ?_⟩
  intro e he key
  have mem := (reachable m.entries [d.symbol]).least (dom b.entries)
    (by simpa using (List.mem_map_of_mem (f := DeclEntry.symbol) hd)) (stableSubmodule m b sub) key
  obtain ⟨f, hf, eq⟩ := List.mem_map.mp mem
  cases keyUnique m.unique (sub hf) he eq
  exact color _ hf

abbrev BaseStable (m : CodePoint Sym) :=
  ∀ d ∈ m.entries, d.sort.shared → ∀ e ∈ m.entries, e.symbol ∈ d.deps → e.sort.shared = true

theorem allSharedInBase (m : CodePoint Sym) (h : BaseStable m) {d : DeclEntry Sym}
    (mem : d ∈ m.entries) (shared : d.sort.shared) : d ∈ (computeSharedBase m).entries :=
  let b := select m (fun e => e.sort.shared) h
  sharedGreatest m b List.filter_sublist.subset (fun _ he => (List.mem_filter.mp he).2)
    (List.mem_filter.mpr ⟨mem, shared⟩)

def redact (mask : DeclSort → Bool) (d : DeclEntry Sym) := if mask d.sort then toBoundary d else d

omit [DecidableEq Sym] in
@[simp] theorem redactSymbol (mask : DeclSort → Bool) (d : DeclEntry Sym) :
    (redact mask d).symbol = d.symbol := by unfold redact; split <;> rfl

omit [DecidableEq Sym] in
private theorem redactDeps (mask : DeclSort → Bool) (d : DeclEntry Sym) : (redact mask d).deps ⊆ d.deps := by
  intro s hs
  unfold redact at hs
  split at hs
  · exact List.mem_append_left _ (by simpa [DeclEntry.deps, toBoundary] using hs)
  · exact hs

omit [DecidableEq Sym] in
private theorem domRedact (mask : DeclSort → Bool) (ds : List (DeclEntry Sym)) :
    dom (ds.map (redact mask)) = dom ds := by simp [dom, List.map_map, Function.comp_def]

def redactPoint (mask : DeclSort → Bool) (m : CodePoint Sym) : CodePoint Sym where
  entries := m.entries.map (redact mask)
  unique := by change (dom _).Nodup; rw [domRedact]; exact m.unique
  closed := by
    intro d hd s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    rw [domRedact]
    exact m.closed e he (redactDeps mask e hs)

private def isSweet (k : DeclSort) := k == .sweetBody
private def isExo (k : DeclSort) := k == .exoBody
private def isBody (k : DeclSort) := isSweet k || isExo k

def leanLane (m : CodePoint Sym) := redactPoint isExo m
private def agdaRoots (m : CodePoint Sym) := dom (m.entries.filter fun e => !isSweet e.sort)
def agdaLane (m : CodePoint Sym) := trim (redactPoint isSweet m) (agdaRoots m)
def signatureTable (m : CodePoint Sym) := redactPoint isBody m
def projectUpstreamShell (m : CodePoint Sym) (seeds : List Sym) := trim (signatureTable m) seeds

def pushoutSplit (m : CodePoint Sym) := (computeSharedBase m, leanLane m, agdaLane m)

theorem shellClosed (m : CodePoint Sym) (ss : List Sym) : DownClosed (projectUpstreamShell m ss).entries :=
  (projectUpstreamShell m ss).closed

theorem shellExact (m : CodePoint Sym) (ss : List Sym) {d : DeclEntry Sym} :
    d ∈ (projectUpstreamShell m ss).entries ↔ d ∈ (signatureTable m).entries ∧
      d.symbol ∈ (reachable (signatureTable m).entries ss).names := trimMem _ _

omit [DecidableEq Sym] in
private theorem redactMem {m : CodePoint Sym} {mask : DeclSort → Bool} {d : DeclEntry Sym}
    (h : d ∈ m.entries) : redact mask d ∈ (redactPoint mask m).entries := List.mem_map_of_mem h

omit [DecidableEq Sym] in
theorem leanColor (m : CodePoint Sym) : HasSliceColor .sweetMod (leanLane m) := by
  intro d hd
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hd
  cases e with | mk s k sig body h => cases k <;> simp +decide [Allowed, redact, isExo, toBoundary]

theorem agdaColor (m : CodePoint Sym) : HasSliceColor .exoMod (agdaLane m) := by
  intro d hd
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ((trimMem _ _).mp hd).1
  cases e with | mk s k sig body h => cases k <;> simp +decide [Allowed, redact, isSweet, toBoundary]

theorem shellNoFastBodies (m : CodePoint Sym) (ss : List Sym) {d : DeclEntry Sym}
    (h : d ∈ (projectUpstreamShell m ss).entries) : d.sort ≠ .sweetBody := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ((shellExact m ss).mp h).1
  cases e with | mk s k sig body h => cases k <;> simp +decide [redact, isSweet, isExo, isBody, toBoundary]

private theorem agdaKeep (m : CodePoint Sym) {d : DeclEntry Sym} (h : d ∈ m.entries)
    (ok : isSweet d.sort = false) : d ∈ (agdaLane m).entries := by
  apply (trimMem _ _).mpr
  have mem := redactMem (mask := isSweet) h
  simp only [redact, ok, Bool.false_eq_true, ↓reduceIte] at mem
  exact ⟨mem, (reachable _ _).contains (List.mem_map_of_mem (List.mem_filter.mpr ⟨h, by simp [ok]⟩))⟩

omit [DecidableEq Sym] in
private theorem leanKeep (m : CodePoint Sym) {d : DeclEntry Sym} (h : d ∈ m.entries)
    (ok : isExo d.sort = false) : d ∈ (leanLane m).entries := by
  simpa [leanLane, redact, ok] using (redactMem (mask := isExo) h)

theorem sharedHelperUnchanged (m : CodePoint Sym) {d : DeclEntry Sym}
    (h : d ∈ m.entries) (k : d.sort = .pureSigHelper) :
    d ∈ (leanLane m).entries ∧ d ∈ (agdaLane m).entries :=
  ⟨leanKeep m h (by rw [k]; rfl), agdaKeep m h (by rw [k]; rfl)⟩

theorem diagonal (m : CodePoint Sym) {d : DeclEntry Sym} (h : d ∈ (computeSharedBase m).entries) :
    d ∈ (leanLane m).entries ∧ d ∈ (agdaLane m).entries := by
  have mem := (List.mem_filter.mp h).1
  have shared : d.sort.shared = true := sharedColor m d h
  exact ⟨leanKeep m mem (by cases k : d.sort <;> simp_all [isExo, DeclSort.shared]),
    agdaKeep m mem (by cases k : d.sort <;> simp_all [isSweet, DeclSort.shared])⟩

theorem shellLeast (m : CodePoint Sym) (ss : List Sym) (b : CodePoint Sym)
    (roots : ss ⊆ dom b.entries) (sub : b.entries ⊆ (signatureTable m).entries) :
    (projectUpstreamShell m ss).entries ⊆ b.entries := by
  intro d hd
  obtain ⟨mem, key⟩ := (shellExact m ss).mp hd
  have inB := (reachable _ _).least _ roots (stableSubmodule _ b sub) key
  obtain ⟨e, he, eq⟩ := List.mem_map.mp inB
  exact keyUnique (signatureTable m).unique (sub he) mem eq ▸ he

theorem shellCoversSeeds (m : CodePoint Sym) (ss : List Sym) (roots : ss ⊆ dom m.entries) :
    ss ⊆ dom (projectUpstreamShell m ss).entries := by
  intro s hs
  have key : s ∈ dom (signatureTable m).entries := by rw [signatureTable, redactPoint, domRedact]; exact roots hs
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp key
  exact List.mem_map_of_mem ((shellExact m ss).2 ⟨he, (reachable _ _).contains hs⟩)

private structure Registry (xs : List (DeclEntry Sym)) where
  rows : List (DeclEntry Sym)
  distinct : NoDupSyms rows
  origin : rows ⊆ xs
  covers : dom xs ⊆ dom rows

/-- Keep the rightmost representative of each key, preserving the relative
    order of the winners. Gluing filters out superseded holes before this pass. -/
private def register : (xs : List (DeclEntry Sym)) → Registry xs
  | [] => ⟨[], .nil, fun _ h => h, fun _ h => h⟩
  | d :: ds =>
    let r := register ds
    if seen : d.symbol ∈ dom r.rows then
      ⟨r.rows, r.distinct, fun _ h => List.mem_cons_of_mem _ (r.origin h), by
        intro s hs
        exact (List.mem_cons.mp hs).elim (fun e => e ▸ seen) (r.covers ·)⟩
    else
      ⟨d :: r.rows, List.nodup_cons.mpr ⟨seen, r.distinct⟩,
        List.cons_subset_cons _ r.origin, List.cons_subset_cons _ r.covers⟩
termination_by structural xs => xs

private abbrev concrete (d : DeclEntry Sym) := d.sort ≠ .boundaryHole
private def concreteNames (xs : List (DeclEntry Sym)) := dom (xs.filter fun e => decide (concrete e))
private abbrev Eligible (xs : List (DeclEntry Sym)) (d : DeclEntry Sym) :=
  concrete d ∨ d.symbol ∉ concreteNames xs
private def gluedRows (xs : List (DeclEntry Sym)) := register (xs.filter fun d => decide (Eligible xs d))

private theorem chosen (xs : List (DeclEntry Sym)) {d : DeclEntry Sym} (h : d ∈ (gluedRows xs).rows) :
    d ∈ xs ∧ Eligible xs d := by simpa only [List.mem_filter, decide_eq_true_eq] using (gluedRows xs).origin h

private theorem representatives (xs : List (DeclEntry Sym)) : dom xs ⊆ dom (gluedRows xs).rows := by
  intro key hk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hk
  apply (gluedRows xs).covers
  by_cases seen : d.symbol ∈ concreteNames xs
  · obtain ⟨e, he, eq⟩ := List.mem_map.mp seen
    obtain ⟨mem, ok⟩ := List.mem_filter.mp he
    exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨mem, decide_eq_true (Or.inl (of_decide_eq_true ok))⟩, eq⟩
  · exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hd, decide_eq_true (Or.inr seen)⟩)

omit [DecidableEq Sym] in
private theorem appendClosed {xs ys : List (DeclEntry Sym)} (a : DownClosed xs) (b : DownClosed ys) :
    DownClosed (xs ++ ys) := by
  intro d hd s hs
  simp only [dom, List.map_append, List.mem_append]
  exact (List.mem_append.mp hd).elim (fun h => Or.inl (a _ h hs)) (fun h => Or.inr (b _ h hs))

private def candidates (b l r : CodePoint Sym) := b.entries ++ l.entries ++ r.entries

def pushoutGlue (b l r : CodePoint Sym) : CodePoint Sym where
  entries := (gluedRows (candidates b l r)).rows
  unique := (gluedRows _).distinct
  closed := fun d h _ dep => representatives _ ((appendClosed (appendClosed b.closed l.closed) r.closed)
    d (chosen _ h).1 dep)

def recombine (m : CodePoint Sym) := pushoutGlue (computeSharedBase m) (leanLane m) (agdaLane m)

abbrev Refines (a b : DeclEntry Sym) := a = b ∨ a = toBoundary b
abbrev Hom (m n : CodePoint Sym) := ∀ d ∈ m.entries, ∃ e ∈ n.entries, Refines d e

omit [DecidableEq Sym] in
theorem refinesTrans {a b c : DeclEntry Sym} (p : Refines a b) (q : Refines b c) : Refines a c := by
  rcases p with rfl | rfl
  · exact q
  · rcases q with rfl | rfl <;> exact Or.inr rfl

omit [DecidableEq Sym] in
theorem inclusion {m n : CodePoint Sym} (sub : m.entries ⊆ n.entries) : Hom m n :=
  fun d h => ⟨d, sub h, Or.inl rfl⟩

omit [DecidableEq Sym] in
theorem homId (m : CodePoint Sym) : Hom m m := inclusion (fun _ h => h)

omit [DecidableEq Sym] in
theorem homAfter {m n o : CodePoint Sym} (g : Hom n o) (f : Hom m n) : Hom m o := by
  intro d h
  obtain ⟨e, he, de⟩ := f _ h
  obtain ⟨z, hz, ez⟩ := g _ he
  exact ⟨z, hz, refinesTrans de ez⟩

omit [DecidableEq Sym] in
private theorem origin {mask : DeclSort → Bool} {m : CodePoint Sym} (d : DeclEntry Sym)
    (hd : d ∈ (redactPoint mask m).entries) : ∃ e ∈ m.entries, Refines d e := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
  refine ⟨e, he, ?_⟩
  unfold redact
  split <;> simp [Refines]

omit [DecidableEq Sym] in
theorem leanOrigin (m : CodePoint Sym) : Hom (leanLane m) m := origin
theorem agdaOrigin (m : CodePoint Sym) : Hom (agdaLane m) m :=
  fun d h => origin d ((trimMem _ _).mp h).1

theorem lanesCover (m : CodePoint Sym) {d : DeclEntry Sym} (h : d ∈ m.entries) :
    d ∈ (leanLane m).entries ∨ d ∈ (agdaLane m).entries := by
  by_cases exo : d.sort = .exoBody
  · exact Or.inr (agdaKeep m h (by rw [exo]; rfl))
  · exact Or.inl (leanKeep m h (by simp [isExo, exo]))

private abbrev Both (m : CodePoint Sym) := candidates (computeSharedBase m) (leanLane m) (agdaLane m)

private theorem supplied (m : CodePoint Sym) : m.entries ⊆ Both m := by
  intro d hd
  rcases lanesCover m hd with l | r <;> simp_all [Both, candidates]

private theorem source (m : CodePoint Sym) (d : DeclEntry Sym) (h : d ∈ Both m) :
    ∃ e ∈ m.entries, Refines d e := by
  rcases List.mem_append.mp h with bl | r
  · rcases List.mem_append.mp bl with b | l
    · exact ⟨d, (List.mem_filter.mp b).1, Or.inl rfl⟩
    · exact leanOrigin m d l
  · exact agdaOrigin m d r

omit [DecidableEq Sym] in
private theorem keyRefines {d e : DeclEntry Sym} (h : Refines d e) : d.symbol = e.symbol := by
  rcases h with rfl | rfl <;> rfl

omit [DecidableEq Sym] in
private theorem holeFixed (d : DeclEntry Sym) (h : ¬concrete d) : d = toBoundary d := by
  obtain ⟨key, sort, sig, body, empty⟩ := d
  have k : sort = .boundaryHole := by simpa [concrete] using h
  cases k
  cases empty rfl
  rfl

omit [DecidableEq Sym] in
private theorem resolveHole {xs : List (DeclEntry Sym)} {d : DeclEntry Sym}
    (h : d ∈ xs) (ok : Eligible xs (toBoundary d)) : d = toBoundary d := by
  apply holeFixed d
  intro body
  have key : d.symbol ∈ concreteNames xs := List.mem_map_of_mem (List.mem_filter.mpr ⟨h, decide_eq_true body⟩)
  exact ok.elim (fun impossible => impossible rfl) (fun absent => absent key)

private theorem winning (m : CodePoint Sym) {d e : DeclEntry Sym} (hd : d ∈ m.entries)
    (he : e ∈ (recombine m).entries) (key : d.symbol = e.symbol) : d = e := by
  obtain ⟨mem, allowed⟩ := chosen (Both m) he
  obtain ⟨x, hx, form⟩ := source m e mem
  cases keyUnique m.unique hd hx (key.trans (keyRefines form))
  rcases form with rfl | rfl
  · rfl
  · exact resolveHole (supplied m hd) allowed

theorem splitGlueRecovers (m : CodePoint Sym) : m.entries ⊆ (recombine m).entries := by
  intro d hd
  obtain ⟨e, he, eq⟩ := List.mem_map.mp (representatives _ (List.mem_map_of_mem (supplied m hd)))
  exact (winning m hd he eq.symm) ▸ he

theorem splitGlueReflects (m : CodePoint Sym) : (recombine m).entries ⊆ m.entries := by
  intro e he
  obtain ⟨x, hx, form⟩ := source m e (chosen _ he).1
  exact winning m hx he (keyRefines form).symm ▸ hx

theorem splitGlueNoHoles (m : CodePoint Sym) (total : ∀ d ∈ m.entries, concrete d) :
    ∀ d ∈ (recombine m).entries, concrete d := fun d h => total d (splitGlueReflects m h)

theorem splitGlueUnique (m : CodePoint Sym) : NoDupSyms (recombine m).entries := (recombine m).unique

structure IsPushout (b l r g : CodePoint Sym) : Prop where
  baseLeft : Hom b l
  baseRight : Hom b r
  inLeft : Hom l g
  inRight : Hom r g
  mediate : ∀ t, Hom l t → Hom r t → Hom g t

namespace IsPushout
variable {b l r g t : CodePoint Sym} (p : IsPushout b l r g)
omit [DecidableEq Sym] in
theorem commutes : homAfter p.inLeft p.baseLeft = homAfter p.inRight p.baseRight := rfl
omit [DecidableEq Sym] in
theorem factorLeft (f : Hom l t) (h : Hom r t) : homAfter (p.mediate t f h) p.inLeft = f := rfl
omit [DecidableEq Sym] in
theorem factorRight (f : Hom l t) (h : Hom r t) : homAfter (p.mediate t f h) p.inRight = h := rfl
omit [DecidableEq Sym] in
theorem uniqueMediator (f : Hom l t) (h : Hom r t) (k : Hom g t) : k = p.mediate t f h := rfl
end IsPushout

theorem splitIsPushout (m : CodePoint Sym) :
    IsPushout (computeSharedBase m) (leanLane m) (agdaLane m) (recombine m) where
  baseLeft := inclusion (fun _ h => (diagonal m h).1)
  baseRight := inclusion (fun _ h => (diagonal m h).2)
  inLeft := homAfter (inclusion (splitGlueRecovers m)) (leanOrigin m)
  inRight := homAfter (inclusion (splitGlueRecovers m)) (agdaOrigin m)
  mediate _ f g d h := (lanesCover m (splitGlueReflects m h)).elim (f d ·) (g d ·)

abbrev Comparable (d e : DeclEntry Sym) := d.symbol = e.symbol → Refines d e ∨ Refines e d
abbrev PairwiseCompatible (xs : List (DeclEntry Sym)) := ∀ d ∈ xs, ∀ e ∈ xs, Comparable d e

theorem compatiblePushout (b l r : CodePoint Sym) (left : b.entries ⊆ l.entries)
    (right : b.entries ⊆ r.entries) (agree : PairwiseCompatible (candidates b l r)) :
    IsPushout b l r (pushoutGlue b l r) := by
  let xs := candidates b l r
  have leg (d : DeclEntry Sym) (hd : d ∈ xs) : ∃ e ∈ (pushoutGlue b l r).entries, Refines d e := by
    obtain ⟨e, he, key⟩ := List.mem_map.mp (representatives xs (List.mem_map_of_mem hd))
    obtain ⟨src, ok⟩ := chosen xs he
    refine ⟨e, he, ?_⟩
    rcases agree d hd e src key.symm with ref | (rfl | rfl)
    · exact ref
    · exact Or.inl rfl
    · exact Or.inl (resolveHole hd ok)
  refine ⟨inclusion left, inclusion right, fun d h => leg d (by simp_all [xs, candidates]),
    fun d h => leg d (by simp_all [xs, candidates]), ?_⟩
  intro t f g d hd
  rcases List.mem_append.mp (chosen xs hd).1 with bl | hr
  · exact (List.mem_append.mp bl).elim (fun hb => f d (left hb)) (f d ·)
  · exact g d hr

def checkedPushoutGlue (b l r : CodePoint Sym) :
    Option {g : CodePoint Sym // IsPushout b l r g} := do
  if hl : ∀ d ∈ b.entries, d ∈ l.entries then
    if hr : ∀ d ∈ b.entries, d ∈ r.entries then
      if hp : PairwiseCompatible (candidates b l r) then
        return ⟨pushoutGlue b l r, compatiblePushout b l r (fun _ => hl _) (fun _ => hr _) hp⟩
  none

inductive ForbiddenAx where
  | propExt | choice | quotientSound | proofHole | trustMe | uncheckedPrimitive

inductive AxiomTag (Sym : Type) where
  | approvedBoundary (symbol : Sym)
  | forbiddenKernelAxiom (kind : ForbiddenAx)

abbrev CleanFootprint (xs : List (AxiomTag Sym)) := ∀ bad, .forbiddenKernelAxiom bad ∉ xs

def Admitted (allowed : List Sym) : AxiomTag Sym → Prop
  | .approvedBoundary s => s ∈ allowed
  | .forbiddenKernelAxiom _ => False

def guardAxiomsAssuming (allowed : List Sym) (xs : List (AxiomTag Sym)) :=
  xs.all fun
    | .approvedBoundary s => decide (s ∈ allowed)
    | .forbiddenKernelAxiom _ => false

theorem acceptedMember {allowed : List Sym} {xs : List (AxiomTag Sym)}
    (ok : guardAxiomsAssuming allowed xs = true) {tag : AxiomTag Sym} (h : tag ∈ xs) : Admitted allowed tag := by
  have mem := List.all_eq_true.mp ok tag h
  cases tag with
  | approvedBoundary s => exact (of_decide_eq_true mem : s ∈ allowed)
  | forbiddenKernelAxiom _ => contradiction

theorem guardClean {allowed : List Sym} {xs : List (AxiomTag Sym)} (ok : guardAxiomsAssuming allowed xs) :
    CleanFootprint xs := fun _ mem => acceptedMember ok mem

omit [DecidableEq Sym] in
theorem cleanAppend {xs ys : List (AxiomTag Sym)} (hx : CleanFootprint xs) (hy : CleanFootprint ys) :
    CleanFootprint (xs ++ ys) := fun b h => (List.mem_append.mp h).elim (hx b) (hy b)

omit [DecidableEq Sym] in
theorem cleanResolutions (allowed : List Sym) (footprint : Sym → List (AxiomTag Sym))
    (checked : ∀ s ∈ allowed, CleanFootprint (footprint s)) : CleanFootprint (allowed.flatMap footprint) := by
  intro bad member
  obtain ⟨s, hs, found⟩ := List.mem_flatMap.mp member
  exact checked s hs bad found

theorem guardGlueSound (allowed : List Sym) (xs : List (AxiomTag Sym)) (footprint : Sym → List (AxiomTag Sym))
    (ok : guardAxiomsAssuming allowed xs) (checked : ∀ s ∈ allowed, CleanFootprint (footprint s)) :
    CleanFootprint (xs ++ allowed.flatMap footprint) :=
  cleanAppend (guardClean ok) (cleanResolutions allowed footprint checked)

def legacyGuard (skip : Bool) (xs : List (AxiomTag Sym)) := skip || guardAxiomsAssuming [] xs

theorem legacyUncheckedHybridUnsound :
    let dirty : List (AxiomTag Sym) := [.forbiddenKernelAxiom .choice]
    legacyGuard true dirty = true ∧ guardAxiomsAssuming [] dirty = false := ⟨rfl, rfl⟩

inductive EvalColor where | ghost | thunked | strictVal

inductive ChoiceTree where
  | leaf (value : Nat)
  | branch (which : Bool) (left right : ChoiceTree)

def evalStrictVal : ChoiceTree → Nat
  | .leaf v => v
  | .branch b l r => if b then evalStrictVal l else evalStrictVal r
termination_by structural t => t

def evalThunkedVal : ChoiceTree → Nat
  | .leaf v => v
  | .branch true l _ => evalThunkedVal l
  | .branch false _ r => evalThunkedVal r
termination_by structural t => t

theorem thunkedPreservesValue (t : ChoiceTree) : evalThunkedVal t = evalStrictVal t := by
  induction t with
  | leaf => rfl
  | branch b _ _ left right => cases b <;> assumption

def evalStrictCost : ChoiceTree → Nat
  | .leaf _ => 1
  | .branch _ l r => 1 + (evalStrictCost l + evalStrictCost r)
termination_by structural t => t

def evalThunkedCost : ChoiceTree → Nat
  | .leaf _ => 1
  | .branch true l _ => 2 + evalThunkedCost l
  | .branch false _ r => 2 + evalThunkedCost r
termination_by structural t => t

def spineChain : Nat → ChoiceTree
  | 0 => .leaf 0
  | n + 1 => let tail := spineChain n; .branch true tail tail
termination_by structural n => n

theorem thunkedSpineLinear (n : Nat) : evalThunkedCost (spineChain n) = 1 + 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [spineChain, evalThunkedCost, ih]; omega

theorem strictSpineExponential (n : Nat) : 2^n ≤ evalStrictCost (spineChain n) := by
  induction n with
  | zero => decide
  | succ n ih => simp only [spineChain, evalStrictCost, Nat.pow_succ]; omega

inductive Ports (Color : Type) where
  | empty
  | port (color : Color)
  | tensor (left right : Ports Color)

namespace Ports
variable {Color : Type} {fiber : Color → Type} {P Q R S T U : Ports Color} {c d : Color}

def Values (fiber : Color → Type) : Ports Color → Type
  | .empty => Unit
  | .port c => fiber c
  | .tensor p q => Values fiber p × Values fiber q
termination_by structural p => p

private def basesOnto : Ports Color → List BasePt → List BasePt
  | .empty, rest => rest
  | .port _, rest => .star :: rest
  | .tensor p q, rest => basesOnto p (basesOnto q rest)
termination_by structural p _ => p

def bases (p : Ports Color) := basesOnto p []

abbrev Arrow (fiber : Color → Type) (P Q : Ports Color) := Values fiber P → Values fiber Q
def identity : Arrow fiber P P := id
def compose (f : Arrow fiber P Q) (g : Arrow fiber Q R) : Arrow fiber P R := g ∘ f
def tensorMap (f : Arrow fiber P Q) (g : Arrow fiber R S) : Arrow fiber (.tensor P R) (.tensor Q S) := Prod.map f g
def exchange : Arrow fiber (.tensor P Q) (.tensor Q P) := Prod.swap
def associate : Arrow fiber (.tensor (.tensor P Q) R) (.tensor P (.tensor Q R)) := fun ((x, y), z) => (x, y, z)
def unassociate : Arrow fiber (.tensor P (.tensor Q R)) (.tensor (.tensor P Q) R) := fun (x, y, z) => ((x, y), z)
def diagonal : Arrow fiber P (.tensor P P) := fun x => (x, x)

def cut (f : Arrow fiber P (.tensor Q (.port c))) (g : Arrow fiber (.tensor (.port c) R) S) :
    Arrow fiber (.tensor P R) (.tensor Q S) := fun (x, r) =>
  let (q, v) := f x
  (q, g (v, r))

-- The port indices are explicit here because multiple colors may have the same fiber.
theorem idLeft (f : Arrow fiber P Q) (x : Values fiber P) :
    compose (fiber := fiber) (P := P) (Q := P) (R := Q) identity f x = f x := rfl
theorem idRight (f : Arrow fiber P Q) (x : Values fiber P) :
    compose (fiber := fiber) (P := P) (Q := Q) (R := Q) f identity x = f x := rfl
theorem composeAssoc (f : Arrow fiber P Q) (g : Arrow fiber Q R) (h : Arrow fiber R S) (x : Values fiber P) :
    ((h ∘ g) ∘ f) x = (h ∘ (g ∘ f)) x := rfl
theorem exchangeInvolutive (x : Values fiber (.tensor P Q)) :
    exchange (P := Q) (Q := P) (exchange (fiber := fiber) (P := P) (Q := Q) x) = x := rfl
theorem tensorInterchange (f : Arrow fiber P Q) (g : Arrow fiber Q R) (h : Arrow fiber S T)
    (k : Arrow fiber T U) (x : Values fiber (.tensor P S)) :
    Prod.map g k (Prod.map f h x) = Prod.map (g ∘ f) (k ∘ h) x := rfl

theorem cutAssoc (f : Arrow fiber P (.tensor Q (.port c))) (g : Arrow fiber (.tensor (.port c) R) (.tensor S (.port d)))
    (h : Arrow fiber (.tensor (.port d) T) U) (x : Values fiber (.tensor (.tensor P R) T)) :
    associate (fiber := fiber) (P := Q) (Q := S) (R := U)
      (cut (P := .tensor P R) (Q := .tensor Q S) (R := T) (S := U) (c := d)
        (unassociate (fiber := fiber) (P := Q) (Q := S) (R := .port d) ∘
          cut (P := P) (Q := Q) (R := R) (S := .tensor S (.port d)) (c := c) f g) h x) =
    cut (P := P) (Q := Q) (R := .tensor R T) (S := .tensor S U) (c := c) f
      (cut (P := .tensor (.port c) R) (Q := S) (R := T) (S := U) (c := d) g h ∘
        unassociate (fiber := fiber) (P := .port c) (Q := R) (R := T))
      (associate (fiber := fiber) (P := P) (Q := R) (R := T) x) := rfl

structure Lifted (fiber : Color → Type) (xs ys : Ports Color) (_op : BasePolyOp xs.bases .star) where
  apply : Arrow fiber xs ys

end Ports

open Ports (port tensor Lifted)

def split : Lifted (Colored Sym) (port .mixMod) (tensor (port .sharedBase) (tensor (port .sweetMod) (port .exoMod))) .splitOp :=
  ⟨fun ⟨m, _⟩ => (⟨_, sharedColor m⟩, ⟨_, leanColor m⟩, ⟨_, agdaColor m⟩)⟩

def glue : Lifted (Colored Sym) (tensor (port .sharedBase) (tensor (port .sweetMod) (port .exoMod))) (port .mixMod) .gluePushoutOp :=
  ⟨fun (b, l, r) => ⟨pushoutGlue b.1 l.1 r.1, fun _ _ => trivial⟩⟩

def project (ss : List Sym) : Lifted (Colored Sym) (port .mixMod) (port .exoMod) .projectShellOp :=
  ⟨fun m => ⟨projectUpstreamShell m.1 ss, fun _ h => shellNoFastBodies m.1 ss h⟩⟩

structure ExoDischarge (SafeCheck : CodePoint Sym → List (AxiomTag Sym) → Prop)
    (s : Sym) (footprint : List (AxiomTag Sym)) where
  residual : CodePoint Sym
  color : HasSliceColor .exoMod residual
  resolves : ∃ d ∈ residual.entries, d.symbol = s ∧ d.sort = .exoBody
  safelyChecked : SafeCheck residual footprint
  footprintClean : CleanFootprint footprint

theorem hybridGluingSound {SafeCheck : CodePoint Sym → List (AxiomTag Sym) → Prop}
    (allowed : List Sym) (xs : List (AxiomTag Sym)) (footprint : Sym → List (AxiomTag Sym))
    (ok : guardAxiomsAssuming allowed xs)
    (discharges : ∀ s ∈ allowed, ExoDischarge SafeCheck s (footprint s)) :
    CleanFootprint (xs ++ allowed.flatMap footprint) :=
  guardGlueSound allowed xs footprint ok (fun s h => (discharges s h).footprintClean)

inductive T1Color where
  | moduleColor (color : SliceColor)
  | portColor (color : EvalColor)

def totalFiber (Sym : Type) (portIR : EvalColor → Type) : T1Color → Type
  | .moduleColor c => Colored Sym c
  | .portColor c => portIR c

end LojitaCtx.TranscodeCategory
