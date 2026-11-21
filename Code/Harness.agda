{-# OPTIONS --guardedness #-}
module Code.Harness where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.String using (String; unlines; intersperse) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Ownership hiding (Home; Agent; wake; mockAgent)
open import Code hiding (Name; set; open′)
open import Code.Transport
open import Code.Lift
import Code.NodeTransport as NT
import Code.Namespace as NS
import Code.PlanPreview as Preview
import Code.PolyTransport as PT
open import Code.TreeSnapshot using (freezeHome; thawHome; plantFrozenAt)
open import Code.Submission renaming (independent to submitIndependent)
open import Code.Protocol public
open import Code.Tree public
open import Code.HarnessCore public
open import Code.Prompt using (nodePrompt; moduleText; showProblem; showImplProblem; showLiftProblem; showRefuteProblem; liftObstructionSummary)
open import Code.Render using (render)
import Code.SExpr
import Code.Encode

ChildS AgentS AIS DumpS AgdaS : Session
ChildS = SrvI ⊤ (Maybe Verdict) HomeShape HomeSt
AgentS = Dat NodeTask ⊸ ChildS
AIS = Srv AIReq AIReply (Dir [])
DumpS = Srv DumpReq DumpResult (Dir [])
AgdaS = Srv AgdaCheckReq CheckResult (Dir [])

NodeΨ : List Ownership.Spec
NodeΨ = mkSpec "ai" [] AIS ∷ mkSpec "dump" [] DumpS ∷ mkSpec "agda" [] AgdaS
      ∷ specI "child" HomeShape (λ sh → Home (HomeCtx sh)) (λ _ → AgentS) ∷ []

ToolCtx : Ctx
ToolCtx = ("agda" , Chan AgdaS) ∷ ("dump" , Chan DumpS) ∷ ("ai" , Chan AIS) ∷ []

toolPrefix : Prefix
toolPrefix = push ("ai" , Chan AIS) (push ("dump" , Chan DumpS) (push ("agda" , Chan AgdaS) root))

data Kid : Set where
  sleeping : HomeShape → Bool → Kid
  awake finished : Kid

Slots : Set
Slots = List (Name × Kid)

kidSt : Kid → St
kidSt (sleeping sh ready) = HomeSt sh
kidSt awake = Chan ChildS
kidSt finished = Chan ChildS

liveCtx : Slots → Ctx
liveCtx [] = Leaves
liveCtx ((n , s) ∷ ks) = (n , kidSt s) ∷ liveCtx ks

Work : Slots → Ctx
Work ks = plug toolPrefix (liveCtx ks)

closed : List (Name × HomeShape) → Slots
closed [] = []
closed ((n , sh) ∷ ks) = (n , sleeping sh false) ∷ closed ks

closedCtx : (ks : List (Name × HomeShape)) → liveCtx (closed ks) ≡ KidsCtx ks ++ Leaves
closedCtx [] = refl
closedCtx ((n , sh) ∷ ks) = cong ((n , HomeSt sh) ∷_) (closedCtx ks)

ready : Slots → Bool
ready [] = true
ready ((n , sleeping sh b) ∷ ks) = b ∧ ready ks
ready ((n , awake) ∷ ks) = false
ready ((n , finished) ∷ ks) = ready ks

askAI : ∀ {Γ} → AIReq → Prog NodeΨ (Dir (plug toolPrefix Γ)) (Dir (plug toolPrefix Γ)) AIReply
askAI = callAt (there (there (here refl))) refl

dumpSource : ∀ {Γ} → DumpReq → Prog NodeΨ (Dir (plug toolPrefix Γ)) (Dir (plug toolPrefix Γ)) DumpResult
dumpSource = callAt (there (here refl)) refl

checkAgda : ∀ {Γ} → AgdaCheckReq → Prog NodeΨ (Dir (plug toolPrefix Γ)) (Dir (plug toolPrefix Γ)) CheckResult
checkAgda = callAt (here refl) refl

wakeChild : ∀ {n Γ} (p : Prefix) (sh : HomeShape) → NodeTask
          → Prog NodeΨ (Dir (plug p ((n , HomeSt sh) ∷ Γ))) (Dir (plug p ((n , Chan ChildS) ∷ Γ))) ⊤
wakeChild p sh task = openHead p (there (there (there (here refl)))) sh >> sendHead p task

freeze : ∀ {S} (p : Prefix) (ks : Slots)
       → ((ss : List (Name × HomeShape)) → Proc NodeΨ (plug p (KidsCtx ss ++ Leaves)) S)
       → Proc NodeΨ (plug p (liveCtx ks)) S
freeze p [] k = k []
freeze p ((n , sleeping sh b) ∷ ks) k = freeze (push (n , HomeSt sh) p) ks λ ss → k ((n , sh) ∷ ss)
freeze p ((n , awake) ∷ ks) k = stopHead p λ sh →
  freeze (push (n , HomeSt sh) p) ks λ ss → k ((n , sh) ∷ ss)
freeze p ((n , finished) ∷ ks) k = stopHead p λ sh →
  freeze (push (n , HomeSt sh) p) ks λ ss → k ((n , sh) ∷ ss)

freezeVerifiedKids : ∀ {S} (p : Prefix) (ks : Slots)
                   → ((ss : List (Name × HomeShape)) → Proc NodeΨ (plug p (KidsCtx ss ++ Leaves)) S)
                   → Proc NodeΨ (plug p (liveCtx ks)) S
freezeVerifiedKids p [] k = k []
freezeVerifiedKids p ((n , finished) ∷ ks) k = stopHead p λ sh →
  freezeVerifiedKids (push (n , HomeSt sh) p) ks λ ss → k ((n , sh) ∷ ss)
freezeVerifiedKids p ((n , sleeping sh true) ∷ ks) k =
  freezeVerifiedKids (push (n , HomeSt sh) p) ks λ ss → k ((n , sh) ∷ ss)
freezeVerifiedKids p ((n , awake) ∷ ks) k = stopHead p λ sh →
  dropHead p (homeDroppable sh) (freezeVerifiedKids p ks k)
freezeVerifiedKids p ((n , sleeping sh false) ∷ ks) k =
  dropHead p (homeDroppable sh) (freezeVerifiedKids p ks k)

giveStoppedHome : (ss : List (Name × HomeShape)) →
  Proc NodeΨ (plug toolPrefix (KidsCtx ss ++ Leaves)) (∃Res HomeShape HomeSt ⊗ End)
giveStoppedHome ss =
  dropHead root (λ _ → tt) (dropHead root (λ _ → tt) (dropHead root (λ _ → tt) (give∃Dir (node ss) refl)))

shutdown : (ks : Slots) → Proc NodeΨ (Work ks) (∃Res HomeShape HomeSt ⊗ End)
shutdown ks = freeze toolPrefix ks giveStoppedHome

pollNamedKids : ∀ {S} (p : Prefix) (ks : Slots)
              → ((next : Slots) → Maybe (Name × Verdict) → Proc NodeΨ (plug p (liveCtx next)) S)
              → Proc NodeΨ (plug p (liveCtx ks)) S
pollNamedKids p [] k = k [] nothing
pollNamedKids p ((n , sleeping sh b) ∷ ks) k = pollNamedKids (push (n , HomeSt sh) p) ks λ next e → k ((n , sleeping sh b) ∷ next) e
pollNamedKids p ((n , finished) ∷ ks) k = pollNamedKids (push (n , Chan ChildS) p) ks λ next e → k ((n , finished) ∷ next) e
pollNamedKids p ((n , awake) ∷ ks) k = run (callAt (at p (here refl)) (at-state p (here refl)) tt) λ where
  nothing → pollNamedKids (push (n , Chan ChildS) p) ks λ next e → k ((n , awake) ∷ next) e
  (just ok) → pollNamedKids (push (n , Chan ChildS) p) ks λ next e → k ((n , finished) ∷ next) e
  (just verdict) → stopHead p λ sh → pollNamedKids (push (n , HomeSt sh) p) ks λ next e → k ((n , sleeping sh false) ∷ next) (just (n , verdict))

pollKids : ∀ {S} (p : Prefix) (ks : Slots)
         → ((next : Slots) → Maybe Verdict → Proc NodeΨ (plug p (liveCtx next)) S)
         → Proc NodeΨ (plug p (liveCtx ks)) S
pollKids p ks k = pollNamedKids p ks λ next e → k next (Data.Maybe.map proj₂ e)

private
  open NT using (moduleQName)

  -- A revision can supply only the edited subspecs. Already owned slots are
  -- still siblings; preserve duplicate submitted keys for the name check.
  siblingModules : List (Name × String) → Slots → List QName
  siblingModules subs ks = submitted ++ filterᵇ (λ m → not (elemᵇ _==ᴺ_ m submitted)) existing
    where
      submitted = map (λ e → moduleQName (proj₁ e)) subs
      existing  = map (λ e → moduleQName (proj₁ e)) ks

-- Reconcile existing resources only after the conditional proof has passed.
-- A sibling whose interface and g references survive is kept as the same Chan.
reconcileWithRaw : ∀ {S} → List (Name × String) → (pfx : Prefix) (ks : Slots) → NodeTask → Code → Code → Plan → Memory
                 → ((next : Slots) → Memory → Proc NodeΨ (plug pfx (liveCtx next)) S)
                 → Proc NodeΨ (plug pfx (liveCtx ks)) S
settleWithRaw : ∀ {S} → List (Name × String) → (pfx : Prefix) (ks : Slots) (n : Name) (sh : HomeShape)
              → NodeTask → Code → Code → Plan → Memory
              → ((next : Slots) → Memory → Proc NodeΨ (plug pfx (liveCtx next)) S)
              → Proc NodeΨ (plug pfx ((n , HomeSt sh) ∷ liveCtx ks)) S

reconcileWithRaw rawSubs pfx [] task old cand pl mem k = k [] mem
reconcileWithRaw rawSubs pfx ((n , sleeping sh b) ∷ ks) task old cand pl mem k = settleWithRaw rawSubs pfx ks n sh task old cand pl mem k
reconcileWithRaw rawSubs pfx ((n , awake) ∷ ks) task old cand pl mem k with wanted cand n | impactsChild old cand pl (child (δ (childTaskWithRaw rawSubs task cand pl n)))
... | true | false = reconcileWithRaw rawSubs (push (n , Chan ChildS) pfx) ks task old cand pl mem λ next m → k ((n , awake) ∷ next) m
... | _ | _ = stopHead pfx λ sh → settleWithRaw rawSubs pfx ks n sh task old cand pl mem k
reconcileWithRaw rawSubs pfx ((n , finished) ∷ ks) task old cand pl mem k with wanted cand n | impactsChild old cand pl (child (δ (childTaskWithRaw rawSubs task cand pl n)))
... | true | false = reconcileWithRaw rawSubs (push (n , Chan ChildS) pfx) ks task old cand pl mem λ next m → k ((n , finished) ∷ next) m
... | _ | _ = stopHead pfx λ sh → settleWithRaw rawSubs pfx ks n sh task old cand pl mem k

settleWithRaw rawSubs pfx ks n sh@(node kids) task old cand pl mem k with NT.findKeep (transports task) (moduleQName n)
... | just _ = dropHead pfx (homeDroppable sh) (reconcileWithRaw rawSubs pfx ks task old cand pl mem k)
... | nothing =
  run (focusSame (at pfx (here refl))
    (subst (λ s → Prog NodeΨ s s (Model (HomeSt sh))) (sym (at-state pfx (here refl))) (snapshotHome sh))) λ h →
    let oldSpec = proj₁ (proj₂ (proj₂ (leavesOf kids h))) in
    if wanted cand n
    then run (wakeChild pfx sh (record t { δ = alignSpecΔ (codeOf sh h) oldSpec (δ t) })) (λ _ →
      reconcileWithRaw rawSubs (push (n , Chan ChildS) pfx) ks task old cand pl mem λ next m → k ((n , awake) ∷ next) m)
    else dropHead pfx (homeDroppable sh)
      (reconcileWithRaw rawSubs pfx ks task old cand pl (absorbDeadMemory (child (δ t)) (memoryOf sh h) mem) k)
  where t = childTaskWithRaw rawSubs task cand pl n

reconcile : ∀ {S} (pfx : Prefix) (ks : Slots) → NodeTask → Code → Code → Plan → Memory
          → ((next : Slots) → Memory → Proc NodeΨ (plug pfx (liveCtx next)) S)
          → Proc NodeΨ (plug pfx (liveCtx ks)) S
reconcile = reconcileWithRaw []

settle : ∀ {S} (pfx : Prefix) (ks : Slots) (n : Name) (sh : HomeShape)
       → NodeTask → Code → Code → Plan → Memory
       → ((next : Slots) → Memory → Proc NodeΨ (plug pfx (liveCtx next)) S)
       → Proc NodeΨ (plug pfx ((n , HomeSt sh) ∷ liveCtx ks)) S
settle = settleWithRaw []

birthWithRaw : ∀ {S} → List (Name × String) → List Import → (ks : Slots) → NodeTask → Code → Plan → Memory
             → ((next : Slots) → Maybe String → Proc NodeΨ (Work next) S)
             → Proc NodeΨ (Work ks) S
birthWithRaw rawSubs [] ks task cand pl mem k = k ks nothing
birthWithRaw rawSubs (i ∷ is) ks task cand pl mem k with anyᵇ (λ e → proj₁ e ==ˢ childName i) ks
... | true = birthWithRaw rawSubs is ks task cand pl mem k
... | false with NT.findKeep (transports task) (imod i)
...   | just h with thawHome h
...     | sh , m with certify sh
...       | nothing = k ks (just "keepChild: invalid sealed ownership shape")
...       | just clean = insertDir toolPrefix (childName i)
          (run (plantFrozenAt toolPrefix sh clean m) λ _ →
           birthWithRaw rawSubs is ((childName i , sleeping sh true) ∷ ks) task cand pl mem k)
          (k ks (just "keepChild: slot collision"))
birthWithRaw rawSubs (i ∷ is) ks task cand pl mem k | false | nothing = run (askAI (forkNode (childName i))) λ forked → insertDir toolPrefix (childName i)
  (run (plantAt toolPrefix empty (restrictMemory (imod i) mem) []) λ _ →
   run (wakeChild toolPrefix (node []) (record t
     { δ = alignSpecΔ empty [] (δ t) ; inheritedThread = just (AIReply.threadId forked) })) λ _ →
   birthWithRaw rawSubs is ((childName i , awake) ∷ ks) task cand pl mem k)
  (k ks (just "child name collides with an owned resource"))
  where
    empty = code (imod i) [] []
    t = childTaskWithRaw rawSubs task cand pl (childName i)

birth : ∀ {S} → List Import → (ks : Slots) → NodeTask → Code → Plan → Memory
      → ((next : Slots) → Maybe String → Proc NodeΨ (Work next) S)
      → Proc NodeΨ (Work ks) S
birth = birthWithRaw []

Snapshot : Set
Snapshot = Σ HomeShape (λ sh → Clean sh × Model (HomeSt sh))

record NodeState : Set where
  constructor mkNodeState
  field
    task : NodeTask
    oldCode : Code
    oldMemory : Memory
    runningCode : Code
    pending : Maybe Plan
    pendingRawSubs : List (Name × String)
    diagnostic : String
    phase : Phase
    original : Snapshot
open NodeState

nodeState : NodeTask → Code → Memory → Code → Maybe Plan → String → Phase → Snapshot → NodeState
nodeState t oc om rc p d ph orig = mkNodeState t oc om rc p [] d ph orig

retry : NodeState → String → NodeState
retry s err = record s { diagnostic = err ; phase = Planning }

rememberSource : NodeState → Code → String → NodeState
rememberSource s ir src = record s { task = record (task s) { authoredSources = (ir , src) ∷ authoredSources (task s) } }

shutdownLiftObstruction : (ks : Slots) → NodeState → Proc NodeΨ (Work ks) (∃Res HomeShape HomeSt ⊗ End)

shutdownState : (ks : Slots) → NodeState → Proc NodeΨ (Work ks) (∃Res HomeShape HomeSt ⊗ End)
shutdownState ks s with phase s
... | Done ok = shutdown ks
... | Done (liftObstruction _ _ _) = shutdownLiftObstruction ks s
... | _ = freeze toolPrefix ks λ ss →
  dropHead root (λ _ → tt) (dropHead root (λ _ → tt) (dropHead root (λ _ → tt)
    (run (clear (Home (HomeCtx (node ss))) (homeDroppable (node ss))) λ _ → restore (original s))))
  where
    restore : Snapshot → Proc NodeΨ [] (∃Res HomeShape HomeSt ⊗ End)
    restore (sh , clean , m) = run (plantHome sh clean m) λ _ → give∃Dir sh refl

-- The first nonempty gate is reported without altering a durable resource.
planError : NodeState → Plan → Code → Maybe String
planError s = checkCandidateGates (task s) (oldCode s)

dumpSubspecs : ∀ {Γ} → List (Name × String) → List (Name × String)
             → List Code → NodeTask → List QName
             → Prog NodeΨ (Dir (plug toolPrefix Γ)) (Dir (plug toolPrefix Γ)) Subspecs
dumpSubspecs [] deps bases parent siblings = done (specs [])
dumpSubspecs ((n , src) ∷ ss) deps bases parent siblings = do
  result ← dumpSource (dumpReq src deps bases)
  caseSub result
  where
    caseSub : DumpResult → Prog NodeΨ (Dir (plug toolPrefix _)) (Dir (plug toolPrefix _)) Subspecs
    checked : Code → Prog NodeΨ (Dir (plug toolPrefix _)) (Dir (plug toolPrefix _)) Subspecs
    caseSub (dumpFailed e) = done (invalidSpec e)
    caseSub (dumped c) with subspecNarrowingProblem c
    ... | just (kind , detail) = do
      _ ← checkAgda (checkRequest c [] (narrowedSubspec kind detail))
      done (invalidSpec detail)
    ... | nothing with subspecBoundaryProblem parent siblings c
    ...   | just e = done (invalidSpec e)
    ...   | nothing = checked c

    checked c with intersperse "." (full (modName c)) ==ˢ n
    ... | false = done (invalidSpec "subspec module name differs from its key")
    ... | true with specProblem (decls c)
    ... | just e = done (invalidSpec e)
    ... | nothing with specImplOK (parentFlags parent) c
    ... | ps@(_ ∷ _) = done (invalidSpec ("subspec closedImplOK:\n" ++ˢ unlines (map showImplProblem ps)))
    ... | [] =
      let subΔ = specΔ (modName c) (decls c) []
          next = do
            rest ← dumpSubspecs ss deps bases parent siblings
            done (join rest)
      in if eqCode (specCheckOf subΔ) (stubOf subΔ) then next else do
        cr ← checkAgda (agdaCheck (specCheckOf subΔ) bases)
        afterCheck cr next
      where
        join : Subspecs → Subspecs
        join (invalidSpec e) = invalidSpec e
        join (specs rs) = specs ((modName c , decls c) ∷ rs)
        afterCheck : CheckResult → Prog NodeΨ (Dir (plug toolPrefix _)) (Dir (plug toolPrefix _)) Subspecs
                   → Prog NodeΨ (Dir (plug toolPrefix _)) (Dir (plug toolPrefix _)) Subspecs
        afterCheck pass k = k
        afterCheck (fail e) _ = done (invalidSpec ("subspec failed Agda typecheck:\n" ++ˢ e))

checkSubspecList : ∀ {Γ} → List (QName × List Decl) → List Code
                 → Prog NodeΨ (Dir (plug toolPrefix Γ)) (Dir (plug toolPrefix Γ)) (Maybe String)
checkSubspecList [] bases = done nothing
checkSubspecList ((k , ds) ∷ rest) bases = do
  cr ← checkAgda (agdaCheck (specCheckOf (specΔ k ds [])) bases)
  afterSubCheck cr
  where
    afterSubCheck : CheckResult → Prog NodeΨ (Dir (plug toolPrefix _)) (Dir (plug toolPrefix _)) (Maybe String)
    afterSubCheck pass = checkSubspecList rest bases
    afterSubCheck (fail e) = done (just ("subspec failed Agda typecheck:\n" ++ˢ e))

commitLeaves : ∀ {Ψ} (p : Prefix) → Code → Memory → Interface
             → Prog Ψ (Dir (plug p Leaves)) (Dir (plug p Leaves)) ⊤
commitLeaves p c m i = do
  _ ← replaceHead p c
  _ ← replaceHead (push ("code" , File Code) p) m
  _ ← replaceHead (push ("memory" , File Memory) (push ("code" , File Code) p)) i
  done tt

commitBelow : ∀ {Ψ} (p : Prefix) (ks : List (Name × HomeShape)) → Code → Memory → Interface
            → Prog Ψ (Dir (plug p (KidsCtx ks ++ Leaves))) (Dir (plug p (KidsCtx ks ++ Leaves))) ⊤
commitBelow p [] = commitLeaves p
commitBelow p ((n , sh) ∷ ks) = commitBelow (push (n , HomeSt sh) p) ks

shutdownLiftObstruction ks s = freezeVerifiedKids toolPrefix ks λ ss →
  run (snapshotKids toolPrefix ss) λ snapshot →
  let kids = NT.children (freezeHome (node ss) snapshot)
      shell = code (child (δ (task s))) [] (map kidImport kids)
  in run (commitBelow toolPrefix ss shell (oldMemory s) []) λ _ → giveStoppedHome ss
  where
    kidImport : Name × NT.Frozen → Decl
    kidImport (n , h) = let q , iface = NT.keptIface (moduleQName n , h)
                        in import′ q false everything iface

-- A finite transaction returns its next state together with the entire owned
-- resource context. The kernel's machine coiterator supplies the sole loop.
StepEnd : Session
StepEnd = ∃Res (Slots × NodeState) (λ j → Dir (Work (proj₁ j))) ⊗ End

StepReply : Session
StepReply = Dat (Maybe Verdict) ⊗ StepEnd

oneTurn : (ks : Slots) → NodeState → Proc NodeΨ (Work ks) (Dat ⊤ ⊸ StepReply)
nodeServer : (ks : Slots) → NodeState → ServerI NodeΨ ⊤ (Maybe Verdict) HomeShape (Work ks) HomeSt
respond : (ks : Slots) → NodeState → Maybe Verdict → Proc NodeΨ (Work ks) StepReply
planning : (ks : Slots) → NodeState → Proc NodeΨ (Work ks) StepReply
handle : (ks : Slots) → NodeState → Maybe Submission → Proc NodeΨ (Work ks) StepReply
checkPlan : (ks : Slots) → NodeState → Plan → Proc NodeΨ (Work ks) StepReply
finish : (ks : Slots) → NodeState → Plan → Proc NodeΨ (Work ks) StepReply

checkEvidence : (ks : Slots) → NodeState → String → CheckPurpose → String
              → (QName → List String → Code → List RefuteProblem) → (Code → Verdict)
              → Proc NodeΨ (Work ks) StepReply
checkEvidence ks s src purpose gate validateProof verdict =
  run (dumpSource (dumpSubmission src [] deps)) λ where
    (dumpFailed e) → respond ks (retry s e) nothing
    (dumped c) → verify c (validateProof (child (δ t)) (parentFlags t) c)
  where
    t = task s
    deps = refuteStubOf (δ t) ∷ baseModules t
    verify : Code → List RefuteProblem → Proc NodeΨ (Work ks) StepReply
    verify c ps@(_ ∷ _) = respond ks (retry s (gate ++ˢ ":\n" ++ˢ unlines (map showRefuteProblem ps))) nothing
    verify c [] = run (checkAgda (checkRequest c deps purpose)) λ where
      (fail e) → respond ks (retry s e) nothing
      pass → respond ks (record s { phase = Done (verdict c) }) (just (verdict c))

oneTurn ks s = ask λ _ → next (phase s)
  where
    next : Phase → Proc NodeΨ (Work ks) StepReply
    next Planning = planning ks s
    next (Done v) = respond ks s (just v)
    next WaitingKids = pollNamedKids toolPrefix ks after
      where
        revise : (next : Slots) → String → Proc NodeΨ (Work next) StepReply
        revise next detail = respond next (record (retry s detail)
          { oldCode = runningCode s
          ; oldMemory = maybe′ (λ p → inherit p (oldMemory s)) (oldMemory s) (pending s)
          ; pending = nothing
          ; pendingRawSubs = []
          ; task = record (task s) { δ = reseedSelf (runningCode s) (δ (task s)) }
          }) nothing
        after : (next : Slots) → Maybe (Name × Verdict) → Proc NodeΨ (Work next) StepReply
        after next (just (_ , contradiction c)) = revise next ("child contradiction:\n" ++ˢ render c)
        after next (just (n , liftObstruction why culprits c)) = revise next
          ("child " ++ˢ liftObstructionSummary why culprits ++ˢ "\nCHILD: " ++ˢ n
           ++ˢ "\nIf your local child split/bridge caused this, revise your plan; if the base blueprint itself makes your SPECIFICATION unliftable, submit (submission (kind refute-lift) (why \"...\") (refute @proof)):\n" ++ˢ render c)
        after next (just (_ , independent why c)) = revise next
          ("child independent (--safe unprovability witness" ++ˢ (if why ==ˢ "" then "" else " — " ++ˢ why)
           ++ˢ "; your subspec is consistent in the standard model, NOT false, so keep intended semantics and replace opaque --safe primitives like primStringEquality/primCharEquality, String roundtrips, or function _≡_ with --safe reflective definitions such as Context.Tools.FsSandbox.eqStr, Data.String.Properties._≟_, Data.Char.Properties._≟_, toℕ, or pointwise equality):\n" ++ˢ render c)
        after next _ with ready next | pending s
        ... | true | just p = finish next s p
        ... | _ | _ = respond next s nothing
respond ks s r = tell r (give∃Dir (ks , s) refl)

planning ks s = run (askAI (propose (nodePrompt (task s) (oldCode s) (oldMemory s) (draft (pending s) ++ˢ diagnostic s)) (not (diagnostic s ==ˢ ""))
  (Preview.planContext (task s) (oldCode s) (siblingModules [] ks)))) λ reply →
  let rawTxt = AIReply.text reply in
  caseSub rawTxt (parseSubmission rawTxt)
  where
    draft : Maybe Plan → String
    draft nothing = ""
    draft (just p) = "PENDING DRAFT (add-moves extends this plan):\n"
      ++ˢ moduleText (task s) (apply p (oldCode s)) ++ˢ "\n"
      ++ˢ Code.SExpr.showSExpr (Code.Encode.encodePlan (plan (why p) [] (moves p))) ++ˢ "\n"
    caseSub : String → Maybe Submission → Proc NodeΨ (Work ks) StepReply
    caseSub rawTxt nothing = respond ks (retry s ("submission: malformed envelope or source block — " ++ˢ explainSubmissionFailure rawTxt)) nothing
    caseSub _ (just sub) = handle ks s (just sub)

handle ks s nothing = respond ks (retry s "submission: malformed envelope or source block") nothing
handle ks s (just (refute src)) = checkEvidence ks s src ordinaryCheck "validRefutation" validateContradiction contradiction
  where
    validateContradiction : QName → List String → Code → List RefuteProblem
    validateContradiction spec allowed c = witnessNamespaceProblems spec c ++ validRefutation spec allowed c
handle ks s (just (submitIndependent why src)) = checkEvidence ks s src
  (independenceCheck (child (δ (task s))) (parentFlags (task s)) (rawSpecSource (task s)) src) "validIndependence" validIndependence (independent why)
handle ks s (just (refuteLift why src)) with baseModules (task s)
... | [] = respond ks (retry s "refute-lift: node has no base modules to refute; use (kind contradiction) if SPECIFICATION is inconsistent") nothing
... | bases@(_ ∷ _) = checkEvidence ks s src ordinaryCheck "validLiftRefutation"
  (λ spec → validLiftRefutation spec bases) (λ c → liftObstruction why (extractCulpritBaseUnits bases c) c)
handle ks s (just (submitPlan why src subs ms)) = run
  (dumpSubspecs subs [] (baseModules (task s)) (task s) (siblingModules subs ks)) λ where
  (invalidSpec e) → respond ks (retry s e) nothing
  (specs ifaces) →
    let mergedIfaces = candidateInterfaces (task s) (oldCode s) ifaces
        deps = nodeDeps (task s) (map (λ e → stubOf (specΔ (proj₁ e) (proj₂ e) [])) mergedIfaces)
        mergedRawSubs = subs ++ filterᵇ (λ e → not (elemᵇ _==ˢ_ (proj₁ e) (map proj₁ subs))) (pendingRawSubs s)
    in run (dumpSource (dumpSubmission src [] deps)) λ where
      (dumpFailed e) → respond ks (retry s e) nothing
      (dumped c) → if modName c ==ᴺ child (δ (task s)) then
        (let withIfaces = withChildIfaces mergedIfaces c
             importedMods = map imod (childImports withIfaces)
             unimported = filterᵇ (λ e →
               not (elemᵇ _==ᴺ_ (proj₁ e) importedMods)
               ∧ eqCode (specCheckOf (specΔ (proj₁ e) (proj₂ e) [])) (stubOf (specΔ (proj₁ e) (proj₂ e) []))) ifaces
         in run (checkSubspecList unimported (baseModules (task s)))
           (λ { (just e) → respond ks (retry s e) nothing
              ; nothing → checkPlan ks (record (rememberSource s c src) { pendingRawSubs = mergedRawSubs }) (candidatePlan (task s) why c mergedIfaces ms) }))
        else respond ks (retry s "main: module name differs from assigned ownership node") nothing
handle ks s (just (addMoves ms src)) with pending s
... | nothing = respond ks (retry s "add-moves: no pending plan") nothing
... | just p = extend src
  where
    extend : Maybe String → Proc NodeΨ (Work ks) StepReply
    extend nothing = checkPlan ks s (record p { moves = mergeMoves (moves p) ms })
    extend (just src) = run (dumpSource (dumpSubmission src [] (nodeDeps (task s) (stubs (apply p (oldCode s)) p)))) λ where
      (dumpFailed e) → respond ks (retry s e) nothing
      (dumped c) → if modName c ==ᴺ child (δ (task s)) then checkPlan ks (rememberSource s c src) (record p
        { new = decls (withChildIfaces (map (λ i → imod i , assumes i) (childImports (apply p (oldCode s)))) c)
        ; moves = mergeMoves (moves p) ms }) else respond ks (retry s "main: wrong ownership node") nothing

checkPlan ks s p with planError s p (apply p (oldCode s))
... | just e = respond ks (record (retry s e) { pending = just p }) nothing
... | nothing = run (checkAgda (agdaCheck (withTests cand (newIface (δ (task s)))) (nodeDeps (task s) (stubs cand p)))) checkedGlue
  where
    cand = apply p (oldCode s)
    proceed : (next : Slots) → Memory → Maybe String → Proc NodeΨ (Work next) StepReply
    proceed next mem (just e) = respond next (record (retry s e) { pending = just p ; oldMemory = mem }) nothing
    proceed [] mem nothing = finish [] (record s { pending = just p ; oldMemory = mem ; runningCode = cand }) p
    proceed next@(_ ∷ _) mem nothing = respond next (record s { pending = just p ; oldMemory = mem ; runningCode = cand ; diagnostic = "" ; phase = WaitingKids }) nothing
    checkedGlue : CheckResult → Proc NodeΨ (Work ks) StepReply
    checkedGlue (fail e) = respond ks (record (retry s ("glue 2.3:\n" ++ˢ e)) { pending = just p }) nothing
    checkedGlue pass = reconcileWithRaw (pendingRawSubs s) toolPrefix ks (task s) (runningCode s) cand p (oldMemory s) λ next mem →
      birthWithRaw (pendingRawSubs s) (childImports cand) next (task s) cand p mem λ next′ err → proceed next′ mem err

finish ks s p = freeze toolPrefix ks λ ss →
  run (snapshotKids toolPrefix ss) λ snapshot →
  run (checkAgda (agdaCheck checked (nodeDeps (task s) (Data.List.concatMap (λ { (n , h) → NT.slotAliases (moduleQName n) h ++ NT.exported h })
    (NT.children (freezeHome (node ss) snapshot)))))) (checkedLink ss)
  where
    checked = withTests (apply p (oldCode s)) (newIface (δ (task s)))
    checkedLink : (ss : List (Name × HomeShape)) → CheckResult → Proc NodeΨ (plug toolPrefix (KidsCtx ss ++ Leaves)) StepReply
    checkedLink ss (fail e) = castP (cong (plug toolPrefix) (closedCtx ss))
      (respond (closed ss) (retry s ("final link:\n" ++ˢ e)) nothing)
    checkedLink ss pass = run (askAI (accept (why p ++ˢ "\n" ++ˢ moduleText (task s) checked))) λ _ →
      run (commitBelow toolPrefix ss checked (inherit p (oldMemory s)) (newIface (δ (task s)))) λ _ →
      castP (cong (plug toolPrefix) (closedCtx ss))
        (respond (closed ss) (record s { oldCode = checked ; oldMemory = inherit p (oldMemory s) ; diagnostic = "" ; phase = Done ok }) (just ok))

ServerI.call (nodeServer ks s) = ask λ _ → tell nothing
  (machine (λ j → oneTurn (proj₁ j) (proj₂ j)) (λ j → shutdownState (proj₁ j) (proj₂ j)) (ks , s))
ServerI.stop (nodeServer ks s) = shutdownState ks s

-- A malformed persisted shape remains stoppable and cannot allocate tools over
-- an existing child. Validated submissions never create these reserved names.
dormant : (sh : HomeShape) → ServerI NodeΨ ⊤ (Maybe Verdict) HomeShape (Home (HomeCtx sh)) HomeSt
ServerI.call (dormant sh) = ask λ _ → tell nothing (daemon (dormant sh))
ServerI.stop (dormant sh) = give∃Dir sh refl

nodeAgent : (sh : HomeShape) → Proc NodeΨ (Home (HomeCtx sh)) AgentS
nodeAgent sh@(node kids) = ask λ task → start (certify sh) task
  where
    start : Maybe (Clean sh) → NodeTask → Proc NodeΨ (Home (HomeCtx sh)) ChildS
    start nothing task = daemon (dormant sh)
    start (just clean) task = run (snapshotHome sh) λ snapshot →
      insertDir root "ai"
        (run (openHead root (here refl) tt) λ _ →
         insertDir root "dump"
           (run (openHead root (there (here refl)) tt) λ _ →
            insertDir root "agda"
              (run (openHead root (there (there (here refl))) tt) λ _ →
               run (askAI (bindNode (intersperse "." (full (child (δ task)))) (inheritedThread task))) λ _ →
               castP (cong (plug toolPrefix) (closedCtx kids))
                 (daemon (nodeServer (closed kids) (nodeState task (codeOf sh snapshot) (memoryOf sh snapshot) (codeOf sh snapshot) nothing "" Planning (sh , clean , snapshot)))))
              (dropHead root (λ _ → tt) (dropHead root (λ _ → tt) (daemon (dormant sh)))))
           (dropHead root (λ _ → tt) (daemon (dormant sh))))
        (daemon (dormant sh))

observeN : ∀ {M : Set} → ℕ → Running ⊤ (Maybe Verdict) M → Maybe Verdict × Running ⊤ (Maybe Verdict) M
observeN zero r = nothing , r
observeN (suc n) r with Running.onCall r tt
... | just v , next = just v , next
... | nothing , next = observeN n next

pollN : ∀ {M : Set} → ℕ → Running ⊤ (Maybe Verdict) M → Maybe Verdict
pollN n r = proj₁ (observeN n r)
