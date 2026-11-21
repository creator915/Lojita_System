module Code.HarnessCore where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; take; drop; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Show as ℕshow
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; unlines; intersperse) renaming (_++_ to _++ˢ_)

open import Code hiding (set)
open import Code.Transport
open import Code.Lift
open import Code.Render using (render)
open import Code.Encode using (encDecl)
open import Code.SExpr using (list; showSExpr)
import Code.NodeTransport as NT
import Code.Namespace as NS
import Code.PolyTransport as PT
open import Code.Protocol
open import Code.Prompt using (showProblem; showImplProblem; showLiftProblem)

open NT using (moduleQName)

firstEvidence : Maybe Code → Maybe Code → Maybe Code
firstEvidence (just c) _ = just c
firstEvidence nothing c = c

private
  -- Dump resolves aliases and infix syntax to canonical names. Only the
  -- result of a signature determines whether it declares a law.
  lawResult : Expr → Bool
  lawResult (pi _ t) = lawResult t
  lawResult (fun′ _ t) = lawResult t
  lawResult (app f _) = lawResult f
  lawResult t@(def q) = tabooExpr t
    ∨ (q ==ᴺ mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ []))
    ∨ (q ==ᴺ mkQ ("Relation" ∷ "Binary" ∷ "PropositionalEquality" ∷ "Core" ∷ "_≢_" ∷ []))
    ∨ (q ==ᴺ mkQ ("Relation" ∷ "Nullary" ∷ "¬_" ∷ []))
  lawResult _ = false

  lawSignature : Decl → Bool
  lawSignature (sig _ _ t) = lawResult t
  lawSignature _ = false

  carrierDecl : Decl → Bool
  carrierDecl (dataSig _ _ _ _) = true
  carrierDecl (recSig _ _ _ _) = true
  carrierDecl (dataDef _ _ _ _) = true
  carrierDecl (recDef _ _ _ _ _) = true
  carrierDecl _ = false

  carrierOrOperation : Unit → Bool
  carrierOrOperation u = anyᵇ carrierDecl ds ∨ hasFun ds ∨ (isPostulate ds ∧ not (anyᵇ lawSignature ds))
    where ds = udecls u

  tooDeep : List Name → Bool
  tooDeep ("Gen" ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) = true
  tooDeep _ = false

subspecLaunderingProblem : Code → Maybe String
subspecLaunderingProblem c with units c
... | us with filterᵇ carrierOrOperation us
... | ports with filterᵇ externalLaw us
  where
    externalLaw : Unit → Bool
    externalLaw u = isPostulate ds ∧ anyᵇ lawSignature ds
      ∧ not (anyᵇ (λ ref → anyᵇ (λ port → unitOwns port ref) ports) (refsDecls ds))
      where ds = udecls u
... | [] = nothing
... | laws@(_ ∷ _) = just ("subspec axiom-laundering narrowing gate: postulate '"
  ++ˢ intersperse "', '" (map (λ u → intersperse "." (full (uname u))) laws)
  ++ˢ "' asserts an unproved equation/law purely over external/stdlib symbols without referencing any local data/record port or local postulated operation in '"
  ++ˢ intersperse "." (full (modName c))
  ++ˢ "'. Do NOT delegate unproved stdlib/primitive axioms to empty child subspecs! If your own SPECIFICATION requires a property that is unprovable in Agda 2.6.3 --safe (e.g. primStringEquality / primCharEquality variable reflexivity or soundness, String toList/fromList roundtrips, or FunExt), prove Context.Taboo.SafeTaboo and submit (submission (kind independent) (why \"...\") (refute @...)) to return the broken specification to your parent.")

subspecNarrowingProblem : Code → Maybe (String × String)
subspecNarrowingProblem c with tooDeep (full (modName c))
... | true = just ("subspec_depth_cap" , ("subspec depth-cap narrowing gate: '" ++ˢ intersperse "." (full (modName c))
  ++ˢ "' exceeds the 3-level ownership hierarchy Gen.<Epoch>.<Root>.<Child>.<Grandchild>. Split siblings horizontally, or if the SPECIFICATION implies a --safe taboo, prove Context.Taboo.SafeTaboo and submit (submission (kind independent) (refute @unprovable))."))
... | false with subspecLaunderingProblem c
...   | just e = just ("subspec_axiom_laundering" , e)
...   | nothing = nothing

childImports : Code → List Import
childImports c = filterᵇ (λ i → not (nullᵇ (assumes i))) (imports c)

-- New epochs grant a child only its declared old/base counterparts. The
-- compiler still has the transitive dependencies needed by those modules.
childAncestors : NodeTask → QName → Maybe (List QName)
childAncestors parent q with allowedAncestors parent
... | nothing = nothing
... | just allowed with NS.epoch (NS.namespaceOf (child (δ parent))) ==ˢ "" | transports parent
...   | true | [] = just allowed
...   | _ | _ = just (NT.sourceNames (transports parent) q ++ lifted (maybeLift parent))
  where
    lifted : Maybe (Code × LiftSpec) → List QName
    lifted nothing = []
    lifted (just (_ , l)) = map baseChild (filterᵇ (λ e → upperChild e ==ᴺ q) (childLifts l))

lookupRawSubspec : List (Name × String) → Name → String
lookupRawSubspec [] _ = ""
lookupRawSubspec ((k , v) ∷ xs) n = if k ==ˢ n then v else lookupRawSubspec xs n

childTaskWithRaw : List (Name × String) → NodeTask → Code → Plan → Name → NodeTask
childTaskWithRaw rawSubs parent c p n = record (nodeTask (restrict c p childQ) (parentFlags parent) childLift)
  { contextText = contextText parent ; baseModules = bases
  ; transports = NT.subBindings (transports parent) childQ ; allowedAncestors = childAncestors parent childQ
  ; rawSpecSource = lookupRawSubspec rawSubs n }
  where
    childQ = moduleQName n
    -- Only the explicitly supplied immutable ancestry can cross this boundary.
    owned = modName c ∷ map imod (childImports c)
    bases = filterᵇ (λ b → not (elemᵇ _==ᴺ_ (modName b) owned)) (baseModules parent)
    childLift : Maybe (Code × LiftSpec)
    childLift with maybeLift parent
    ... | nothing = nothing
    ... | just (base , l) = findMap (childLifts l)
      where
        childSpec : ChildLift → LiftSpec
        childSpec entry with subLift entry
        ... | just sub = sub
        ... | nothing = liftSpec (baseChild entry) childQ [] []
        findBase : ChildLift → List Code → Maybe (Code × LiftSpec)
        findBase entry [] = nothing
        findBase entry (b ∷ bs) = if modName b ==ᴺ baseChild entry then just (b , childSpec entry) else findBase entry bs
        findMap : List ChildLift → Maybe (Code × LiftSpec)
        findMap [] = nothing
        findMap (entry ∷ ms) = if upperChild entry ==ᴺ childQ then findBase entry bases else findMap ms

childTask : NodeTask → Code → Plan → Name → NodeTask
childTask = childTaskWithRaw []

childName : Import → Name
childName i = intersperse "." (full (imod i))

wanted : Code → Name → Bool
wanted c n = anyᵇ (λ i → childName i ==ˢ n) (childImports c)

data Phase : Set where
  Planning WaitingKids : Phase
  Done : Verdict → Phase

liftProblems : NodeTask → Code → List LiftProblem
liftProblems t cand with maybeLift t
... | nothing = []
... | just (base , l) = checkLift base cand (newIface (δ t)) l ++ NT.checkKeptLifts (baseModules t) (transports t) l

scopeProblems : NodeTask → Code → List NS.NamespaceProblem
scopeProblems t c with allowedAncestors t
... | nothing = []
... | just bases = NS.checkOwnedImports (child (δ t)) (map imod (childImports c))
  (concatMap (λ b → NT.retainedNames (proj₂ b)) (transports t)) bases c

transportError : NodeTask → Code → Maybe String
transportError t cand with concatMap checkPair (transports t)
  where
    checkPair : NT.Frozen × PT.TransportSpec → List PT.PolyTransportProblem
    checkPair (h , s) = PT.checkPolyTransport (NT.implementation h) cand (newIface (δ t)) s
... | ps@(_ ∷ _) = just ("checkPolyTransport:\n" ++ˢ unlines (map PT.showPolyTransportProblem ps))
... | [] = if allᵇ owned (concatMap targets (transports t)) ∧ allᵇ unchanged (NT.keeps (transports t))
           then nothing else just "checkPolyTransport: missing owned target or changed keepChild interface"
  where
    targets : NT.Frozen × PT.TransportSpec → List QName
    targets (_ , s) = concatMap NT.targetsOfMove (PT.childMovesOf s)
    owned : QName → Bool
    owned q = anyᵇ (λ i → imod i ==ᴺ q) (childImports cand)
    unchanged : QName × NT.Frozen → Bool
    unchanged pair = anyᵇ (λ i → imod i ==ᴺ proj₁ pair ∧ eqDecls (assumes i) (proj₂ (NT.keptIface pair)))
                           (childImports cand)

satisfiesDetails : SpecΔ → Code → List String
satisfiesDetails δ cand with localizeTo (child δ) (newIface δ)
... | loc with unitsIn (full (child δ)) loc | units cand | coreNames (child δ) (newIface δ)
... | us | newUnits | core = formatWitnesses (concatMap inspect us)
  where
    qstr : QName → String
    qstr q = intersperse "." (full q)

    renderWitness : List Decl → List Decl → String
    renderWitness expDs actDs =
      let expTxt = render (code (child δ) [] expDs)
          actTxt = render (code (modName cand) [] actDs)
          sexpNote = if expTxt ==ˢ actTxt
                     then "\n    spec AST: " ++ˢ showSExpr (list (map encDecl expDs))
                          ++ˢ "\n    cand AST: " ++ˢ showSExpr (list (map encDecl actDs))
                     else ""
      in "\n    expected (SPECIFICATION):\n" ++ˢ expTxt
         ++ˢ "\n    actual   (your module):\n" ++ˢ actTxt ++ˢ sexpNote
         ++ˢ "\n    note: `satisfies` checks syntactic AST equality (e.g. `∀ x →` uses `_` meta binder, not explicit `(x : T) →`; copy core signatures and helper definitions verbatim from SPECIFICATION!)"

    isFunDecl : Decl → Bool
    isFunDecl (fun _ _ _) = true
    isFunDecl _ = false

    sigOnlyDecls : List Decl → List Decl
    sigOnlyDecls = filterᵇ (λ d → not (isFunDecl d))

    inspect : Unit → List (String × String)
    inspect u with anonymousUnit u | lookupUnit newUnits (uname u)
    ... | true  | _       = []
    ... | false | nothing =
      if elemᵇ _==ᴺ_ (uname u) core
        then (("missing core unit " ++ˢ qstr (uname u)) , "") ∷ []
        else []
    ... | false | just v  =
      if elemᵇ _==ᴺ_ (uname u) core ∧ not (hasFun (udecls u))
        then (if eqIface (ifaceOfDecls (udecls u)) (ifaceOfDecls (udecls v))
                then []
                else (("changed interface on " ++ˢ qstr (uname u)) ,
                      renderWitness (sigOnlyDecls (udecls u)) (sigOnlyDecls (udecls v))) ∷ [])
        else (if eqDecls (udecls u) (udecls v)
                then []
                else (("changed concrete helper or test on " ++ˢ qstr (uname u)) ,
                      renderWitness (udecls u) (udecls v)) ∷ [])

    tailSummary : List String → List String
    tailSummary [] = []
    tailSummary rs@(_ ∷ _) = ("... plus " ++ˢ ℕshow.show (length rs) ++ˢ " more unit mismatches: " ++ˢ intersperse ", " rs) ∷ []

    formatWitnesses : List (String × String) → List String
    formatWitnesses items =
      map (λ p → proj₁ p ++ˢ proj₂ p) (take 5 items) ++ tailSummary (map proj₁ (drop 5 items))

checkCandidateGates : NodeTask → Code → Plan → Code → Maybe String
checkCandidateGates t old p cand with extendsSeed (δ t) p
... | false = just "extendsSeed: the parent interface moves are locked"
... | true with validate old p cand
... | ps@(_ ∷ _) = just (unlines (map showProblem ps))
... | [] with satisfies (δ t) cand
... | false = just ("satisfies: missing core unit, changed interface, concrete helper, or named test ("
                    ++ˢ intersperse "; " (satisfiesDetails (δ t) cand) ++ˢ ")")
... | true with closedImplOK (parentFlags t) cand
... | ps@(_ ∷ _) = just ("closedImplOK:\n" ++ˢ unlines (map showImplProblem ps))
... | [] with liftProblems t cand
... | ps@(_ ∷ _) = just ("checkLift:\n" ++ˢ unlines (map showLiftProblem ps))
... | [] with scopeProblems t (withTests cand (newIface (δ t)))
... | ps@(_ ∷ _) = just ("namespace: " ++ˢ unlines (map NS.showNamespaceProblem ps))
... | [] = transportError t cand

stubs : Code → Plan → List Code
stubs cand pl = map (λ i → stubOf (restrict cand pl (imod i))) (childImports cand)

nodeDeps : NodeTask → List Code → List Code
nodeDeps t local = filterᵇ (λ c → not (elemᵇ _==ᴺ_ (modName c) kept)) local
                 ++ NT.keepAliases (transports t) ++ concatMap (λ pair → NT.exported (proj₂ pair)) retained ++ baseModules t
  where
    retained = NT.keeps (transports t)
    kept = map proj₁ retained

data Subspecs : Set where
  specs : List (QName × List Decl) → Subspecs
  invalidSpec : String → Subspecs
