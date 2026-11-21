module Code.HarnessCore where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; unlines; intersperse) renaming (_++_ to _++ˢ_)

open import Code hiding (set)
open import Code.Transport
open import Code.Lift
open import Code.Render using (render)
open import Code.Encode using (encDecl; encObj)
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

record NarrowingCertificate : Set where
  constructor certificate
  field
    kind witness cause detour : String

showCertificate : NarrowingCertificate → String
showCertificate (certificate k w c d) = unlines
  (("[KIND] " ++ˢ k) ∷ ("[WITNESS] " ++ˢ w) ∷ ("[CAUSE] " ++ˢ c) ∷ ("[DETOUR] " ++ˢ d) ∷ [])

launderedLaws : Code → List Unit
launderedLaws c = filterᵇ externalLaw us
  where
    us = units c
    ports = filterᵇ carrierOrOperation us
    externalLaw : Unit → Bool
    externalLaw u = isPostulate ds ∧ anyᵇ lawSignature ds
      ∧ not (anyᵇ (λ ref → anyᵇ (λ port → unitOwns port ref) ports) (refsDecls ds))
      where ds = udecls u

launderingCertificate : Unit → NarrowingCertificate
launderingCertificate u = certificate "subspec_laundering" (NT.moduleKey (uname u))
  "The postulated law only refers to external symbols. No local data/record port or local operation occurs in its signature."
  "State the law over a child-owned port. If the parent specification entails a safe taboo, derive Context.Taboo.SafeTaboo and submit (kind independent)."

subspecLaunderingProblem : Code → Maybe String
subspecLaunderingProblem c with launderedLaws c
... | [] = nothing
... | us@(_ ∷ _) = just ("subspec axiom-laundering narrowing gate:\n" ++ˢ unlines (map (λ u → showCertificate (launderingCertificate u)) us))

depthCertificate : Code → NarrowingCertificate
depthCertificate c = certificate "subspec_narrowing" (NT.moduleKey (modName c))
  "The child exceeds the ownership depth Gen.<Epoch>.<Root>.<Child>.<Grandchild>."
  "Split siblings horizontally. If the specification entails a safe taboo, derive Context.Taboo.SafeTaboo and submit (kind independent)."

subspecCertificates : Code → List NarrowingCertificate
subspecCertificates c = if tooDeep (full (modName c)) then depthCertificate c ∷ [] else map launderingCertificate (launderedLaws c)

subspecNarrowingProblem : Code → Maybe (String × String)
subspecNarrowingProblem c with tooDeep (full (modName c))
... | true = just ("subspec_depth_cap" , ("subspec depth-cap narrowing gate:\n" ++ˢ showCertificate (depthCertificate c)))
... | false with subspecLaunderingProblem c
...   | just e = just ("subspec_axiom_laundering" , e)
...   | nothing = nothing

unsafeCertificate : String → NarrowingCertificate
unsafeCertificate q = certificate "unsafe_module" q
  "Agda --safe excludes TrustMe and Unsafe modules and their declarations."
  "Use a constructive safe import. For an unprovable requirement, derive Context.Taboo.SafeTaboo from the specification and submit (kind independent)."

frontierCertificates : Code → Code → Plan → List Obj → List NarrowingCertificate
frontierCertificates old cand p os = map explain os
  where
    objText : Obj → String
    objText o = showSExpr (encObj o)

    oldEdges = arrows old
    changedSources = changed old cand p

    explain : Obj → NarrowingCertificate
    explain o = certificate "frontier_incomplete" (objText o)
      (intersperse ", " (map objText upstream) ++ˢ " changed interface. Its dependent " ++ˢ objText o ++ˢ " has no outgoing proarrow.")
      ("If it survives, add (move " ++ˢ objText o ++ˢ " " ++ˢ objText o ++ˢ "). Otherwise supply its rewrite or deletion move.")
      where upstream = map proj₂ (filterᵇ (λ e → (proj₁ e ==ᴼ o) ∧ elemᵇ _==ᴼ_ (proj₂ e) changedSources) oldEdges)

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
  ; authoredSources = authoredSources parent
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

subspecBoundaryProblem : NodeTask → List QName → Code → Maybe String
subspecBoundaryProblem t siblings c with subspecImportProblem (child (δ t)) siblings collisionBases c
  where collisionBases = filterᵇ (λ b → not (elemᵇ _==ᴺ_ (modName b) (map proj₁ (NT.keeps (transports t))))) (baseModules t)
... | just e = just e
... | nothing with childAncestors t (modName c)
...   | nothing = nothing
...   | just allowed with NS.checkTaskImports (NS.namespaceOf (modName c)) [] allowed c
...     | [] = nothing
...     | ps@(_ ∷ _) = just ("subspec namespace: " ++ˢ unlines (map NS.showNamespaceProblem ps))

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

record InterfaceMismatch : Set where
  constructor mismatch
  field name summary detail : String
open InterfaceMismatch

satisfiesMismatches : SpecΔ → Code → List InterfaceMismatch
satisfiesMismatches δ cand with localizeTo (child δ) (newIface δ)
... | loc with unitsIn (full (child δ)) loc | units cand | coreNames (child δ) (newIface δ)
... | us | newUnits | core = concatMap inspect us
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

    inspect : Unit → List InterfaceMismatch
    inspect u with anonymousUnit u | lookupUnit newUnits (uname u)
    ... | true  | _       = []
    ... | false | nothing =
      if elemᵇ _==ᴺ_ (uname u) core
        then (mismatch (qstr (uname u)) ("missing core unit " ++ˢ qstr (uname u)) (renderWitness (sigOnlyDecls (udecls u)) [])) ∷ []
        else []
    ... | false | just v  =
      if elemᵇ _==ᴺ_ (uname u) core ∧ not (hasFun (udecls u))
        then (if eqIface (ifaceOfDecls (udecls u)) (ifaceOfDecls (udecls v))
                then []
                else (mismatch (qstr (uname u)) ("changed interface on " ++ˢ qstr (uname u))
                      (renderWitness (sigOnlyDecls (udecls u)) (sigOnlyDecls (udecls v)))) ∷ [])
        else (if eqDecls (udecls u) (udecls v)
                then []
                else (mismatch (qstr (uname u)) ("changed concrete helper or test on " ++ˢ qstr (uname u))
                      (renderWitness (udecls u) (udecls v))) ∷ [])

satisfiesDetails : SpecΔ → Code → List String
satisfiesDetails d cand = map (λ m → summary m ++ˢ detail m) (satisfiesMismatches d cand)

interfaceCertificate : InterfaceMismatch → NarrowingCertificate
interfaceCertificate m = certificate "subspec_narrowing" (name m) (summary m ++ˢ detail m)
  "Copy the required core signature or concrete helper from SPECIFICATION and keep its qualified export."

-- Submitted, kept and surviving old interfaces are merged identically for
-- production scope checking, candidate assembly and read-only previews.
candidateInterfaces : NodeTask → Code → List (QName × List Decl) → List (QName × List Decl)
candidateInterfaces t old ifaces = ifaces ++ kept ++ map (λ i → imod i , assumes i) retained
  where
    submitted = map proj₁ ifaces
    kept = filterᵇ (λ e → not (elemᵇ _==ᴺ_ (proj₁ e) submitted)) (map NT.keptIface (NT.keeps (transports t)))
    retained = filterᵇ (λ i → not (elemᵇ _==ᴺ_ (imod i) (submitted ++ map proj₁ kept))) (childImports old)

candidatePlan : NodeTask → String → Code → List (QName × List Decl) → List Proarrow → Plan
candidatePlan t reason c merged ms = plan reason (decls (withChildIfaces merged c)) (mergeMoves (seedArrows (δ t)) ms)

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
