module Code.HarnessCore where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; unlines; intersperse) renaming (_++_ to _++ˢ_)

open import Code hiding (set)
open import Code.Transport
open import Code.Lift
import Code.NodeTransport as NT
import Code.Namespace as NS
import Code.PolyTransport as PT
open import Code.Protocol
open import Code.Prompt using (showProblem; showImplProblem; showLiftProblem)

open NT using (moduleQName)

firstEvidence : Maybe Code → Maybe Code → Maybe Code
firstEvidence (just c) _ = just c
firstEvidence nothing c = c

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

childTask : NodeTask → Code → Plan → Name → NodeTask
childTask parent c p n = record (nodeTask (restrict c p childQ) (parentFlags parent) childLift)
  { contextText = contextText parent ; baseModules = bases
  ; transports = NT.subBindings (transports parent) childQ ; allowedAncestors = childAncestors parent childQ }
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
... | us | newUnits | core = concatMap inspect us
  where
    qstr : QName → String
    qstr q = intersperse "." (full q)
    inspect : Unit → List String
    inspect u with anonymousUnit u | lookupUnit newUnits (uname u)
    ... | true  | _       = []
    ... | false | nothing =
      if elemᵇ _==ᴺ_ (uname u) core
        then ("missing core unit " ++ˢ qstr (uname u)) ∷ []
        else []
    ... | false | just v  =
      if elemᵇ _==ᴺ_ (uname u) core ∧ not (hasFun (udecls u))
        then (if eqIface (ifaceOfDecls (udecls u)) (ifaceOfDecls (udecls v))
                then []
                else ("changed interface on " ++ˢ qstr (uname u)) ∷ [])
        else (if eqDecls (udecls u) (udecls v)
                then []
                else ("changed concrete helper or test on " ++ˢ qstr (uname u)) ∷ [])

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
