module Code.NodeTransport where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (intersperse; wordsBy)
import Data.Char as Char
open import Code
open import Code.Transport using (Memory; requalify; nullᵇ)
import Code.Namespace as NS
import Code.Lift as L
open import Code.PolyTransport

-- Plain sealed data can cross the node protocol. Live ownership channels cannot.
data Frozen : Set where
  frozen : Code → Memory → List Decl → List (Name × Frozen) → Frozen

implementation : Frozen → Code
implementation (frozen c _ _ _) = c

-- Public units of an identity re-export can also be addressed at the slot
-- name in a descriptor. This view is only used for static obligations.
implementationAt : QName → Frozen → Code
implementationAt q h = record (renameCode (requalify (modName c) q) c) { modName = q }
  where c = implementation h

interface : Frozen → List Decl
interface (frozen _ _ ds _) = ds

children : Frozen → List (Name × Frozen)
children (frozen _ _ _ ks) = ks

moduleKey : QName → Name
moduleKey m = intersperse "." (full m)

moduleQName : Name → QName
moduleQName n = mkQ (wordsBy ('.' Char.≟_) n)

lookupChild : Frozen → QName → Maybe Frozen
lookupChild h q = find (children h)
  where
    find : List (Name × Frozen) → Maybe Frozen
    find [] = nothing
    find ((n , child) ∷ ks) = if n ==ˢ moduleKey q then just child else find ks

-- A relocated identity slot re-exports the old module. Its HomeNode and all
-- of its descendants retain their original content addresses.
aliasCode : QName → QName → Code
aliasCode target source = code target []
  [ import′ (qn (full source) (moduleKey source)) true (record everything { dpublic = true }) [] ]

slotAliases : QName → Frozen → List Code
slotAliases q h = if q ==ᴺ src then [] else [ aliasCode q src ]
  where src = modName (implementation h)

exported : Frozen → List Code
exported (frozen c _ _ ks) = c ∷ forest ks
  where
    forest : List (Name × Frozen) → List Code
    forest [] = []
    forest ((n , h) ∷ rest) = slotAliases (moduleQName n) h ++ exported h ++ forest rest

Bindings = List (Frozen × TransportSpec)

keeps : Bindings → List (QName × Frozen)
keeps = concatMap (λ { (h , s) → Data.List.mapMaybe (kept h) (childMovesOf s) })
  where
    kept : Frozen → ChildMove → Maybe (QName × Frozen)
    kept h (keepChild o n) = Data.Maybe.map (n ,_) (lookupChild h o)
    kept _ _ = nothing

keptIface : QName × Frozen → QName × List Decl
keptIface (n , h) = n , renameDecls (requalify (modName (implementation h)) n) (interface h)

-- Agda resolves a public re-export back to the defining module. Only a
-- lookup of the declared source slot may translate a nested descriptor.
atDefinition : Frozen → TransportSpec → TransportSpec
atDefinition h s@(transportSpecTree old new cs squares) =
  if old ==ᴺ original then s else transportSpecTree original new cs (map atSource squares)
  where
    original = modName (implementation h)
    rename = requalify old original
    atSource : PolySquareSpec → PolySquareSpec
    atSource sq = record sq { oldUnits = map rename (oldUnits sq) ; requiredRefs = map rename (requiredRefs sq) }

subBindings : Bindings → QName → Bindings
subBindings bs q = concatMap descend bs
  where
    descend : Frozen × TransportSpec → Bindings
    descend (h , s) = concatMap subs (childMovesOf s)
      where
        bindSub : TransportSpec → Maybe (Frozen × TransportSpec)
        bindSub sub = if newModOf sub ==ᴺ q then Data.Maybe.map (λ kid → kid , atDefinition kid sub) (lookupChild h (oldModOf sub)) else nothing
        subs : ChildMove → Bindings
        subs (keepChild _ _) = []
        subs (moveChildren _ _ ss) = Data.List.mapMaybe bindSub ss

-- All nested obligations must be dispatched to an actual target slot.
targetsOfMove : ChildMove → List QName
targetsOfMove (keepChild _ n) = [ n ]
targetsOfMove (moveChildren _ ns _) = ns

-- Only an existing source slot may keep its name outside the new epoch.
-- A freshly named re-export belongs directly under its new parent.
retainedNames : TransportSpec → List QName
retainedNames s = Data.List.mapMaybe retained (childMovesOf s)
  where
    retained : ChildMove → Maybe QName
    retained (keepChild o n) = Data.Maybe.when (o ==ᴺ n) n
    retained _ = nothing

sourceNames : Bindings → QName → List QName
sourceNames bs q = concatMap (λ { (_ , s) → concatMap sources (childMovesOf s) }) bs
  where
    sources : ChildMove → List QName
    sources (keepChild o n) = if n ==ᴺ q then [ o ] else []
    sources (moveChildren os ns _) = if elemᵇ _==ᴺ_ q ns then os else []

validSource : Frozen → TransportSpec → Bool
validSource h s@(transportSpecTree old new cs _) =
  movesOK cs
  ∧ allᵇ (λ k → elemᵇ _==ᴺ_ (moduleQName (proj₁ k)) oldSlots) (children h)
  ∧ nullᵇ (NS.checkOwnedNames new (concatMap targetsOfMove cs) (retainedNames s) [])
  where
    sources : ChildMove → List QName
    sources (keepChild o _) = [ o ]
    sources (moveChildren os _ _) = os
    oldSlots = concatMap sources cs
    present : QName → Bool
    present q = Data.Maybe.is-just (lookupChild h q)
    nested : List QName → List QName → List TransportSpec → Bool
    nested os ns [] = true
    nested os ns (s ∷ ss) with lookupChild h (oldModOf s)
    ... | nothing = false
    ... | just sub = elemᵇ _==ᴺ_ (oldModOf s) os ∧ elemᵇ _==ᴺ_ (newModOf s) ns
                   ∧ validSource sub s ∧ nested os ns ss
    movesOK : List ChildMove → Bool
    movesOK [] = true
    movesOK (keepChild o n ∷ rest) = present o ∧ movesOK rest
    movesOK (moveChildren os ns ss ∷ rest) = allᵇ present os ∧ nested os ns ss ∧ movesOK rest

findKeep : Bindings → QName → Maybe Frozen
findKeep bs q = go (keeps bs)
  where
    go : List (QName × Frozen) → Maybe Frozen
    go [] = nothing
    go ((n , h) ∷ rest) = if n ==ᴺ q then just h else go rest

keepAliases : Bindings → List Code
keepAliases bs = concatMap (λ { (q , h) → slotAliases q h }) (keeps bs)

-- A retained implementation gets no planning turn. Check any new vertical
-- obligations on that implementation and its retained descendants here.
retainedLift : List Code → Code → L.LiftSpec → List L.LiftProblem
retainedLift cs target (L.liftSpecTree base upper entries squares) with findCode base cs
  where
    findCode : QName → List Code → Maybe Code
    findCode q [] = nothing
    findCode q (c ∷ rest) = if modName c ==ᴺ q then just c else findCode q rest
... | nothing = [ L.missingBaseUnit base ]
... | just b = L.checkLift b target [] (L.liftSpecTree base upper entries squares) ++ nested entries
  where
    nested : List L.ChildLift → List L.LiftProblem
    nested [] = []
    nested (L.mkChildLift _ _ nothing ∷ rest) = nested rest
    nested (L.mkChildLift _ q (just s) ∷ rest) with filterᵇ (λ c → modName c ==ᴺ q) cs
    ... | [] = L.missingChildImport q ∷ nested rest
    ... | c ∷ _ = retainedLift cs c s ++ nested rest

checkKeptLifts : List Code → Bindings → L.LiftSpec → List L.LiftProblem
checkKeptLifts cs bs l = concatMap inspect (L.childLifts l)
  where
    inspect : L.ChildLift → List L.LiftProblem
    inspect (L.mkChildLift _ q (just s)) with findKeep bs q
    ... | nothing = []
    ... | just h = retainedLift (exported h ++ cs) (implementationAt q h) s
    inspect _ = []
