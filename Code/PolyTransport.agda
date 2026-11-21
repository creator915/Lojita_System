module Code.PolyTransport where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; [_]; _++_; map; concatMap)
open import Data.Maybe using (Maybe; just; nothing; _>>=_; zipWith)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Agda.Builtin.Char using (primCharEquality)

open import Code
open import Code.Transport using (withTests; nullᵇ)
open import Code.SExpr using (SExpr; list; sym; str; parseSExpr; showSExpr)
open import Code.Encode using (encQ)
open import Code.Parse using (decodeQ; decodeNames)

record PolySquareSpec : Set where
  constructor polySquareRefs
  field
    oldUnits newUnits : List QName
    squareUnit        : QName
    requiredRefs      : List QName
open PolySquareSpec public

polySquare : List QName → List QName → QName → PolySquareSpec
polySquare os ns proof = polySquareRefs os ns proof []

mutual
  data TransportSpec : Set where
    transportSpecTree : (oldMod newMod : QName) → List ChildMove → List PolySquareSpec → TransportSpec

  data ChildMove : Set where
    keepChild    : QName → QName → ChildMove
    moveChildren : List QName → List QName → List TransportSpec → ChildMove

oldModOf newModOf : TransportSpec → QName
oldModOf (transportSpecTree o _ _ _) = o
newModOf (transportSpecTree _ n _ _) = n

childMovesOf : TransportSpec → List ChildMove
childMovesOf (transportSpecTree _ _ cs _) = cs

polySquaresOf : TransportSpec → List PolySquareSpec
polySquaresOf (transportSpecTree _ _ _ ss) = ss

keptPairs : TransportSpec → List (QName × QName)
keptPairs (transportSpecTree _ _ cs _) = children cs
  where
    nested : List TransportSpec → List (QName × QName)
    nested [] = []
    nested (s ∷ ss) = keptPairs s ++ nested ss

    children : List ChildMove → List (QName × QName)
    children [] = []
    children (keepChild o n ∷ rest) = (o , n) ∷ children rest
    children (moveChildren _ _ subs ∷ rest) = nested subs ++ children rest

data PolyTransportProblem : Set where
  wrongOldMod wrongNewMod : PolyTransportProblem
  unaccountedOldChild missingTargetChildImport duplicateTargetChild : QName → PolyTransportProblem
  emptySquareEndpoints missingOldEndpoint missingNewEndpoint : QName → PolyTransportProblem
  missingPolySquare invalidPolySquare : QName → PolyTransportProblem

private
  sources targets : ChildMove → List QName
  sources (keepChild o _) = [ o ]
  sources (moveChildren os _ _) = os
  targets (keepChild _ n) = [ n ]
  targets (moveChildren _ ns _) = ns

  missing : (QName → PolyTransportProblem) → List QName → List QName → List PolyTransportProblem
  missing problem expected available =
    map problem (filterᵇ (λ q → not (elemᵇ _==ᴺ_ q available)) expected)

  repeated : List QName → List QName
  repeated [] = []
  repeated (q ∷ qs) with elemᵇ _==ᴺ_ q qs
  ... | true  = q ∷ repeated qs
  ... | false = repeated qs

  -- Child obligations belong to the pair of modules currently being checked.
  checkChildren : List Import → List Import → List ChildMove → List PolyTransportProblem
  checkChildren oldImports newImports cs
    with nubᵇ _==ᴺ_ (map imod (filterᵇ (λ i → not (nullᵇ (assumes i))) oldImports))
       | concatMap sources cs | concatMap targets cs | map imod newImports
  ... | required | os | ns | available =
       missing unaccountedOldChild required os
    ++ missing missingTargetChildImport (nubᵇ _==ᴺ_ ns) available
    ++ map duplicateTargetChild (nubᵇ _==ᴺ_ (repeated ns))

  codomain : Expr → Expr
  codomain (pi _ t)    = codomain t
  codomain (fun′ _ t)  = codomain t
  codomain (let′ bs t) = let′ bs (codomain t)
  codomain t           = t

  unitType : List Name → Bool
  unitType ("⊤" ∷ []) = true
  unitType ("Agda" ∷ "Builtin" ∷ "Unit" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "Base" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "Polymorphic" ∷ "⊤" ∷ []) = true
  unitType ("Data" ∷ "Unit" ∷ "Polymorphic" ∷ "Base" ∷ "⊤" ∷ []) = true
  unitType _ = false

  trivial : Expr → Bool
  trivial (set _)    = true
  trivial (def q)    = unitType (full q)
  trivial (app f _)  = trivial f  -- Includes Set ℓ and explicit level arguments to ⊤.
  trivial (let′ _ t) = trivial t
  trivial _          = false

  relation : QName → Bool
  relation q with full q
  ... | "_≡_" ∷ [] = true
  ... | "Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ [] = true
  ... | "Relation" ∷ "Binary" ∷ "PropositionalEquality" ∷ "_≡_" ∷ [] = true
  ... | "Context" ∷ "Blueprint" ∷ _ ∷ _ = true
  ... | "Context" ∷ "PolyTransport" ∷ _ ∷ _ = true
  ... | _ = false

  signatureOK : PolySquareSpec → Decl → Bool
  signatureOK s (sig _ _ t) with refsExpr t | codomain t
  ... | refs | result =
    allᵇ (λ q → elemᵇ _==ᴺ_ q refs) (oldUnits s ++ newUnits s ++ requiredRefs s)
    ∧ not (trivial result)
    ∧ (anyᵇ relation (refsExpr result) ∨ not (nullᵇ (requiredRefs s)))
  signatureOK _ _ = false

  checkProof : QName → List String → List Unit → PolySquareSpec → List PolyTransportProblem
  checkProof newMod allowed locals s with lookupUnit locals (squareUnit s)
  ... | nothing = [ missingPolySquare (squareUnit s) ]
  ... | just u =
    if not (isPostulate (udecls u))
       ∧ nullᵇ (closedImplOK allowed (code newMod [] (udecls u)))
       ∧ anyᵇ (signatureOK s) (udecls u)
    then [] else [ invalidPolySquare (squareUnit s) ]

checkPolyTransport : Code → Code → List Decl → TransportSpec → List PolyTransportProblem
checkPolyTransport old new newSpec s with withTests new newSpec
... | checked with units checked | map uname (units old ++ extUnits old)
... | locals | oldNames with map uname (locals ++ extUnits checked) | flagsOf new
... | newNames | allowed =
     (if modName old ==ᴺ oldModOf s then [] else [ wrongOldMod ])
  ++ (if modName new ==ᴺ newModOf s then [] else [ wrongNewMod ])
  ++ checkChildren (imports old) (imports checked) (childMovesOf s)
  ++ concatMap checkSquare (polySquaresOf s)
  where
    checkSquare : PolySquareSpec → List PolyTransportProblem
    checkSquare square =
         (if nullᵇ (oldUnits square) ∨ nullᵇ (newUnits square)
          then [ emptySquareEndpoints (squareUnit square) ] else [])
      ++ missing missingOldEndpoint (oldUnits square) oldNames
      ++ missing missingNewEndpoint (newUnits square) newNames
      ++ checkProof (modName new) allowed locals square

-- (poly-transport OLD NEW (CHILD*) (SQUARE*))
-- CHILD  = (keep OLD NEW) | (move (OLD*) (NEW*) (SUB*))
-- SQUARE = (square (OLD*) (NEW*) PROOF (REF*))
private
  -- Use the shared dotted QName format whenever it preserves the segments.
  -- An empty path or a literal dot inside a segment needs the segment list.
  encName : QName → SExpr
  encName q@(scopedQName path sh alts) =
    if nullᵇ path ∨ anyᵇ (λ n → anyᵇ (primCharEquality '.') (toList n)) path
    then list (sym "q" ∷ list (map str path) ∷ str sh ∷ map str alts)
    else encQ q

  decName : SExpr → Maybe QName
  decName (list (sym "q" ∷ list path ∷ str sh ∷ as)) = decodeNames path >>= λ ns → decodeNames as >>= λ alts → just (scopedQName ns sh alts)
  decName e = decodeQ e

  encNames : List QName → SExpr
  encNames qs = list (map encName qs)

  encSquare : PolySquareSpec → SExpr
  encSquare (polySquareRefs os ns proof refs) =
    list (sym "square" ∷ encNames os ∷ encNames ns ∷ encName proof ∷ encNames refs ∷ [])

encodePolyTransport : TransportSpec → SExpr
encodePolyTransport (transportSpecTree o n cs ss) =
  list (sym "poly-transport" ∷ encName o ∷ encName n ∷ list (children cs) ∷ list (map encSquare ss) ∷ [])
  where
    nested : List TransportSpec → List SExpr
    nested [] = []
    nested (s ∷ ss) = encodePolyTransport s ∷ nested ss

    children : List ChildMove → List SExpr
    children [] = []
    children (keepChild o n ∷ cs) = list (sym "keep" ∷ encName o ∷ encName n ∷ []) ∷ children cs
    children (moveChildren os ns subs ∷ cs) =
      list (sym "move" ∷ encNames os ∷ encNames ns ∷ list (nested subs) ∷ []) ∷ children cs

private
  decodeItems : {A : Set} → (SExpr → Maybe A) → List SExpr → Maybe (List A)
  decodeItems read [] = just []
  decodeItems read (x ∷ xs) = zipWith _∷_ (read x) (decodeItems read xs)

  decNames : SExpr → Maybe (List QName)
  decNames (list xs) = decodeItems decName xs
  decNames _ = nothing

  decSquare : SExpr → Maybe PolySquareSpec
  decSquare (list (sym "square" ∷ os ∷ ns ∷ proof ∷ refs ∷ [])) =
    decNames os >>= λ os′ → decNames ns >>= λ ns′ → decName proof >>= λ proof′ →
    decNames refs >>= λ refs′ → just (polySquareRefs os′ ns′ proof′ refs′)
  decSquare _ = nothing

decodePolyTransport : SExpr → Maybe TransportSpec
decodePolyTransport (list (sym "poly-transport" ∷ o ∷ n ∷ list cs ∷ list ss ∷ [])) =
  decName o >>= λ o′ → decName n >>= λ n′ →
  zipWith (transportSpecTree o′ n′) (children cs) (decodeItems decSquare ss)
  where
    nested : List SExpr → Maybe (List TransportSpec)
    nested [] = just []
    nested (s ∷ ss) = zipWith _∷_ (decodePolyTransport s) (nested ss)

    children : List SExpr → Maybe (List ChildMove)
    children [] = just []
    children (list (sym "keep" ∷ o ∷ n ∷ []) ∷ cs) =
      zipWith _∷_ (zipWith keepChild (decName o) (decName n)) (children cs)
    children (list (sym "move" ∷ os ∷ ns ∷ list subs ∷ []) ∷ cs) =
      decNames os >>= λ os′ → decNames ns >>= λ ns′ → nested subs >>= λ subs′ →
      children cs >>= λ rest → just (moveChildren os′ ns′ subs′ ∷ rest)
    children _ = nothing
decodePolyTransport _ = nothing

parsePolyTransport : String → Maybe TransportSpec
parsePolyTransport txt = parseSExpr txt >>= decodePolyTransport

private
  eqNames : List QName → List QName → Bool
  eqNames = eqList _==ᴺ_

  eqSquare : PolySquareSpec → PolySquareSpec → Bool
  eqSquare (polySquareRefs os ns p rs) (polySquareRefs os′ ns′ p′ rs′) =
    eqNames os os′ ∧ eqNames ns ns′ ∧ p ==ᴺ p′ ∧ eqNames rs rs′

eqTransportSpec : TransportSpec → TransportSpec → Bool
eqTransportSpec (transportSpecTree o n cs ss) (transportSpecTree o′ n′ cs′ ss′) =
  o ==ᴺ o′ ∧ n ==ᴺ n′ ∧ children cs cs′ ∧ eqList eqSquare ss ss′
  where
    nested : List TransportSpec → List TransportSpec → Bool
    nested [] [] = true
    nested (s ∷ ss) (s′ ∷ ss′) = eqTransportSpec s s′ ∧ nested ss ss′
    nested _ _ = false

    children : List ChildMove → List ChildMove → Bool
    children [] [] = true
    children (keepChild o n ∷ cs) (keepChild o′ n′ ∷ cs′) =
      o ==ᴺ o′ ∧ n ==ᴺ n′ ∧ children cs cs′
    children (moveChildren os ns subs ∷ cs) (moveChildren os′ ns′ subs′ ∷ cs′) =
      eqNames os os′ ∧ eqNames ns ns′ ∧ nested subs subs′ ∧ children cs cs′
    children _ _ = false

private
  namedProblem : String → QName → String
  namedProblem tag q = showSExpr (list (sym tag ∷ encName q ∷ []))

showPolyTransportProblem : PolyTransportProblem → String
showPolyTransportProblem wrongOldMod = "(wrongOldMod)"
showPolyTransportProblem wrongNewMod = "(wrongNewMod)"
showPolyTransportProblem (unaccountedOldChild q) = namedProblem "unaccountedOldChild" q
showPolyTransportProblem (missingTargetChildImport q) = namedProblem "missingTargetChildImport" q
showPolyTransportProblem (duplicateTargetChild q) = namedProblem "duplicateTargetChild" q
showPolyTransportProblem (emptySquareEndpoints q) = namedProblem "emptySquareEndpoints" q
showPolyTransportProblem (missingOldEndpoint q) = namedProblem "missingOldEndpoint" q
showPolyTransportProblem (missingNewEndpoint q) = namedProblem "missingNewEndpoint" q
showPolyTransportProblem (missingPolySquare q) = namedProblem "missingPolySquare" q
showPolyTransportProblem (invalidPolySquare q) = namedProblem "invalidPolySquare" q
