module Code.Countermodel where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; [_]; map; concatMap; foldl)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; intersperse)

open import Code
open import Code.Countermodel.Wire using (countermodelWire)
import Code.Encode as Encode
import Code.Namespace as NS
import Code.Parse as Parse
open import Code.SExpr using (SExpr; list; sym)

countermodelMod : QName
countermodelMod = mkQ ("Countermodel" ∷ [])

bridgeMod : QName
bridgeMod = mkQ ("CountermodelCheck" ∷ [])

bundleTypePath : List Name
bundleTypePath = "Countermodel" ∷ "CountermodelBundle" ∷ []

verifiedClaimPath : List Name
verifiedClaimPath = "CountermodelCheck" ∷ "VerifiedClaim" ∷ []

countermodelLib : Code
countermodelLib = maybe′ (λ c → c) (code countermodelMod [] []) (Parse.parse countermodelWire)

private
  qual : List Name → QName
  qual path = qn path (intersperse "." path)

  usingNames : List Name → Directive
  usingNames ns = directive (just ns) [] [] false

  applyVis : Expr → List Expr → Expr
  applyVis = foldl (λ f a → app f (vis a))

  forbiddenModelPrefix : List Name → Bool
  forbiddenModelPrefix p =
    anyᵇ (λ bad → isPrefix bad p)
      (("Agda" ∷ "Builtin" ∷ "String" ∷ [])
       ∷ ("Agda" ∷ "Builtin" ∷ "Float" ∷ [])
       ∷ ("Agda" ∷ "Builtin" ∷ "Word" ∷ [])
       ∷ ("Data" ∷ "String" ∷ [])
       ∷ ("Data" ∷ "Float" ∷ [])
       ∷ ("Data" ∷ "Word" ∷ [])
       ∷ ("Context" ∷ [])
       ∷ [])

  forbiddenModelExact : List Name → Bool
  forbiddenModelExact p =
    eqList _==ˢ_ p ("Data" ∷ "Nat" ∷ "Show" ∷ "show" ∷ [])
    ∨ eqList _==ˢ_ p ("Agda" ∷ "Builtin" ∷ "Char" ∷ "primCharEquality" ∷ [])

  cleanStdModule : QName → Bool
  cleanStdModule q = safeQName q ∧ not (forbiddenModelPrefix (full q)) ∧ not (forbiddenModelExact (full q))
    ∧ anyᵇ (λ p → isPrefix p (full q))
        (("Agda" ∷ "Builtin" ∷ []) ∷ ("Data" ∷ []) ∷ ("Relation" ∷ [])
         ∷ ("Function" ∷ []) ∷ ("Level" ∷ []) ∷ [])

  permittedModelImport : QName → Bool
  permittedModelImport q = (q ==ᴺ countermodelMod) ∨ cleanStdModule q

  permittedModelRef : QName → QName → Bool
  permittedModelRef self q = safeQName q
    ∧ not (forbiddenModelPrefix (full q))
    ∧ not (forbiddenModelExact (full q))
    ∧ (isPrefix (full self) (full q) ∨ isPrefix (full countermodelMod) (full q) ∨ cleanStdModule q)

  mutual
    hasStrLitSExpr : SExpr → Bool
    hasStrLitSExpr (list (sym "lit" ∷ list (sym "str" ∷ _) ∷ [])) = true
    hasStrLitSExpr (list xs) = hasStrLitList xs
    hasStrLitSExpr _ = false

    hasStrLitList : List SExpr → Bool
    hasStrLitList [] = false
    hasStrLitList (x ∷ xs) = hasStrLitSExpr x ∨ hasStrLitList xs

  validModelModName : QName → Bool
  validModelModName m = not (nullParamsLike (full m))
    ∧ allᵇ NS.validSegment (full m)
    ∧ not (NS.isMetaModule m)
    ∧ not (NS.isPreTaskContext m)
    ∧ not (m ==ᴺ countermodelMod)
    ∧ not (m ==ᴺ bridgeMod)
    ∧ not (isPrefix (full m) bundleTypePath)
    ∧ not (isPrefix (full m) verifiedClaimPath)
    where
      nullParamsLike : List Name → Bool
      nullParamsLike [] = true
      nullParamsLike _ = false

  topLevelDecl : Decl → Bool
  topLevelDecl (module′ _ _ _) = false
  topLevelDecl _ = true

  bundleSigName : Decl → Maybe Name
  bundleSigName (sig m n (def (scopedQName path _ []))) =
    if not (isPrivate m) ∧ not (n ==ˢ "_") ∧ eqList _==ˢ_ path bundleTypePath
    then just n else nothing
  bundleSigName _ = nothing

  unitBundleName : Unit → Maybe Name
  unitBundleName u = if isPostulate (udecls u) then nothing else findSig (udecls u)
    where
      findSig : List Decl → Maybe Name
      findSig [] = nothing
      findSig (d ∷ ds) with bundleSigName d
      ... | just n = just n
      ... | nothing = findSig ds

firstBundleUnit : Code → Maybe Name
firstBundleUnit c with params c
... | _ ∷ _ = nothing
... | [] = go (unitsIn (full (modName c)) (filterᵇ topLevelDecl (decls c)))
  where
    go : List Unit → Maybe Name
    go [] = nothing
    go (u ∷ us) with unitBundleName u
    ... | just n = just n
    ... | nothing = go us

validCountermodel : List String → Code → List RefuteProblem
validCountermodel allowed m =
  (if validModelModName (modName m) then [] else unauthorizedImport (modName m) ∷ [])
  ++ (if elemᵇ _==ˢ_ "--safe" (flagsOf m) ∧ not (hasStrLitSExpr (Encode.encodeCode m))
      then [] else invalidImplementation flagEnvelopeViolation ∷ [])
  ++ map invalidImplementation (closedImplOK ("--safe" ∷ allowed) m)
  ++ map unauthorizedImport (filterᵇ (λ q → not (permittedModelImport q)) (NS.moduleImports m))
  ++ concatMap checkRef (refsDecls (decls m))
  ++ maybe′ (λ _ → []) (missingCountermodelBundle ∷ []) (firstBundleUnit m)
  where
    checkRef : QName → List RefuteProblem
    checkRef q = if permittedModelRef (modName m) q then [] else unauthorizedImport q ∷ []

countermodelBridge : QName → Name → Code
countermodelBridge modelMod bundleName =
  code bridgeMod []
    ( pragma "OPTIONS --safe"
    ∷ import′ (qual (full modelMod)) false everything []
    ∷ import′ (qual ("Agda" ∷ "Builtin" ∷ "Char" ∷ [])) true
        (usingNames ("Char" ∷ "primCharToNat" ∷ "primNatToChar" ∷ "primCharEquality" ∷ [])) []
    ∷ import′ (qual ("Agda" ∷ "Builtin" ∷ "Char" ∷ "Properties" ∷ [])) true
        (usingNames ("primCharToNatInjective" ∷ [])) []
    ∷ import′ (qual ("Agda" ∷ "Builtin" ∷ "String" ∷ [])) true
        (usingNames ("String" ∷ "primStringToList" ∷ "primStringFromList" ∷ "primStringAppend" ∷ "primStringEquality" ∷ [])) []
    ∷ import′ (qual ("Agda" ∷ "Builtin" ∷ "String" ∷ "Properties" ∷ [])) true
        (usingNames ("primStringToListInjective" ∷ "primStringFromListInjective" ∷ [])) []
    ∷ import′ (qual ("Countermodel" ∷ [])) true
        (usingNames ("StringAlg" ∷ "stringAlg" ∷ "CharAlg" ∷ "charAlg" ∷ "CountermodelBundle" ∷ "stringCountermodel" ∷ "charCountermodel" ∷ [])) []
    ∷ sig plain "realStringAlg" (def (mkQ ("Countermodel" ∷ "StringAlg" ∷ [])))
    ∷ fun plain "realStringAlg"
        (clause (head (mkQ ("CountermodelCheck" ∷ "realStringAlg" ∷ [])) [])
          (rhs (applyVis (con (mkQ ("Countermodel" ∷ "stringAlg" ∷ [])))
            ( def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "String" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "primStringToList" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "primStringFromList" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "primStringAppend" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "primStringEquality" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "Properties" ∷ "primStringToListInjective" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "String" ∷ "Properties" ∷ "primStringFromListInjective" ∷ []))
            ∷ []))) [] ∷ [])
    ∷ sig plain "realCharAlg" (def (mkQ ("Countermodel" ∷ "CharAlg" ∷ [])))
    ∷ fun plain "realCharAlg"
        (clause (head (mkQ ("CountermodelCheck" ∷ "realCharAlg" ∷ [])) [])
          (rhs (applyVis (con (mkQ ("Countermodel" ∷ "charAlg" ∷ [])))
            ( def (mkQ ("Agda" ∷ "Builtin" ∷ "Char" ∷ "Char" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "Char" ∷ "primCharToNat" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "Char" ∷ "primNatToChar" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "Char" ∷ "primCharEquality" ∷ []))
            ∷ def (mkQ ("Agda" ∷ "Builtin" ∷ "Char" ∷ "Properties" ∷ "primCharToNatInjective" ∷ []))
            ∷ []))) [] ∷ [])
    ∷ sig plain "RealTarget" (fun′ (vis (def (mkQ bundleTypePath))) (set 0))
    ∷ fun plain "RealTarget"
        ( clause
            (head (mkQ ("CountermodelCheck" ∷ "RealTarget" ∷ []))
              (vis (conP (mkQ ("Countermodel" ∷ "CountermodelBundle" ∷ "stringCountermodel" ∷ []))
                     (vis (varP "Claim") ∷ vis wildP ∷ vis wildP ∷ [])) ∷ []))
            (rhs (app (var "Claim") (vis (def (mkQ ("CountermodelCheck" ∷ "realStringAlg" ∷ [])))))) []
        ∷ clause
            (head (mkQ ("CountermodelCheck" ∷ "RealTarget" ∷ []))
              (vis (conP (mkQ ("Countermodel" ∷ "CountermodelBundle" ∷ "charCountermodel" ∷ []))
                     (vis (varP "Claim") ∷ vis wildP ∷ vis wildP ∷ [])) ∷ []))
            (rhs (app (var "Claim") (vis (def (mkQ ("CountermodelCheck" ∷ "realCharAlg" ∷ [])))))) []
        ∷ [])
    ∷ recSig plain "VerifiedClaim" [] (set 0)
    ∷ recDef plain "VerifiedClaim" [] (recDir false (just "verifiedClaim"))
        (("derive" , app (def (mkQ ("CountermodelCheck" ∷ "RealTarget" ∷ [])))
                         (vis (def (qual (full modelMod ++ (bundleName ∷ [])))))) ∷ [])
    ∷ [])

usesCountermodelBridge : Code → Bool
usesCountermodelBridge c = elemᵇ _==ᴺ_ bridgeMod (NS.moduleImports c)

validCountermodelRefute : QName → List QName → QName → List String → Code → List RefuteProblem
validCountermodelRefute specMod baseMods modelMod allowed c =
  witnessNamespaceProblems specMod c
  ++ (if (modName c ==ᴺ modelMod) ∨ (modName c ==ᴺ countermodelMod) ∨ (modName c ==ᴺ bridgeMod)
         ∨ elemᵇ _==ᴺ_ (modName c) baseMods
      then unauthorizedImport (modName c) ∷ [] else [])
  ++ (if elemᵇ _==ᴺ_ bridgeMod imported then [] else unauthorizedImport bridgeMod ∷ [])
  ++ checkWitnessIn hasVerifiedClaim missingCountermodelRefute permitted imported allowed c
  where
    imported = NS.moduleImports c
    permitted = specMod ∷ bridgeMod ∷ countermodelMod ∷ modelMod ∷ baseMods
    hasVerifiedClaim : Name → Expr → Bool
    hasVerifiedClaim name (def (scopedQName path _ [])) =
      not (name ==ˢ "_") ∧ eqList _==ˢ_ path verifiedClaimPath
    hasVerifiedClaim _ _ = false
