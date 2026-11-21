module Code.TranscodeIR where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; foldr; foldl; length; upTo; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred)
import Data.Nat.Show as Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; words) renaming (_++_ to _++ˢ_)
import Data.List.Properties as Listₚ
import Data.String.Properties as Stringₚ
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Code
import Context.TranscodeCategory as C
open C using (DeclSort; baseTypeDecl; pureSigHelperDecl; sweetBodyDecl; exoBodyDecl; boundaryHoleDecl;
              EvalColor; Ghost; Thunked; StrictVal)

data SurfaceOrigin : Set where
  authoredSource synthesizedFromCode : String → SurfaceOrigin

surfaceText : SurfaceOrigin → String
surfaceText (authoredSource s) = s
surfaceText (synthesizedFromCode s) = s

record AmbQHint : Set where
  constructor ambQ
  field primaryQ : QName
        candidateQs : List QName

-- Fix the scope-checking decoder for the whole family of points. Both choices
-- of surface origin carry the same roundtrip obligation.
record PreTCModulePoint (dump : String → Maybe Code) : Set where
  field irCode : Code
        surfaceView : SurfaceOrigin
        ambTable : List AmbQHint
        decoded : Code
        surfaceDecoded : dump (surfaceText surfaceView) ≡ just decoded
        canonicalRoundtrip : eqCode decoded irCode ≡ true

-- A surface submission obtains its IR and its roundtrip evidence from the
-- same scope-check result. Callers with an existing IR also check canonical
-- equality before attaching an authored or synthesized presentation.
checkedSurface : (dump : String → Maybe Code) → SurfaceOrigin → Code → List AmbQHint →
                 Maybe (PreTCModulePoint dump)
checkedSurface dump view ir hints with dump (surfaceText view) in result
... | nothing = nothing
... | just c with eqCode c ir in same
...   | false = nothing
...   | true = just (record { irCode = ir ; surfaceView = view ; ambTable = hints ; decoded = c
                            ; surfaceDecoded = result ; canonicalRoundtrip = same })

-- The display spelling is evidence for rendering only. All keys supplied to
-- the category are in mkQ normal form, including imported seed aliases.
canonical : QName → QName
canonical = mkQ ∘ full
  where open import Function using (_∘_)

qDec : (q r : QName) → Dec (q ≡ r)
qDec (scopedQName p s as) (scopedQName q t bs) with Listₚ.≡-dec Stringₚ._≟_ p q | Stringₚ._≟_ s t | Listₚ.≡-dec Stringₚ._≟_ as bs
... | yes refl | yes refl | yes refl = yes refl
... | no ne | _ | _ = no λ { refl → ne refl }
... | _ | no ne | _ = no λ { refl → ne refl }
... | _ | _ | no ne = no λ { refl → ne refl }

module Q = C.Over {QName} qDec

-- Label each leaf once, using Code.unitsIn's anonymous declaration numbering.
-- Sections and ambient declarations remain in the source tree. This preserves
-- original declaration order and the lexical scope of projected nested units.
data Fragment : Set where
  owned : QName → Decl → Fragment
  ambient : Decl → Fragment
  imported : QName → Bool → Directive → List Fragment → Fragment
  section : QName → Name → List Bind → List Fragment → Fragment

isOptions : String → Bool
isOptions s with words s
... | "OPTIONS" ∷ _ = true
... | _ = false

indexBlock : List Name → ℕ → ℕ → List Decl → List Fragment
indexBlock path anon pos [] = []
indexBlock path anon pos (import′ q o dir iface ∷ ds) =
  imported q o dir (indexBlock (full q) 0 0 iface) ∷ indexBlock path anon (suc pos) ds
indexBlock path anon pos (module′ n bs sub ∷ ds) =
  section key n bs (indexBlock (full key) 0 0 sub) ∷ indexBlock path anon (suc pos) ds
  where key = mkQ (path ++ [ n ])
indexBlock path anon pos (d ∷ ds) = tag d ++ indexBlock path (next d) (suc pos) ds
  where
    key : Name → QName
    key x = mkQ (path ++ [ x ])
    opaqueKey = mkQ (path ++ ("" ∷ Nat.show pos ∷ []))
    anonKey : ℕ → QName
    anonKey i = key ("_#" ++ˢ Nat.show i)
    next : Decl → ℕ
    next (sig _ "_" _) = suc anon
    next _ = anon
    tag : Decl → List Fragment
    tag (variable′ vs) = map (λ { v@(n , _) → owned (key n) (variable′ [ v ]) }) vs
    tag s@(sig m "_" e) = [ owned (anonKey anon) s ]
    tag f@(fun m "_" cs) = [ owned (anonKey (pred anon)) f ]
    tag p@(pragma s) = [ (if isOptions s then ambient p else owned opaqueKey p) ]
    tag u@(unsupported _) = [ owned opaqueKey u ]
    tag x with declName x
    ... | just n = [ owned (key n) x ]
    ... | nothing = [ ambient x ]

record UnitSource : Set where
  constructor source
  field unitIR : Unit
        contextRefs : List QName
        environment : List Import
open UnitSource

-- An import with declared assumptions is a typed telescope. Its functions
-- supply signatures only, even if the supplied interface carried clauses.
headerImports : List Fragment → List Import
headerImports [] = []
headerImports (imported q o dir _ ∷ fs) = importOf q o dir [] ∷ headerImports fs
headerImports (_ ∷ fs) = headerImports fs

scopeImports : List Import → List Fragment → List Import
scopeImports inherited fs = opened fs ++ available
  where
    available = headerImports fs ++ inherited
    opened : List Fragment → List Import
    opened [] = []
    opened (ambient (open′ q dir) ∷ rest) =
      (if anyᵇ (λ i → isPrefix (full (imod i)) (full q)) available
       then [ importOf q true dir [] ] else []) ++ opened rest
    opened (_ ∷ rest) = opened rest

gather : Bool → List Import → List QName → List Fragment → List UnitSource → List UnitSource
gather iface env ctx [] acc = acc
gather iface env ctx (ambient _ ∷ fs) acc = gather iface env ctx fs acc
gather iface env ctx (imported _ _ _ sub ∷ fs) acc =
  gather true (scopeImports env sub) [] sub (gather iface env ctx fs acc)
gather iface env ctx (section _ _ bs sub ∷ fs) acc =
  gather iface (scopeImports env sub) (ctx ++ refsBinds bs) sub (gather iface env ctx fs acc)
gather true env ctx (owned q (fun _ _ _) ∷ fs) acc = gather true env ctx fs acc
gather iface env ctx (owned q d ∷ fs) acc = add (gather iface env ctx fs acc)
  where
    add : List UnitSource → List UnitSource
    add [] = [ source (unitOf q [ d ]) ctx env ]
    add (s ∷ ss) with q ==ᴺ uname (unitIR s)
    ... | true = source (unitOf q (d ∷ udecls (unitIR s))) ctx env ∷ ss
    ... | false = s ∷ add ss

-- Every signature-bearing constituent participates, including the types of
-- fields and constructors, which Code stores in recDef/dataDef.
isBody : Decl → Bool
isBody (fun _ _ _) = true
isBody _ = false

isTypeBlock : Decl → Bool
isTypeBlock (dataSig _ _ _ _) = true
isTypeBlock (dataDef _ _ _ _) = true
isTypeBlock (recSig _ _ _ _) = true
isTypeBlock (recDef _ _ _ _ _) = true
isTypeBlock _ = false

mutual
  exoticDecl : Decl → Bool
  exoticDecl (unsupported _) = true
  exoticDecl (pragma s) = not (isOptions s)
  exoticDecl (sig m _ e) = bypassMods m ∨ exoticExpr e
  exoticDecl (fun m _ cs) = bypassMods m ∨ exoticClauses cs
  exoticDecl (dataSig m _ bs e) = bypassMods m ∨ exoticBinds bs ∨ exoticExpr e
  exoticDecl (dataDef m _ _ fs) = bypassMods m ∨ exoticFields fs
  exoticDecl (recSig m _ bs e) = bypassMods m ∨ exoticBinds bs ∨ exoticExpr e
  exoticDecl (recDef m _ _ dir fs) = coind dir ∨ bypassMods m ∨ exoticFields fs
  exoticDecl (module′ _ _ ds) = exoticDecls ds
  exoticDecl _ = false

  exoticDecls : List Decl → Bool
  exoticDecls [] = false
  exoticDecls (d ∷ ds) = exoticDecl d ∨ exoticDecls ds

  exoticClauses : List Clause → Bool
  exoticClauses [] = false
  exoticClauses (clause l r ds ∷ cs) = copattern l ∨ exoticRhs r ∨ exoticDecls ds ∨ exoticClauses cs
    where
      copattern : LHS → Bool
      copattern (head _ ps) = anyᵇ (λ { (arg _ _ (projP _)) → true ; _ → false }) ps
      copattern (proj _ _ _) = true
      copattern (with′ l _ _) = copattern l

  exoticRhs : RHS → Bool
  exoticRhs (rhs e) = exoticExpr e
  exoticRhs (withRHS es cs) = exoticExprs es ∨ exoticClauses cs
  exoticRhs (rewriteRHS es r) = exoticExprs es ∨ exoticRhs r
  exoticRhs _ = false

  exoticExpr : Expr → Bool
  exoticExpr (app f a) = exoticExpr f ∨ exoticExpr (thing a)
  exoticExpr (lam _ e) = exoticExpr e
  exoticExpr (lamT (bind _ _ t) e) = exoticExpr t ∨ exoticExpr e
  exoticExpr (lamCase cs) = exoticClauses cs
  exoticExpr (pi (bind _ _ t) e) = exoticExpr t ∨ exoticExpr e
  exoticExpr (fun′ a e) = exoticExpr (thing a) ∨ exoticExpr e
  exoticExpr (let′ bs e) = exoticLets bs ∨ exoticExpr e
  exoticExpr (rec′ fs) = exoticFields fs
  exoticExpr (recUpd v fs) = exoticExpr v ∨ exoticFields fs
  exoticExpr (dot e) = exoticExpr e
  exoticExpr _ = false

  exoticBinds : List Bind → Bool
  exoticBinds [] = false
  exoticBinds (bind _ _ t ∷ bs) = exoticExpr t ∨ exoticBinds bs

  exoticExprs : List Expr → Bool
  exoticExprs [] = false
  exoticExprs (e ∷ es) = exoticExpr e ∨ exoticExprs es

  exoticLets : List LetBind → Bool
  exoticLets [] = false
  exoticLets (letBind _ t e ∷ bs) = exoticExpr t ∨ exoticExpr e ∨ exoticLets bs
  exoticLets (letPat _ e ∷ bs) = exoticExpr e ∨ exoticLets bs

  exoticFields : List (Name × Expr) → Bool
  exoticFields [] = false
  exoticFields ((_ , e) ∷ fs) = exoticExpr e ∨ exoticFields fs

signatureRefs : UnitSource → List QName
signatureRefs s = contextRefs s ++ refsDecls (filterᵇ (λ d → not (isBody d)) (udecls (unitIR s)))

-- Scoped external names belong to the enclosing import telescope. Local
-- references with no owner stay in the dependency table for checkPoint to
-- reject. In particular a missing sibling declaration is never erased.
visibleFrom : QName → Import → Bool
visibleFrom q i = isPrefix (full (imod i)) (full q) ∨ qualified ∨
  (iopen i ∧ (renamed ∨ (selected ∧ not (anyᵇ spelled (dhiding dir)))))
  where
    name = shown (canonical q)
    spelling = shown q
    dir = idir i
    -- The scope checker may expose Agda.Builtin.Nat.Nat as ℕ.
    spelled : Name → Bool
    spelled n = (n ==ˢ spelling) ∨ (n ==ˢ name)
    qualified = setsOption (shown (imod i) ++ˢ ".") spelling
    renamed = anyᵇ (λ { (old , new) → new ==ˢ spelling }) (drenaming dir)
    selected : Bool
    selected with dusing dir
    ... | just ns = anyᵇ spelled ns
    -- Scope checking resolves unqualified re-exports from open imports.
    ... | nothing = true

parentPath : List Name → List Name
parentPath [] = []
parentPath (_ ∷ []) = []
parentPath (x ∷ y ∷ ns) = x ∷ parentPath (y ∷ ns)

headQName : LHS → QName
headQName (head q _) = q
headQName (proj _ l _) = headQName l
headQName (with′ l _ _) = headQName l

-- Only declared members project to an owner. Prefix matching would allow a
-- fabricated M.f.Missing to masquerade as a dependency on f.
members : QName → Decl → List QName
members q (dataDef _ _ _ cs) = map (λ f → mkQ (full q ++ [ proj₁ f ])) cs
members q (recDef _ _ _ dir fs) = ctor (constr dir) ++ map (λ f → mkQ (full q ++ [ proj₁ f ])) fs
  where
    ctor : Maybe Name → List QName
    ctor nothing = []
    ctor (just n) = [ mkQ (parentPath (full q) ++ [ n ]) ]
members _ _ = []

mutual
  localDeclarations : List Name → List Decl → List QName
  localDeclarations _ [] = []
  localDeclarations path (module′ n _ inner ∷ ds) =
    localDeclarations (path ++ [ n ]) inner ++ localDeclarations path ds
  localDeclarations path (fun _ n cs ∷ ds) =
    mkQ (path ++ [ n ]) ∷ definedClauses cs ++ localDeclarations path ds
  localDeclarations path (d ∷ ds) with declName d
  ... | just n = let q = mkQ (path ++ [ n ]) in q ∷ members q d ++ localDeclarations path ds
  ... | nothing = localDeclarations path ds

  definedClauses : List Clause → List QName
  definedClauses [] = []
  definedClauses (clause l r wh ∷ cs) =
    let q = headQName l
        path = parentPath (full q)
    in q ∷ localDeclarations (path ++ [ "_" ]) wh ++ namedWhere path wh ++ definedBranches r ++ definedClauses cs

  namedWhere : List Name → List Decl → List QName
  namedWhere path (module′ n _ inner ∷ []) = localDeclarations (path ++ [ n ]) inner
  namedWhere _ _ = []

  definedBranches : RHS → List QName
  definedBranches (rewriteRHS _ r) = definedBranches r
  definedBranches (withRHS _ cs) = definedClauses cs
  definedBranches _ = []

ownsSymbol : Unit → QName → Bool
ownsSymbol u q = (uname u ==ᴺ q) ∨ anyᵇ owns (udecls u)
  where
    owns : Decl → Bool
    owns (fun _ _ cs) = elemᵇ _==ᴺ_ q (definedClauses cs)
    owns d = elemᵇ _==ᴺ_ q (members (uname u) d)

resolveOwner : List Unit → QName → Maybe QName
resolveOwner [] _ = nothing
resolveOwner (u ∷ us) q = if ownsSymbol u q then just (uname u) else resolveOwner us q

localRefs : Code → List Unit → List Import → List QName → List QName
localRefs c us env = nubᵇ _==ᴺ_ ∘ concatMap local
  where
    open import Function using (_∘_)
    local : QName → List QName
    local q with resolveOwner us q
    ... | just owner = [ canonical owner ]
    ... | nothing = if not (isPrefix (full (modName c)) (full q)) ∧
                       (anyᵇ (visibleFrom q) env ∨ isPrefix ("Agda" ∷ "Primitive" ∷ []) (full q))
                    then [] else [ canonical q ]

at : ∀ {A : Set} → ℕ → List A → Maybe A
at _ [] = nothing
at zero (x ∷ _) = just x
at (suc n) (_ ∷ xs) = at n xs

mutual
  patternVars : Pat → List Name
  patternVars (varP n) = [ n ]
  patternVars (conP _ ps) = argVars ps
  patternVars (asP n p) = n ∷ patternVars p
  patternVars (recP fs) = fieldVars fs
  patternVars _ = []
  argVars : List (Arg Pat) → List Name
  argVars [] = []
  argVars (arg _ _ p ∷ ps) = patternVars p ++ argVars ps
  fieldVars : List (Name × Pat) → List Name
  fieldVars [] = []
  fieldVars ((_ , p) ∷ fs) = patternVars p ++ fieldVars fs

strictSubterms : Pat → List Name
strictSubterms (conP _ ps) = argVars ps
strictSubterms (asP _ p) = strictSubterms p
strictSubterms _ = []

visibleArgs : ∀ {A : Set} → List (Arg A) → List (Arg A)
visibleArgs = filterᵇ (λ a → eqHiding (hid a) visible)

-- Inspect every recursive call at the same visible argument position. The
-- accumulator is the application spine, from left to right at its head.
-- Binders can shadow a decreasing pattern variable.
callsDecrease : QName → ℕ → List Name → List Expr → Expr → Bool
callsDecrease self k smaller args (app f a) =
  callsDecrease self k smaller [] (thing a) ∧ callsDecrease self k smaller args′ f
  where args′ = if eqHiding (hid a) visible then thing a ∷ args else args
callsDecrease self k smaller args (def q) = not (q ==ᴺ self) ∨ proper (at k args)
  where
    proper : Maybe Expr → Bool
    proper (just (var v)) = elemᵇ _==ˢ_ v smaller
    proper _ = false
callsDecrease self k smaller _ (lam a e) =
  callsDecrease self k (filterᵇ (λ x → not (x ==ˢ thing a)) smaller) [] e
callsDecrease self k smaller _ (lamT (bind _ ns t) e) =
  callsDecrease self k smaller [] t ∧ callsDecrease self k (filterᵇ (λ x → not (elemᵇ _==ˢ_ x ns)) smaller) [] e
callsDecrease self k smaller _ (dot e) = callsDecrease self k smaller [] e
callsDecrease self k smaller _ e = not (elemᵇ _==ᴺ_ self (refsExpr e))

clauseDecreases : QName → ℕ → Clause → Bool
clauseDecreases q k cl@(clause (head _ ps) (rhs e) ds) =
  not (elemᵇ _==ᴺ_ q (refsDecls ds)) ∧ checkCall (at k (visibleArgs ps))
  where
    checkCall : Maybe (Arg Pat) → Bool
    checkCall (just a) = callsDecrease q k (strictSubterms (thing a)) [] e
    checkCall nothing = not (elemᵇ _==ᴺ_ q (refsExpr e))
clauseDecreases q _ cl = not (elemᵇ _==ᴺ_ q (refsClause cl))

complexRecursion : QName → Decl → Bool
complexRecursion q (fun _ _ cs@(clause (head _ ps) _ _ ∷ _)) =
  elemᵇ _==ᴺ_ q (refsClauses cs) ∧ not (anyᵇ (λ k → allᵇ (clauseDecreases q k) cs) (upTo (length (visibleArgs ps))))
complexRecursion q (fun _ _ cs) = elemᵇ _==ᴺ_ q (refsClauses cs)
complexRecursion _ _ = false

-- Multi-function recursive components need the full termination graph. A
-- self-edge alone is handled by the single structural-parameter test above.
mutualRecursion : Code → List UnitSource → List QName
mutualRecursion c table = map proj₁ (filterᵇ cyclic graph)
  where
    us = map unitIR table
    node : UnitSource → QName × List QName
    node s = uname (unitIR s) , localRefs c us (environment s)
                  (refsDecls (filterᵇ isBody (udecls (unitIR s))))
    graph = map node table
    walk : ℕ → List QName → List QName
    walk zero qs = qs
    walk (suc k) qs with nubᵇ _==ᴺ_ (qs ++ concatMap proj₂ (filterᵇ (λ g → elemᵇ _==ᴺ_ (proj₁ g) qs) graph))
    ... | more = if eqList _==ᴺ_ qs more then qs else walk k more
    cyclic : QName × List QName → Bool
    cyclic (q , adj) = elemᵇ _==ᴺ_ q (walk (length table) (filterᵇ (λ n → not (q ==ᴺ n)) adj))

exoticUnit : List QName → Unit → Bool
exoticUnit cycles u = exoticDecls (udecls u) ∨ elemᵇ _==ᴺ_ (uname u) cycles ∨
                      anyᵇ (complexRecursion (uname u)) (udecls u)

candidateHelper : List QName → Unit → Bool
candidateHelper cycles u = anyᵇ isBody (udecls u) ∧ not (exoticUnit cycles u)

-- A helper's implementation may itself compute through another pure
-- function. Promote those callees transitively before assigning body colors.
helperNames : Code → List UnitSource → List QName → List QName → List QName
helperNames c table cycles extra = grow (length table) seeds
  where
    us = map unitIR table
    seeds = nubᵇ _==ᴺ_ (extra ++ concatMap (λ s → localRefs c us (environment s) (signatureRefs s)) table)
    step : List QName → List QName
    step ks = nubᵇ _==ᴺ_ (ks ++ concatMap descend table)
      where
        descend : UnitSource → List QName
        descend s = let u = unitIR s in if candidateHelper cycles u ∧ elemᵇ _==ᴺ_ (uname u) ks
                    then localRefs c us (environment s) (refsDecls (udecls u)) else []
    grow : ℕ → List QName → List QName
    grow zero ks = ks
    grow (suc n) ks with step ks
    ... | ks′ = if eqList _==ᴺ_ ks ks′ then ks else grow n ks′

classify : List QName → List QName → Unit → DeclSort
classify helpers cycles u with exoticUnit cycles u | anyᵇ isTypeBlock (udecls u) | anyᵇ isBody (udecls u)
... | true | _ | _ = exoBodyDecl
... | false | true | _ = baseTypeDecl
... | false | false | false = boundaryHoleDecl
... | false | false | true = if elemᵇ _==ᴺ_ (uname u) helpers then pureSigHelperDecl else sweetBodyDecl

fragments : Code → List Fragment
fragments c = indexBlock (full (modName c)) 0 0 (decls c)

unitSources : Code → List Fragment → List UnitSource
unitSources c fs = gather false (scopeImports [] fs) (refsBinds (params c)) fs []

classifyCodeUnit : Code → Unit → DeclSort
classifyCodeUnit c = classify (helperNames c table cycles []) cycles
  where table = unitSources c (fragments c)
        cycles = mutualRecursion c table

lowerTableWith : Code → List UnitSource → List QName → Maybe (C.CodePoint QName)
lowerTableWith c table extra = if allᵇ (λ q → elemᵇ _==ᴺ_ q (map uname us)) paramDeps
                     then Q.checkPoint (map entry table) else nothing
  where
    us = map unitIR table
    paramDeps = localRefs c us (scopeImports [] (fragments c)) (refsBinds (params c))
    cycles = mutualRecursion c table
    helpers = helperNames c table cycles extra
    entry : UnitSource → C.DeclEntry QName
    entry s = C.decl (canonical (uname u)) (classify helpers cycles u)
                (localRefs c us (environment s) (signatureRefs s))
                (localRefs c us (environment s) (refsDecls (filterᵇ isBody (udecls u))))
      where u = unitIR s

lowerTable : Code → List UnitSource → Maybe (C.CodePoint QName)
lowerTable c table = lowerTableWith c table []

lowerCode : Code → Maybe (C.CodePoint QName)
lowerCode c = lowerTable c (unitSources c (fragments c))

lookupSort : QName → List (C.DeclEntry QName) → Maybe DeclSort
lookupSort q [] = nothing
lookupSort q (d ∷ ds) = if q ==ᴺ C.entrySym d then just (C.entrySort d) else lookupSort q ds


blockParams : List Decl → List Bind
blockParams (recSig _ _ bs _ ∷ _) = bs
blockParams (dataSig _ _ bs _ ∷ _) = bs
blockParams (_ ∷ ds) = blockParams ds
blockParams [] = []

-- Parameters of the opaque type constructor keep their original visibility.
-- At a projection/constructor they are implicit and inferable from its type.
implicitBind : Bind → Bind
implicitBind (bind visible ns t) = bind hidden ns t
implicitBind b = b

applyParams : QName → List Bind → Expr
applyParams q bs = foldl app (def q) (concatMap args bs)
  where
    args : Bind → List (Arg Expr)
    args (bind h ns _) = map (λ n → arg h nothing (var n)) ns

signatureMods : Mods → Mods
signatureMods (mods p i a _) = mods p i a check

-- A bodyless sig is the Code representation of a typed assumption. In the
-- record namespace, the receiver is a section parameter: dependent later
-- field types can refer to earlier projections in their original scope.
shellDecl : QName → List Bind → Decl → List Decl
shellDecl _ _ (sig m n t) = [ sig (signatureMods m) n t ]
shellDecl _ _ (dataSig m n bs sort) = [ sig (signatureMods m) n (foldr pi sort bs) ]
shellDecl _ _ (recSig m n bs sort) = [ sig (signatureMods m) n (foldr pi sort bs) ]
shellDecl q bs (dataDef m n _ cs) =
  [ module′ n (map implicitBind bs) (map (λ { (x , t) → sig (signatureMods m) x t }) cs) ]
shellDecl q bs (recDef m n _ dir fs) = projections ∷ constructorSig (constr dir)
  where
    recTy = applyParams q bs
    tel = map implicitBind bs
    projections = module′ n (tel ++ [ bind visible [ "_" ] recTy ])
                            (map (λ { (x , t) → sig (signatureMods m) x t }) fs)
    constructorSig : Maybe Name → List Decl
    constructorSig nothing = []
    constructorSig (just x) = [ sig (signatureMods m) x (foldr pi recTy (tel ++ fields)) ]
      where fields = map (λ { (f , t) → bind visible [ f ] t }) fs
shellDecl _ _ v@(variable′ _) = [ v ]
shellDecl _ _ _ = []

materialize : Code → List Unit → List Fragment → C.CodePoint QName → Code
materialize c us fs p = code (modName c) (params c) (block false (full (modName c)) fs)
  where
    ds = C.entries p
    hasPrefix : List Name → Bool
    hasPrefix path = anyᵇ (λ d → isPrefix path (full (C.entrySym d))) ds
    isLocal : List Name → Bool
    isLocal path = anyᵇ (λ u → isPrefix path (full (uname u))) us
    -- Drop imports used only by clauses which this projection discarded.
    -- A scoped re-export may have a different canonical owner from its import.
    keptRefs : Unit → List QName
    keptRefs u with lookupSort (uname u) ds
    ... | nothing = []
    ... | just boundaryHoleDecl = refsDecls (filterᵇ (λ d → not (isBody d)) (udecls u))
    ... | just _ = refsDecls (udecls u)
    sourceContexts : List UnitSource → List QName
    sourceContexts [] = []
    sourceContexts (s ∷ rest) =
      (if hasPrefix (full (uname (unitIR s))) then contextRefs s else []) ++ sourceContexts rest
    externalRefs = filterᵇ (λ q → not (isPrefix (full (modName c)) (full q)))
      (refsBinds (params c) ++ sourceContexts (unitSources c fs) ++ concatMap keptRefs us)
    exposesRef : QName → Bool → Directive → Bool
    exposesRef q o dir = anyᵇ (λ ref → visibleFrom ref (importOf q o dir [])) externalRefs
    opens : List Fragment → List QName
    opens [] = []
    opens (ambient (open′ q dir) ∷ rest) = (if exposesRef q true dir then [ q ] else []) ++ opens rest
    opens (section q _ _ inner ∷ rest) = (if hasPrefix (full q) then opens inner else []) ++ opens rest
    opens (_ ∷ rest) = opens rest
    neededOpens = opens fs
    keepImport : QName → Bool → Directive → Bool
    keepImport q o dir = exposesRef q o dir ∨ anyᵇ (λ n → isPrefix (full q) (full n)) neededOpens
    visibleOpen : List Name → QName → Directive → Bool
    visibleOpen path q dir = if isLocal (path ++ full q) then hasPrefix (path ++ full q)
                         else if isPrefix (full (modName c)) (full q) then hasPrefix (full q)
                         else exposesRef q true dir
    sigBinds : QName → List Bind
    sigBinds q with lookupUnit us q
    ... | nothing = []
    ... | just u = blockParams (udecls u)
    emit : Bool → QName → Decl → List Decl
    emit true q (fun _ _ _) = []
    emit iface q d with lookupSort q ds
    ... | nothing = []
    ... | just boundaryHoleDecl = shellDecl q (sigBinds q) d
    ... | just _ = [ d ]
    hasFixityTarget : List Name → Name → Bool
    hasFixityTarget path n = hasPrefix (path ++ [ n ]) ∨ anyᵇ member us
      where
        exports : Decl → Bool
        exports (dataDef _ _ _ cs) = elemᵇ _==ˢ_ n (map proj₁ cs)
        exports (recDef _ _ _ (recDir _ (just k)) fs) = (n ==ˢ k) ∨ elemᵇ _==ˢ_ n (map proj₁ fs)
        exports (recDef _ _ _ _ fs) = elemᵇ _==ˢ_ n (map proj₁ fs)
        exports _ = false
        member : Unit → Bool
        member u = isPrefix path (full (uname u)) ∧ hasPrefix (full (uname u)) ∧ anyᵇ exports (udecls u)
    block : Bool → List Name → List Fragment → List Decl
    block iface path [] = []
    block iface path (owned q d ∷ rest) = emit iface q d ++ block iface path rest
    block iface path (imported q o dir sub ∷ rest) =
      (if keepImport q o dir then [ import′ q o dir (block true (full q) sub) ] else []) ++ block iface path rest
    block iface path (section q n bs sub ∷ rest) =
      (if hasPrefix (full q) then [ module′ n bs (block iface (full q) sub) ] else []) ++ block iface path rest
    block iface path (ambient d ∷ rest) = header d ++ block iface path rest
      where
        header : Decl → List Decl
        header (open′ q dir) = if visibleOpen path q dir then [ d ] else []
        header (fixity _ _ n) = if hasFixityTarget path n then [ d ] else []
        header _ = [ d ]

splitCodePushout : Code → Maybe (Code × Code × Code)
splitCodePushout c with fragments c
... | fs with unitSources c fs
...   | table with lowerTable c table
...     | nothing = nothing
...     | just p with Q.pushoutSplit p
...       | base , fast , slow =
  let lift = materialize c (map unitIR table) fs in just (lift base , lift fast , lift slow)

projectCodeUpstreamShell : Code → List QName → Maybe Code
projectCodeUpstreamShell c needed with fragments c
... | fs with unitSources c fs
...   | table with lowerTable c table
...     | nothing = nothing
...     | just p =
  let us = map unitIR table
      owners = localRefs c us [] needed
  in just (materialize c us fs (Q.projectUpstreamShell p owners))

-- A downstream signature may be the only place that unfolds an upstream h.
-- Supply signature and body roots separately before assigning source sorts.
-- Ordinary proof dependencies seen only in residual clauses remain opaque.
projectCodeUpstreamFor : Code → Code → Maybe Code
projectCodeUpstreamFor up residual with fragments up
... | fs with unitSources up fs
...   | table = shell (lowerTableWith up table typeRoots)
  where
    us = map unitIR table
    localUnit : UnitSource → Bool
    localUnit s = isPrefix (full (modName residual)) (full (uname (unitIR s)))
    consumers = filterᵇ localUnit (unitSources residual (fragments residual))
    sigUses = refsBinds (params residual) ++ concatMap signatureRefs consumers
    typeRoots = localRefs up us [] sigUses
    roots = localRefs up us [] (sigUses ++ refsDecls (decls residual))
    shell : Maybe (C.CodePoint QName) → Maybe Code
    shell nothing = nothing
    shell (just p) = just (materialize up us fs (Q.projectUpstreamShell p roots))

-- Port annotations describe one node's incoming edges. Calling the annotator
-- at each visited node preserves the pre-TC Expr/Clause itself as the payload.
data Demand : Set where
  strictPrimitive demandedOnce deferred branchChoice : Demand

domains : Expr → List (Arg Expr)
domains (pi (bind h ns t) rest) = map (λ n → arg h (just n) t) ns ++ domains rest
domains (fun′ a rest) = a ∷ domains rest
domains _ = []

codomain : Expr → Expr
codomain (pi _ t) = codomain t
codomain (fun′ _ t) = codomain t
codomain e = e

declType : List Decl → Maybe Expr
declType [] = nothing
declType (sig _ _ t ∷ _) = just t
declType (dataSig _ _ bs t ∷ _) = just (foldr pi t bs)
declType (recSig _ _ bs t ∷ _) = just (foldr pi t bs)
declType (_ ∷ ds) = declType ds

namedType : Code → QName → Maybe Expr
namedType c q with lookupUnit us q
  where us = units c ++ extUnits c
... | just u = declType (udecls u)
... | nothing = findOwner (units c ++ extUnits c)
  where
    constructorType : QName → List Decl → Maybe Expr
    constructorType owner [] = nothing
    constructorType owner (dataDef _ _ _ cs ∷ rest) = find cs
      where
        find : List (Name × Expr) → Maybe Expr
        find [] = constructorType owner rest
        find ((n , t) ∷ ns) = if (mkQ (full owner ++ [ n ])) ==ᴺ q then just t else find ns
    constructorType owner (_ ∷ rest) = constructorType owner rest
    findOwner : List Unit → Maybe Expr
    findOwner [] = nothing
    findOwner (u ∷ more) with constructorType (uname u) (udecls u)
    ... | just t = just t
    ... | nothing = findOwner more

headExpr : Expr → Expr
headExpr (app f _) = headExpr f
headExpr e = e

isProp : Expr → Bool
isProp (def q) = full q ==ᴸ ("Agda" ∷ "Primitive" ∷ "Prop" ∷ [])
  where _==ᴸ_ = eqList _==ˢ_
isProp _ = false

sortPosition : Expr → Bool
sortPosition (set _) = true
sortPosition e = isProp (headExpr e) ∨ isSetApp (headExpr e)
  where
    isSetApp : Expr → Bool
    isSetApp (set _) = true
    isSetApp _ = false

erasedType : Code → Expr → Bool
erasedType c (pi _ rest) = erasedType c rest
erasedType c (fun′ _ rest) = erasedType c rest
erasedType c t with headExpr t
... | def q with namedType c q
...   | just ty = sortPosition t ∨ isProp (headExpr (codomain ty))
...   | nothing = sortPosition t ∨ eqList _==ˢ_ (full q) ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ [])
erasedType c t | _ = sortPosition t

erasedExpr : Code → Expr → Bool
erasedExpr c (set _) = true
erasedExpr c (pi _ _) = true
erasedExpr c (fun′ _ _) = true
erasedExpr c e with headExpr e
... | def q with namedType c q
...   | just t = erasedType c (codomain t)
...   | nothing = sortPosition e
erasedExpr c _ | _ = false

portColor : Demand → Bool → Hiding → EvalColor
portColor _ _ hidden = Ghost
portColor _ _ inst = Ghost
portColor _ true visible = Ghost
portColor strictPrimitive false visible = StrictVal
portColor demandedOnce false visible = StrictVal
portColor deferred false visible = Thunked
portColor branchChoice false visible = Thunked

matches : ∀ {A : Set} → Arg A → Arg Expr → Bool
matches (arg h n _) (arg h′ n′ _) = eqHiding h h′ ∧ labels n n′
  where
    labels : Maybe Name → Maybe Name → Bool
    labels nothing _ = true
    labels (just n) (just m) = n ==ˢ m
    labels _ _ = false

-- Scope checking can omit implicit arguments. Skip their formals before
-- considering the type of a visible port.
typeAtPort : ∀ {A : Set} → Arg A → List (Arg Expr) → Maybe Expr × List (Arg Expr)
typeAtPort a [] = nothing , []
typeAtPort a (b ∷ bs) with matches a b
... | true = just (thing b) , bs
... | false with hid b
...   | visible = nothing , b ∷ bs
...   | _ = typeAtPort a bs

knownErased : Code → Maybe Expr → Bool
knownErased c (just t) = erasedType c t
knownErased _ nothing = false

strictHead : Expr → Bool
strictHead (def q) = anyᵇ (eqList _==ˢ_ (full q))
  (map (λ n → "Agda" ∷ "Builtin" ∷ "Nat" ∷ n ∷ [])
       ("_+_" ∷ "_-_" ∷ "_*_" ∷ "_==_" ∷ "_<_" ∷ []))
strictHead _ = false

appSpine : Expr → List (Arg Expr) → Expr × List (Arg Expr)
appSpine (app f a) as = appSpine f (a ∷ as)
appSpine f as = f , as

singleIdentity : Unit → ℕ → Bool
singleIdentity u pos = anyᵇ identityAt (udecls u)
  where
    returnsPort : ℕ → List (Arg Pat) → Name → Bool
    returnsPort zero (arg _ _ (varP n) ∷ _) x = n ==ˢ x
    returnsPort (suc k) (_ ∷ ps) x = returnsPort k ps x
    returnsPort _ _ _ = false
    identityAt : Decl → Bool
    identityAt (fun _ _ (clause (head _ ps) (rhs (var x)) [] ∷ [])) = returnsPort pos ps x
    identityAt _ = false

branchingRhs : RHS → Bool
branchingRhs (withRHS _ _) = true
branchingRhs (rewriteRHS _ rr) = branchingRhs rr
branchingRhs (rhs (lamCase (_ ∷ _ ∷ _))) = true
branchingRhs _ = false

branches : Decl → Bool
branches (fun _ _ (_ ∷ _ ∷ _)) = true
branches (fun _ _ (clause _ r _ ∷ [])) = branchingRhs r
branches _ = false

argDemand : Code → Expr → ℕ → Expr → Demand
argDemand c (con _) pos _ = deferred
argDemand c hd pos val with strictHead hd
... | true = strictPrimitive
... | false with hd
...   | def q with lookupUnit (units c) q
...     | just u = if anyᵇ branches (udecls u) then branchChoice else
                   (if singleIdentity u pos then demandedOnce else scalarDemand val)
  where
    scalarDemand : Expr → Demand
    scalarDemand (lit _) = strictPrimitive
    scalarDemand _ = deferred
...     | nothing = deferred
argDemand c _ pos _ | false | _ = deferred

classifyExprPort : Code → Demand → Maybe Expr → Arg Expr → EvalColor
classifyExprPort c d ty a = portColor d (knownErased c ty ∨ erasedExpr c (thing a)) (hid a)

record ExprPort (color : EvalColor) : Set where
  constructor expressionPort
  field
    scope : Code
    demand : Demand
    expectedType : Maybe Expr
    argument : Arg Expr
    checkedColor : classifyExprPort scope demand expectedType argument ≡ color

module ConcretePorts = C.TotalPorts QName ExprPort

checkedExprPort : (c : Code) (d : Demand) (t : Maybe Expr) (a : Arg Expr) →
                  ConcretePorts.Fiber (C.portColor (classifyExprPort c d t a))
checkedExprPort c d t a = expressionPort c d t a refl

mutual
  choiceValues : List Clause → List Expr
  choiceValues [] = []
  choiceValues (clause _ r _ ∷ cs) = choices r ++ choiceValues cs
  choices : RHS → List Expr
  choices (rhs v) = [ v ]
  choices absurdRHS = []
  choices (withRHS _ cs) = choiceValues cs
  choices (rewriteRHS _ r) = choices r

-- In the absence of an expected record name, erase a field when all records
-- matching this literal agree that its type is erased. The expected-type
-- entry point below can disambiguate overloaded field names before elaboration.
annotateRecordFields : Code → Maybe QName → List (Name × Expr) → List (Arg Expr × EvalColor)
annotateRecordFields c expected fs = map fieldPort fs
  where
    compatible : Maybe QName → Unit → Bool
    compatible nothing _ = true
    compatible (just q) u = q ==ᴺ uname u
    candidates : Decl → List (List (Name × Expr))
    candidates (recDef _ _ _ _ fields) =
      if allᵇ (λ n → elemᵇ _==ˢ_ n (map proj₁ fields)) (map proj₁ fs) then [ fields ] else []
    candidates _ = []
    records = concatMap (λ u → concatMap candidates (udecls u)) (filterᵇ (compatible expected) (units c ++ extUnits c))
    allErased : List Expr → Bool
    allErased [] = false
    allErased ts@(_ ∷ _) = allᵇ (erasedType c) ts
    fieldPort : Name × Expr → Arg Expr × EvalColor
    fieldPort (n , e) = arg visible (just n) e , portColor deferred (erasedExpr c e ∨ allErased ts) visible
      where ts = map proj₂ (concatMap (filterᵇ (λ f → n ==ˢ proj₁ f)) records)

annotateExprPorts : Code → Expr → List (Arg Expr × EvalColor)
annotateExprPorts c (lamCase cs) = map (λ e → vis e , classifyExprPort c branchChoice nothing (vis e)) (choiceValues cs)
annotateExprPorts c (rec′ fs) = annotateRecordFields c nothing fs
annotateExprPorts c (recUpd r fs) = (vis r , StrictVal) ∷ annotateExprPorts c (rec′ fs)
annotateExprPorts c (pi (bind h _ t) body) = (arg h nothing t , Ghost) ∷ (vis body , Ghost) ∷ []
annotateExprPorts c (fun′ a body) = (a , Ghost) ∷ (vis body , Ghost) ∷ []
annotateExprPorts c e with appSpine e []
... | hd , as = colorArgs 0 as (headDomains hd)
  where
    headDomains : Expr → List (Arg Expr)
    headDomains (def q) with namedType c q
    ... | just t = domains t
    ... | nothing = []
    headDomains (con q) with namedType c q
    ... | just t = domains t
    ... | nothing = []
    headDomains _ = []
    colorArgs : ℕ → List (Arg Expr) → List (Arg Expr) → List (Arg Expr × EvalColor)
    colorArgs _ [] _ = []
    colorArgs k (a ∷ xs) ts with typeAtPort a ts
    ... | ty , rest = (a , classifyExprPort c (argDemand c hd k (thing a)) ty a)
                      ∷ colorArgs (suc k) xs rest

annotateExprPortsAt : Code → Expr → Expr → List (Arg Expr × EvalColor)
annotateExprPortsAt c ty (rec′ fs) with headExpr ty
... | def q = annotateRecordFields c (just q) fs
... | _ = annotateRecordFields c nothing fs
annotateExprPortsAt c _ e = annotateExprPorts c e

annotateClausePorts : Code → Unit → Clause → List (Arg Pat × EvalColor)
annotateClausePorts c u (clause l r _) = mark 0 (patterns l) types
  where
    types : List (Arg Expr)
    types with declType (udecls u)
    ... | just t = domains t
    ... | nothing = []
    patterns : LHS → List (Arg Pat)
    patterns (head _ ps) = ps
    patterns (proj _ l ps) = patterns l ++ ps
    patterns (with′ l ws ps) = patterns l ++ ws ++ ps
    demand : ℕ → Pat → Demand
    demand k p with anyᵇ branches (udecls u) ∨ branchingRhs r
    ... | true = branchChoice
    ... | false with p
    ...   | litP _ = strictPrimitive
    ...   | conP _ _ = demandedOnce
    ...   | _ = if singleIdentity u k then demandedOnce else deferred
    mark : ℕ → List (Arg Pat) → List (Arg Expr) → List (Arg Pat × EvalColor)
    mark k [] _ = []
    mark k (a ∷ as) ts with typeAtPort a ts
    ... | ty , rest = (a , portColor (demand k (thing a)) (knownErased c ty) (hid a))
                      ∷ mark (suc k) as rest
