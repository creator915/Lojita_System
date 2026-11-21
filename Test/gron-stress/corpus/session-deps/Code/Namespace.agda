module Code.Namespace where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char; isAlpha; isDigit)
open import Agda.Builtin.Char using (primCharEquality)
open import Data.List using (List; []; _∷_; [_]; _++_; map; concatMap)
open import Data.Maybe as Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList; intersperse) renaming (_++_ to _++ˢ_)

open import Code
open import Code.Transport using (Plan; mkPlan; Proarrow; _⇝_)

record NamespaceCtx : Set where
  constructor nsCtx
  field
    epoch     : Name
    ownerPath : List Name
open NamespaceCtx public

validSegment : Name → Bool
validSegment n with toList n
... | [] = false
... | c ∷ cs = initial c ∧ allᵇ (λ d → initial d ∨ isDigit d) cs
             ∧ not (elemᵇ _==ˢ_ n reserved)
  where
    initial : Char → Bool
    initial d = isAlpha d ∨ primCharEquality d '_'

    reserved = "module" ∷ "where" ∷ "import" ∷ "open" ∷ "postulate" ∷ "data" ∷ "record"
             ∷ "code" ∷ "memory" ∷ "spec" ∷ "ai" ∷ "dump" ∷ "agda" ∷ "child" ∷ []

private
  hasRoot : List Name → QName → Bool
  hasRoot roots (qn [] _) = false
  hasRoot roots (qn (r ∷ _) _) = elemᵇ _==ˢ_ r roots

  libraryRoots = "Data" ∷ "Relation" ∷ "Function" ∷ "Algebra" ∷ "Category"
               ∷ "Induction" ∷ "Context" ∷ []

  ioModule : QName → Bool
  ioModule (qn ("IO" ∷ _) _) = true
  ioModule (qn ("Agda" ∷ path) _) = elemᵇ _==ˢ_ "IO" path
  ioModule _ = false

isMetaModule : QName → Bool
isMetaModule (qn ("Main" ∷ []) _) = true
isMetaModule q = hasRoot ("Ownership" ∷ "OwnershipIO" ∷ "Code" ∷ "Store" ∷ "Meta"
                       ∷ "Backend" ∷ "Test" ∷ "Verification" ∷ "SessionEnv" ∷ []) q

isPreTaskContext : QName → Bool
isPreTaskContext q = safeQName q ∧ hasRoot ("Agda" ∷ "Level" ∷ "Axiom" ∷ "Codata" ∷ "Effect" ∷ "IO" ∷ libraryRoots) q

isClosedWorldContext : QName → Bool
isClosedWorldContext (qn ("Level" ∷ []) _) = true
isClosedWorldContext q = safeQName q ∧ hasRoot ("Agda" ∷ libraryRoots) q ∧ not (ioModule q)

canonicalMod : NamespaceCtx → Name → QName
canonicalMod (nsCtx e path) = qn ("Gen" ∷ e ∷ path)

private
  below : NamespaceCtx → Name → NamespaceCtx
  below (nsCtx e path) k = nsCtx e (path ++ [ k ])

childCtx : NamespaceCtx → Name → Maybe NamespaceCtx
childCtx ctx k = if validSegment k then just (below ctx k) else nothing

data NamespaceProblem : Set where
  invalidSlotSegment               : Name → NamespaceProblem
  metaNamespaceCollision           : QName → NamespaceProblem
  forbiddenSiblingOrExternalImport : QName → NamespaceProblem
  duplicateChildSlot               : Name → NamespaceProblem

private
  -- 只替换首段一次。别名目标已经是全名，shown 属于引用处的作用域。
  expand : NamespaceCtx → Name → List Name → List (Name × QName) → QName → QName
  expand ctx self kids bases (qn [] s) = qn [] s
  expand ctx self kids bases q@(qn (k ∷ suffix) s) =
    if k ==ˢ self then qn (prefix ++ suffix) s
    else if elemᵇ _==ˢ_ k kids then qn (prefix ++ (k ∷ suffix)) s
    else fromBase bases
    where
      prefix = full (canonicalMod ctx self)

      fromBase : List (Name × QName) → QName
      fromBase [] = q
      fromBase ((alias , target) ∷ rest) =
        if k ==ˢ alias then qn (full target ++ suffix) s else fromBase rest

  -- import/open 也携带 QName，甚至可以出现在 λ where 的子句里。
  -- 直接结构递归重写 QName，并单独收集实际进入父作用域的 import（assumes 是孩子接口，不计入父作用域）。
  mutual
    rewriteExpr : (QName → QName) → Expr → Expr
    rewriteExpr ρ (def q) = def (ρ q)
    rewriteExpr ρ (con q) = con (ρ q)
    rewriteExpr ρ (app f a) = app (rewriteExpr ρ f) (rewriteArg ρ a)
    rewriteExpr ρ (lam x e) = lam x (rewriteExpr ρ e)
    rewriteExpr ρ (lamT b e) = lamT (rewriteBind ρ b) (rewriteExpr ρ e)
    rewriteExpr ρ (lamCase cs) = lamCase (rewriteClauses ρ cs)
    rewriteExpr ρ (pi b e) = pi (rewriteBind ρ b) (rewriteExpr ρ e)
    rewriteExpr ρ (fun′ a e) = fun′ (rewriteArg ρ a) (rewriteExpr ρ e)
    rewriteExpr ρ (let′ bs e) = let′ (rewriteLets ρ bs) (rewriteExpr ρ e)
    rewriteExpr ρ (rec′ fs) = rec′ (rewriteFields ρ fs)
    rewriteExpr ρ (recUpd e fs) = recUpd (rewriteExpr ρ e) (rewriteFields ρ fs)
    rewriteExpr ρ (dot e) = dot (rewriteExpr ρ e)
    rewriteExpr ρ e = e

    rewriteArg : (QName → QName) → Arg Expr → Arg Expr
    rewriteArg ρ (arg h l e) = arg h l (rewriteExpr ρ e)

    rewriteExprs : (QName → QName) → List Expr → List Expr
    rewriteExprs ρ [] = []
    rewriteExprs ρ (e ∷ es) = rewriteExpr ρ e ∷ rewriteExprs ρ es

    rewriteFields : (QName → QName) → List (Name × Expr) → List (Name × Expr)
    rewriteFields ρ [] = []
    rewriteFields ρ ((n , e) ∷ fs) = (n , rewriteExpr ρ e) ∷ rewriteFields ρ fs

    rewriteBind : (QName → QName) → Bind → Bind
    rewriteBind ρ (bind h ns e) = bind h ns (rewriteExpr ρ e)

    rewriteBinds : (QName → QName) → List Bind → List Bind
    rewriteBinds ρ [] = []
    rewriteBinds ρ (b ∷ bs) = rewriteBind ρ b ∷ rewriteBinds ρ bs

    rewritePat : (QName → QName) → Pat → Pat
    rewritePat ρ (conP q ps) = conP (ρ q) (rewritePats ρ ps)
    rewritePat ρ (projP q) = projP (ρ q)
    rewritePat ρ (dotP e) = dotP (rewriteExpr ρ e)
    rewritePat ρ (asP n p) = asP n (rewritePat ρ p)
    rewritePat ρ (recP fs) = recP (rewritePatFields ρ fs)
    rewritePat ρ p = p

    rewritePatFields : (QName → QName) → List (Name × Pat) → List (Name × Pat)
    rewritePatFields ρ [] = []
    rewritePatFields ρ ((n , p) ∷ fs) = (n , rewritePat ρ p) ∷ rewritePatFields ρ fs

    rewritePats : (QName → QName) → List (Arg Pat) → List (Arg Pat)
    rewritePats ρ [] = []
    rewritePats ρ (arg h l p ∷ ps) = arg h l (rewritePat ρ p) ∷ rewritePats ρ ps

    rewriteLets : (QName → QName) → List LetBind → List LetBind
    rewriteLets ρ [] = []
    rewriteLets ρ (letBind n t e ∷ bs) = letBind n (rewriteExpr ρ t) (rewriteExpr ρ e) ∷ rewriteLets ρ bs
    rewriteLets ρ (letPat p e ∷ bs) = letPat (rewritePat ρ p) (rewriteExpr ρ e) ∷ rewriteLets ρ bs

    rewriteLHS : (QName → QName) → LHS → LHS
    rewriteLHS ρ (head q ps) = head (ρ q) (rewritePats ρ ps)
    rewriteLHS ρ (proj q l ps) = proj (ρ q) (rewriteLHS ρ l) (rewritePats ρ ps)
    rewriteLHS ρ (with′ l ws ps) = with′ (rewriteLHS ρ l) (rewritePats ρ ws) (rewritePats ρ ps)

    rewriteRight : (QName → QName) → RHS → RHS
    rewriteRight ρ (rhs e) = rhs (rewriteExpr ρ e)
    rewriteRight ρ absurdRHS = absurdRHS
    rewriteRight ρ (withRHS es cs) = withRHS (rewriteExprs ρ es) (rewriteClauses ρ cs)
    rewriteRight ρ (rewriteRHS es r) = rewriteRHS (rewriteExprs ρ es) (rewriteRight ρ r)

    rewriteClauses : (QName → QName) → List Clause → List Clause
    rewriteClauses ρ [] = []
    rewriteClauses ρ (clause l r w ∷ cs) =
      clause (rewriteLHS ρ l) (rewriteRight ρ r) (rewriteDecls ρ w) ∷ rewriteClauses ρ cs

    rewriteDecl : (QName → QName) → Decl → Decl
    rewriteDecl ρ (import′ m o d ifc) = import′ (ρ m) o d (rewriteDecls ρ ifc)
    rewriteDecl ρ (open′ m d) = open′ (ρ m) d
    rewriteDecl ρ (sig m n e) = sig m n (rewriteExpr ρ e)
    rewriteDecl ρ (fun m n cs) = fun m n (rewriteClauses ρ cs)
    rewriteDecl ρ (dataSig m n bs e) = dataSig m n (rewriteBinds ρ bs) (rewriteExpr ρ e)
    rewriteDecl ρ (dataDef m n ns cs) = dataDef m n ns (rewriteFields ρ cs)
    rewriteDecl ρ (recSig m n bs e) = recSig m n (rewriteBinds ρ bs) (rewriteExpr ρ e)
    rewriteDecl ρ (recDef m n ns d fs) = recDef m n ns d (rewriteFields ρ fs)
    rewriteDecl ρ (variable′ vs) = variable′ (rewriteFields ρ vs)
    rewriteDecl ρ (module′ n bs ds) = module′ n (rewriteBinds ρ bs) (rewriteDecls ρ ds)
    rewriteDecl ρ d = d

    rewriteDecls : (QName → QName) → List Decl → List Decl
    rewriteDecls ρ [] = []
    rewriteDecls ρ (d ∷ ds) = rewriteDecl ρ d ∷ rewriteDecls ρ ds

  mutual
    importsExpr : Expr → List QName
    importsExpr (app f a) = importsExpr f ++ importsArg a
    importsExpr (lam _ e) = importsExpr e
    importsExpr (lamT b e) = importsBind b ++ importsExpr e
    importsExpr (lamCase cs) = importsClauses cs
    importsExpr (pi b e) = importsBind b ++ importsExpr e
    importsExpr (fun′ a e) = importsArg a ++ importsExpr e
    importsExpr (let′ bs e) = importsLets bs ++ importsExpr e
    importsExpr (rec′ fs) = importsFields fs
    importsExpr (recUpd e fs) = importsExpr e ++ importsFields fs
    importsExpr (dot e) = importsExpr e
    importsExpr _ = []

    importsArg : Arg Expr → List QName
    importsArg (arg _ _ e) = importsExpr e

    importsExprs : List Expr → List QName
    importsExprs [] = []
    importsExprs (e ∷ es) = importsExpr e ++ importsExprs es

    importsFields : List (Name × Expr) → List QName
    importsFields [] = []
    importsFields ((_ , e) ∷ fs) = importsExpr e ++ importsFields fs

    importsBind : Bind → List QName
    importsBind (bind _ _ e) = importsExpr e

    importsBinds : List Bind → List QName
    importsBinds [] = []
    importsBinds (b ∷ bs) = importsBind b ++ importsBinds bs

    importsPat : Pat → List QName
    importsPat (conP _ ps) = importsPats ps
    importsPat (dotP e) = importsExpr e
    importsPat (asP _ p) = importsPat p
    importsPat (recP fs) = importsPatFields fs
    importsPat _ = []

    importsPatFields : List (Name × Pat) → List QName
    importsPatFields [] = []
    importsPatFields ((_ , p) ∷ fs) = importsPat p ++ importsPatFields fs

    importsPats : List (Arg Pat) → List QName
    importsPats [] = []
    importsPats (arg _ _ p ∷ ps) = importsPat p ++ importsPats ps

    importsLets : List LetBind → List QName
    importsLets [] = []
    importsLets (letBind _ t e ∷ bs) = importsExpr t ++ importsExpr e ++ importsLets bs
    importsLets (letPat p e ∷ bs) = importsPat p ++ importsExpr e ++ importsLets bs

    importsLHS : LHS → List QName
    importsLHS (head _ ps) = importsPats ps
    importsLHS (proj _ l ps) = importsLHS l ++ importsPats ps
    importsLHS (with′ l ws ps) = importsLHS l ++ importsPats ws ++ importsPats ps

    importsRHS : RHS → List QName
    importsRHS (rhs e) = importsExpr e
    importsRHS absurdRHS = []
    importsRHS (withRHS es cs) = importsExprs es ++ importsClauses cs
    importsRHS (rewriteRHS es r) = importsExprs es ++ importsRHS r

    importsClauses : List Clause → List QName
    importsClauses [] = []
    importsClauses (clause l r w ∷ cs) =
      importsLHS l ++ importsRHS r ++ importsDecls w ++ importsClauses cs

    importsDecl : Decl → List QName
    importsDecl (import′ m _ _ _) = [ m ]
    importsDecl (sig _ _ e) = importsExpr e
    importsDecl (fun _ _ cs) = importsClauses cs
    importsDecl (dataSig _ _ bs e) = importsBinds bs ++ importsExpr e
    importsDecl (dataDef _ _ _ cs) = importsFields cs
    importsDecl (recSig _ _ bs e) = importsBinds bs ++ importsExpr e
    importsDecl (recDef _ _ _ _ fs) = importsFields fs
    importsDecl (variable′ vs) = importsFields vs
    importsDecl (module′ _ bs ds) = importsBinds bs ++ importsDecls ds
    importsDecl _ = []

    importsDecls : List Decl → List QName
    importsDecls [] = []
    importsDecls (d ∷ ds) = importsDecl d ++ importsDecls ds

  slotProblems : List Name → List Name → List NamespaceProblem
  slotProblems seen [] = []
  slotProblems seen (k ∷ ks) =
    (if validSegment k then [] else [ invalidSlotSegment k ])
    ++ (if elemᵇ _==ˢ_ k seen then [ duplicateChildSlot k ] else [])
    ++ slotProblems (k ∷ seen) ks

checkNodeImports : NamespaceCtx → List Name → List QName → Code → List NamespaceProblem
checkNodeImports ctx ownedKids allowedBases c = slotProblems [] ownedKids
  ++ concatMap problem (importsBinds (params c) ++ importsDecls (decls c))
  where
    directChild : QName → Name → Bool
    directChild m k = m ==ᴺ mkQ [ k ] ∨ m ==ᴺ canonicalMod (below ctx k) k

    problem : QName → List NamespaceProblem
    problem m =
      if not (safeQName m) then [ forbiddenSiblingOrExternalImport m ]
      else if isMetaModule m then [ metaNamespaceCollision m ]
      else if isClosedWorldContext m ∨ anyᵇ (directChild m) ownedKids
              ∨ (not (ioModule m) ∧ elemᵇ _==ᴺ_ m allowedBases)
           then [] else [ forbiddenSiblingOrExternalImport m ]

checkTaskImports : NamespaceCtx → List Name → List QName → Code → List NamespaceProblem
checkTaskImports = checkNodeImports

qualifyCode : NamespaceCtx → Name → List Name → List (Name × QName) → Code → Code
qualifyCode ctx self kids bases (code m ps ds) =
  code (canonicalMod ctx (shown m)) (rewriteBinds rename ps) (rewriteDecls rename ds)
  where rename = expand ctx self kids bases

qualifyPlanWithBases : NamespaceCtx → Name → List Name → List (Name × QName) → Plan → Plan
qualifyPlanWithBases ctx self kids bases (mkPlan why origin ds moves) =
  mkPlan why (Maybe.map rename origin) (rewriteDecls rename ds) (map move moves)
  where
    rename = expand ctx self kids bases

    object : Obj → Obj
    object (unit q) = unit (rename q)
    object (ext q)  = ext (rename q)
    object flags    = flags
    object ⊥        = ⊥

    move : Proarrow → Proarrow
    move (s ⇝ t) = object s ⇝ object t

qualifyPlan : NamespaceCtx → Name → List Name → Plan → Plan
qualifyPlan ctx self kids = qualifyPlanWithBases ctx self kids []

disjointPaths : List Code → Bool
disjointPaths [] = true
disjointPaths (c ∷ cs) = not (anyᵇ (λ d → modName c ==ᴺ modName d) cs) ∧ disjointPaths cs

-- Session sources may already carry canonical names. Legacy module headers
-- stay addressable by the names used by existing scripts and lift descriptors.
namespaceOf : QName → NamespaceCtx
namespaceOf (qn ("Gen" ∷ e ∷ path) _) = nsCtx e path
namespaceOf m = nsCtx "" (full m)

canonicalRootOK : Name → QName → Bool
canonicalRootOK name (qn ("Gen" ∷ e ∷ r ∷ []) _) = e ==ˢ name ∧ validSegment e ∧ validSegment r
canonicalRootOK _ (qn ("Gen" ∷ _) _) = false
canonicalRootOK _ q = not (isMetaModule q ∨ isPreTaskContext q)

showNamespaceProblem : NamespaceProblem → Name
showNamespaceProblem (invalidSlotSegment n) = "invalid child slot " ++ˢ n
showNamespaceProblem (duplicateChildSlot n) = "duplicate child slot " ++ˢ n
showNamespaceProblem (metaNamespaceCollision m) = "reserved module " ++ˢ intersperse "." (full m)
showNamespaceProblem (forbiddenSiblingOrExternalImport m) = "forbidden import " ++ˢ intersperse "." (full m)

-- Check resolved imports against the exact owned module identities. A kept
-- child can legitimately retain its module path from a previous epoch.
checkOwnedNames : QName → List QName → List QName → List QName → List NamespaceProblem
checkOwnedNames parent owned retained bases =
  slotProblems [] (map (λ q → shown (mkQ (full q))) owned)
  ++ concatMap owner owned
  where
    ctx = namespaceOf parent
    owner : QName → List NamespaceProblem
    owner q = if isMetaModule q ∨ isPreTaskContext q then [ metaNamespaceCollision q ]
      else if elemᵇ _==ᴺ_ q retained then []
      else if elemᵇ _==ᴺ_ q bases then [ forbiddenSiblingOrExternalImport q ]
      else if (epoch ctx ==ˢ "") ∨ (q ==ᴺ canonicalMod (below ctx (shown (mkQ (full q)))) (shown q))
        then [] else [ forbiddenSiblingOrExternalImport q ]

checkOwnedImports : QName → List QName → List QName → List QName → Code → List NamespaceProblem
checkOwnedImports parent owned retained bases c = checkOwnedNames parent owned retained bases
  ++ checkTaskImports (namespaceOf parent) [] (owned ++ bases) c
