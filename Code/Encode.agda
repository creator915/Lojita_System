------------------------------------------------------------------------
-- Code/Encode.agda —— Code → s-expr。Dump.hs 输出格式的镜像；Code/Parse.agda 的逆。
--
-- 用处：存盘（Code/Codecs.agda）、以后的内容寻址（规范化后哈希的就是这串）。
-- 和 Parse 一一对应：decodeCode (encodeCode c) ≡ just c（Test/EncodeTest.agda 用 refl 验）。
------------------------------------------------------------------------
module Code.Encode where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; intersperse; fromList)

open import Code
open import Code.SExpr
open import Code.Transport using (Plan; mkPlan; Proarrow; _⇝_; Memory)

-- 名字：shown 就是最后一段时只写 full，否则写 (q full shown)（Parse 的 decodeQ 两种都认）
encQ : QName → SExpr
encQ q = let f = intersperse "." (full q) in
         if shown q ==ˢ shown (mkQ (full q)) then str f else list (sym "q" ∷ str f ∷ str (shown q) ∷ [])

encHid : Hiding → SExpr
encHid visible = sym "vis"
encHid hidden  = sym "hid"
encHid inst    = sym "inst"

encLabel : Maybe Name → SExpr
encLabel nothing  = sym "_"
encLabel (just l) = str l

encLit : Lit → SExpr
encLit (natL n)  = list (sym "nat" ∷ num n ∷ [])
encLit (strL s)  = list (sym "str" ∷ str s ∷ [])
encLit (charL c) = list (sym "chr" ∷ str (fromList (c ∷ [])) ∷ [])

encMods : Mods → SExpr
encMods (mods p i a t) = list (sym "mods" ∷ (if p then sym "private" ∷ [] else []) ++ (if i then sym "instance" ∷ [] else []) ++ (if a then sym "abstract" ∷ [] else []) ++ encTC t)
  where
    encTC : TermCheck → List SExpr
    encTC check          = []
    encTC nonTerminating = sym "nonterminating" ∷ []
    encTC terminating    = sym "terminating" ∷ []

encAssoc : Assoc → SExpr
encAssoc infixL = sym "l"
encAssoc infixR = sym "r"
encAssoc infixN = sym "n"

encNames : List Name → List SExpr
encNames = map str

encDir : Directive → SExpr
encDir (directive u h r p) = list
  ( sym "dir"
  ∷ usingS u
  ∷ list (sym "hiding" ∷ encNames h)
  ∷ list (sym "renaming" ∷ map (λ ab → list (str (Data.Product.proj₁ ab) ∷ str (Data.Product.proj₂ ab) ∷ [])) r)
  ∷ (if p then sym "public" else sym "private") ∷ [])
  where
    usingS : Maybe (List Name) → SExpr
    usingS nothing   = sym "everything"
    usingS (just ns) = list (sym "using" ∷ encNames ns)

mutual
  encExpr : Expr → SExpr
  encExpr (var x)             = list (sym "var" ∷ str x ∷ [])
  encExpr (def q)             = list (sym "def" ∷ encQ q ∷ [])
  encExpr (con q)             = list (sym "con" ∷ encQ q ∷ [])
  encExpr (lit l)             = list (sym "lit" ∷ encLit l ∷ [])
  encExpr (set n)             = list (sym "set" ∷ num n ∷ [])
  encExpr hole                = sym "hole"
  encExpr meta                = sym "meta"
  encExpr (app f a)           = list (sym "app" ∷ encExpr f ∷ encArg a ∷ [])
  encExpr (lam (arg h l x) e) = list (sym "lam" ∷ list (sym "arg" ∷ encHid h ∷ encLabel l ∷ str x ∷ []) ∷ encExpr e ∷ [])
  encExpr (lamT b e)          = list (sym "lamT" ∷ encBind b ∷ encExpr e ∷ [])
  encExpr (absurdLam h)       = list (sym "absurdlam" ∷ encHid h ∷ [])
  encExpr (lamCase cs)        = list (sym "lamcase" ∷ encClauses cs)
  encExpr (pi b e)            = list (sym "pi" ∷ encBind b ∷ encExpr e ∷ [])
  encExpr (fun′ a e)          = list (sym "fun" ∷ encArg a ∷ encExpr e ∷ [])
  encExpr (let′ bs e)         = list (sym "let" ∷ list (encLetBinds bs) ∷ encExpr e ∷ [])
  encExpr (rec′ fs)           = list (sym "rec" ∷ list (encFields fs) ∷ [])
  encExpr (recUpd r fs)       = list (sym "recupd" ∷ encExpr r ∷ list (encFields fs) ∷ [])
  encExpr (dot e)             = list (sym "dot" ∷ encExpr e ∷ [])

  encArg : Arg Expr → SExpr
  encArg (arg h l e) = list (sym "arg" ∷ encHid h ∷ encLabel l ∷ encExpr e ∷ [])

  encExprs : List Expr → List SExpr
  encExprs []       = []
  encExprs (e ∷ es) = encExpr e ∷ encExprs es

  encBind : Bind → SExpr
  encBind (bind h xs t) = list (sym "bind" ∷ encHid h ∷ list (encNames xs) ∷ encExpr t ∷ [])

  encBinds : List Bind → List SExpr
  encBinds []       = []
  encBinds (b ∷ bs) = encBind b ∷ encBinds bs

  encFields : List (Name × Expr) → List SExpr
  encFields []             = []
  encFields ((n , e) ∷ fs) = list (sym "fld" ∷ str n ∷ encExpr e ∷ []) ∷ encFields fs

  encLetBinds : List LetBind → List SExpr
  encLetBinds []                    = []
  encLetBinds (letBind x t e ∷ bs)  = list (sym "letbind" ∷ str x ∷ encExpr t ∷ encExpr e ∷ []) ∷ encLetBinds bs
  encLetBinds (letPat p e ∷ bs)     = list (sym "letpat" ∷ encPat p ∷ encExpr e ∷ []) ∷ encLetBinds bs

  encPat : Pat → SExpr
  encPat (varP x)    = list (sym "varp" ∷ str x ∷ [])
  encPat (conP q ps) = list (sym "conp" ∷ encQ q ∷ encPats ps)
  encPat wildP       = sym "wildp"
  encPat (litP l)    = list (sym "litp" ∷ encLit l ∷ [])
  encPat (dotP e)    = list (sym "dotp" ∷ encExpr e ∷ [])
  encPat absurdP     = sym "absurdp"
  encPat (asP x p)   = list (sym "asp" ∷ str x ∷ encPat p ∷ [])
  encPat (projP q)   = list (sym "projp" ∷ encQ q ∷ [])
  encPat (recP fs)   = list (sym "recp" ∷ list (encPatFields fs) ∷ [])

  encPatFields : List (Name × Pat) → List SExpr
  encPatFields []             = []
  encPatFields ((n , p) ∷ fs) = list (sym "fld" ∷ str n ∷ encPat p ∷ []) ∷ encPatFields fs

  encPats : List (Arg Pat) → List SExpr
  encPats []                 = []
  encPats (arg h l p ∷ ps)   = list (sym "arg" ∷ encHid h ∷ encLabel l ∷ encPat p ∷ []) ∷ encPats ps

  encLHS : LHS → SExpr
  encLHS (head f ps)     = list (sym "head" ∷ encQ f ∷ encPats ps)
  encLHS (proj d l ps)   = list (sym "proj" ∷ encQ d ∷ encLHS l ∷ encPats ps)
  encLHS (with′ l ws ps) = list (sym "with" ∷ encLHS l ∷ list (encPats ws) ∷ list (encPats ps) ∷ [])

  encRHS : RHS → SExpr
  encRHS (rhs e)           = list (sym "rhs" ∷ encExpr e ∷ [])
  encRHS absurdRHS         = sym "absurdrhs"
  encRHS (withRHS es cs)   = list (sym "withrhs" ∷ list (encExprs es) ∷ list (encClauses cs) ∷ [])
  encRHS (rewriteRHS es r) = list (sym "rewriterhs" ∷ list (encExprs es) ∷ encRHS r ∷ [])

  encClause : Clause → SExpr
  encClause (clause l r w) = list (sym "clause" ∷ encLHS l ∷ encRHS r ∷ list (sym "where" ∷ encDecls w) ∷ [])

  encClauses : List Clause → List SExpr
  encClauses []       = []
  encClauses (c ∷ cs) = encClause c ∷ encClauses cs

  encDecl : Decl → SExpr
  encDecl (pragma s)           = list (sym "pragma" ∷ str s ∷ [])
  encDecl (import′ m o d a)    = list (sym "import" ∷ encQ m ∷ (if o then sym "open" else sym "noopen") ∷ encDir d ∷ list (sym "assumes" ∷ encDecls a) ∷ [])
  encDecl (open′ m d)          = list (sym "open" ∷ encQ m ∷ encDir d ∷ [])
  encDecl (fixity a n x)       = list (sym "fixity" ∷ encAssoc a ∷ num n ∷ str x ∷ [])
  encDecl (sig m x e)          = list (sym "sig" ∷ encMods m ∷ str x ∷ encExpr e ∷ [])
  encDecl (fun m x cs)         = list (sym "fun" ∷ encMods m ∷ str x ∷ encClauses cs)
  encDecl (dataSig m x bs e)   = list (sym "datasig" ∷ encMods m ∷ str x ∷ list (sym "params" ∷ encBinds bs) ∷ encExpr e ∷ [])
  encDecl (dataDef m x ps cs)  = list (sym "datadef" ∷ encMods m ∷ str x ∷ list (encNames ps) ∷ encCons "con" cs)
  encDecl (recSig m x bs e)    = list (sym "recsig" ∷ encMods m ∷ str x ∷ list (sym "params" ∷ encBinds bs) ∷ encExpr e ∷ [])
  encDecl (recDef m x ps (recDir co c) fs) =
    list (sym "recdef" ∷ encMods m ∷ str x ∷ list (encNames ps)
         ∷ list (sym "recdir" ∷ (if co then sym "coinductive" else sym "inductive") ∷ encLabel c ∷ [])
         ∷ encCons "field" fs)
  encDecl (variable′ vs)       = list (sym "variable" ∷ encVars vs)
  encDecl (module′ x bs ds)    = list (sym "module" ∷ str x ∷ list (sym "params" ∷ encBinds bs) ∷ encDecls ds)
  encDecl (unsupported s)      = list (sym "unsupported" ∷ str s ∷ [])

  encCons : String → List (Name × Expr) → List SExpr
  encCons tag []             = []
  encCons tag ((n , e) ∷ cs) = list (sym tag ∷ str n ∷ encExpr e ∷ []) ∷ encCons tag cs

  encVars : List (Name × Expr) → List SExpr
  encVars []             = []
  encVars ((n , e) ∷ vs) = list (sym "var" ∷ str n ∷ encExpr e ∷ []) ∷ encVars vs

  encDecls : List Decl → List SExpr
  encDecls []       = []
  encDecls (d ∷ ds) = encDecl d ∷ encDecls ds

encodeCode : Code → SExpr
encodeCode (code m ps ds) = list (sym "module" ∷ encQ m ∷ list (sym "params" ∷ encBinds ps) ∷ encDecls ds)

-- 搬运计划里的对象和计划本身
encObj : Obj → SExpr
encObj (unit q) = list (sym "unit" ∷ encQ q ∷ [])
encObj (ext q)  = list (sym "ext" ∷ encQ q ∷ [])
encObj flags    = sym "flags"
encObj ⊥        = sym "bot"

encodePlan : Plan → SExpr
encodePlan (mkPlan why nothing new moves) =
  list (sym "plan" ∷ str why ∷ list (sym "new" ∷ encDecls new) ∷ list (sym "moves" ∷ map (λ a → list (sym "move" ∷ encObj (Proarrow.src a) ∷ encObj (Proarrow.tgt a) ∷ [])) moves) ∷ [])
encodePlan (mkPlan why (just origin) new moves) =
  list (sym "plan" ∷ str why ∷ list (sym "origin" ∷ encQ origin ∷ []) ∷ list (sym "new" ∷ encDecls new)
    ∷ list (sym "moves" ∷ map (λ a → list (sym "move" ∷ encObj (Proarrow.src a) ∷ encObj (Proarrow.tgt a) ∷ [])) moves) ∷ [])

-- 记忆：(memory (note OBJ "…"*)*)
encodeMemory : Memory → SExpr
encodeMemory m = list (sym "memory" ∷ map (λ e → list (sym "note" ∷ encObj (Data.Product.proj₁ e) ∷ map str (Data.Product.proj₂ e))) m)

-- 一串声明（接口 / 规约）：(decls D*)
encodeDecls : List Decl → SExpr
encodeDecls ds = list (sym "decls" ∷ encDecls ds)

-- Canonical serialization erases every presentation-only qualified name,
-- including module/import names (renameCode intentionally preserves these).
canonical : SExpr → SExpr
canonical (list (sym "q" ∷ str f ∷ str sh ∷ [])) = str f
canonical (list xs) = list (canonicalList xs)
  where
    canonicalList : List SExpr → List SExpr
    canonicalList [] = []
    canonicalList (x ∷ xs) = canonical x ∷ canonicalList xs
canonical x = x

encodeCanonical : Code → String
encodeCanonical c = showSExpr (canonical (encodeCode c))

open import Code.Lift
open import Code.Shape

encodeLift : LiftSpec → SExpr
encodeLift (liftSpecTree b u cs es) = list (sym "lift" ∷ encQ b ∷ encQ u ∷ list (children cs) ∷ list (map endpoint es) ∷ [])
  where
    children : List ChildLift → List SExpr
    children [] = []
    children (mkChildLift b u nothing ∷ cs) = list (encQ b ∷ encQ u ∷ []) ∷ children cs
    children (mkChildLift b u (just sub) ∷ cs) = list (encQ b ∷ encQ u ∷ encodeLift sub ∷ []) ∷ children cs
    endpoint : EndpointLift → SExpr
    endpoint (endpointLiftRefs b u s []) = list (encQ b ∷ encQ u ∷ encQ s ∷ [])
    endpoint (endpointLiftRefs b u s rs) = list (encQ b ∷ encQ u ∷ encQ s ∷ list (map encQ rs) ∷ [])

encodeShape : HomeShape → SExpr
encodeShape (node kids) = list (sym "node" ∷ go kids)
  where
    go : List (Name × HomeShape) → List SExpr
    go [] = []
    go ((n , sh) ∷ ks) = list (str n ∷ encodeShape sh ∷ []) ∷ go ks
