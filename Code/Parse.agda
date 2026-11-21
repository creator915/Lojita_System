------------------------------------------------------------------------
-- Code/Parse.agda —— 把 Dump.hs 导出的 s-expr 解码成 Code
--
-- parse : String → Maybe Code
--
-- 这里不做任何"理解"：每种 s-expr 形状对应 Code 的一个构造子，一一对应地搬过去。
-- 不认识的形状 → nothing（整个文件解析失败），宁可失败也不猜。
-- 形状的清单见 README_code.md §2，和 Dump.hs 里的 *S 函数一一对应。
------------------------------------------------------------------------
module Code.Parse where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Char using (Char)
open import Agda.Builtin.Char using (primCharEquality)

open import Code
open import Code.SExpr
open import Code.Transport using (Plan; plan; mkPlan; Proarrow; _⇝_; Memory)

private
  infixl 1 _>>=_
  _>>=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
  nothing >>= f = nothing
  just a  >>= f = f a

  -- "A.ℕ.suc" → "A" ∷ "ℕ" ∷ "suc" ∷ []
  splitDots : String → List Name
  splitDots s = go (toList s) [] []
    where
      go : List Char → List Char → List Name → List Name
      go []       cur acc = reverse (fromList (reverse cur) ∷ acc)
      go (c ∷ cs) cur acc = if primCharEquality c '.' then go cs [] (fromList (reverse cur) ∷ acc)
                            else go cs (c ∷ cur) acc
        where open import Data.Bool using (if_then_else_)

------------------------------------------------------------------------
-- 原子
------------------------------------------------------------------------

decodeNames : List SExpr → Maybe (List Name)
decodeNames []           = just []
decodeNames (str x ∷ xs) = decodeNames xs >>= λ r → just (x ∷ r)
decodeNames (_ ∷ _)      = nothing

decodeQ : SExpr → Maybe QName
decodeQ (str s)                                 = just (mkQ (splitDots s))
decodeQ (list (sym "q" ∷ str f ∷ str sh ∷ as))  = decodeNames as >>= λ alts → just (scopedQName (splitDots f) sh alts)
decodeQ _                                       = nothing

decodeHid : SExpr → Maybe Hiding
decodeHid (sym "vis")  = just visible
decodeHid (sym "hid")  = just hidden
decodeHid (sym "inst") = just inst
decodeHid _            = nothing

decodeLabel : SExpr → Maybe (Maybe Name)
decodeLabel (sym "_") = just nothing
decodeLabel (str x)   = just (just x)
decodeLabel _         = nothing

decodeLit : SExpr → Maybe Lit
decodeLit (list (sym "nat" ∷ num n ∷ [])) = just (natL n)
decodeLit (list (sym "str" ∷ str s ∷ [])) = just (strL s)
decodeLit (list (sym "chr" ∷ str s ∷ [])) with toList s
... | c ∷ _ = just (charL c)
... | []    = nothing
decodeLit _ = nothing

decodeMods : SExpr → Maybe Mods
decodeMods (list (sym "mods" ∷ ms)) = just (go ms plain)
  where
    go : List SExpr → Mods → Mods
    go []                      m = m
    go (sym "private"  ∷ fs)   m = go fs (record m { isPrivate = true })
    go (sym "instance" ∷ fs)   m = go fs (record m { isInstance = true })
    go (sym "abstract" ∷ fs)   m = go fs (record m { isAbstract = true })
    go (sym "nonterminating" ∷ fs) m = go fs (record m { termCheck = nonTerminating })
    go (sym "terminating" ∷ fs)    m = go fs (record m { termCheck = terminating })
    go (_ ∷ fs)                m = go fs m
decodeMods _ = nothing

decodeAssoc : SExpr → Maybe Assoc
decodeAssoc (sym "l") = just infixL
decodeAssoc (sym "r") = just infixR
decodeAssoc (sym "n") = just infixN
decodeAssoc _         = nothing

decodeDir : SExpr → Maybe Directive
decodeDir (list (sym "dir" ∷ u ∷ list (sym "hiding" ∷ hs) ∷ list (sym "renaming" ∷ rs) ∷ pub ∷ [])) =
  decodeUsing u >>= λ u′ → decodeNames hs >>= λ hs′ → decodeRen rs >>= λ rs′ → decodePub pub >>= λ p →
  just (directive u′ hs′ rs′ p)
  where
    decodeUsing : SExpr → Maybe (Maybe (List Name))
    decodeUsing (sym "everything")       = just nothing
    decodeUsing (list (sym "using" ∷ xs)) = decodeNames xs >>= λ ns → just (just ns)
    decodeUsing _                        = nothing
    decodeRen : List SExpr → Maybe (List (Name × Name))
    decodeRen []                              = just []
    decodeRen (list (str a ∷ str b ∷ []) ∷ rs) = decodeRen rs >>= λ r → just ((a , b) ∷ r)
    decodeRen (_ ∷ _)                         = nothing
    decodePub : SExpr → Maybe Bool
    decodePub (sym "public")  = just true
    decodePub (sym "private") = just false
    decodePub _               = nothing
decodeDir _ = nothing

------------------------------------------------------------------------
-- 树
------------------------------------------------------------------------

mutual
  decodeExpr : SExpr → Maybe Expr
  decodeExpr (list (sym "var" ∷ str x ∷ []))        = just (var x)
  decodeExpr (list (sym "def" ∷ q ∷ []))            = decodeQ q >>= λ q′ → just (def q′)
  decodeExpr (list (sym "con" ∷ q ∷ []))            = decodeQ q >>= λ q′ → just (con q′)
  decodeExpr (list (sym "lit" ∷ l ∷ []))            = decodeLit l >>= λ l′ → just (lit l′)
  decodeExpr (list (sym "set" ∷ num n ∷ []))        = just (set n)
  decodeExpr (sym "hole")                           = just hole
  decodeExpr (sym "meta")                           = just meta
  decodeExpr (list (sym "app" ∷ f ∷ a ∷ []))        = decodeExpr f >>= λ f′ → decodeArgE a >>= λ a′ → just (app f′ a′)
  decodeExpr (list (sym "lam" ∷ list (sym "arg" ∷ h ∷ l ∷ str x ∷ []) ∷ e ∷ [])) =
    decodeHid h >>= λ h′ → decodeLabel l >>= λ l′ → decodeExpr e >>= λ e′ → just (lam (arg h′ l′ x) e′)
  decodeExpr (list (sym "lamT" ∷ b ∷ e ∷ []))       = decodeBind b >>= λ b′ → decodeExpr e >>= λ e′ → just (lamT b′ e′)
  decodeExpr (list (sym "absurdlam" ∷ h ∷ []))      = decodeHid h >>= λ h′ → just (absurdLam h′)
  decodeExpr (list (sym "lamcase" ∷ cs))            = decodeClauses cs >>= λ cs′ → just (lamCase cs′)
  decodeExpr (list (sym "pi" ∷ b ∷ e ∷ []))         = decodeBind b >>= λ b′ → decodeExpr e >>= λ e′ → just (pi b′ e′)
  decodeExpr (list (sym "fun" ∷ a ∷ e ∷ []))        = decodeArgE a >>= λ a′ → decodeExpr e >>= λ e′ → just (fun′ a′ e′)
  decodeExpr (list (sym "let" ∷ list bs ∷ e ∷ []))  = decodeLetBinds bs >>= λ bs′ → decodeExpr e >>= λ e′ → just (let′ bs′ e′)
  decodeExpr (list (sym "rec" ∷ list fs ∷ []))      = decodeFlds fs >>= λ fs′ → just (rec′ fs′)
  decodeExpr (list (sym "recupd" ∷ r ∷ list fs ∷ [])) = decodeExpr r >>= λ r′ → decodeFlds fs >>= λ fs′ → just (recUpd r′ fs′)
  decodeExpr (list (sym "dot" ∷ e ∷ []))            = decodeExpr e >>= λ e′ → just (dot e′)
  decodeExpr _                                      = nothing

  decodeArgE : SExpr → Maybe (Arg Expr)
  decodeArgE (list (sym "arg" ∷ h ∷ l ∷ e ∷ [])) =
    decodeHid h >>= λ h′ → decodeLabel l >>= λ l′ → decodeExpr e >>= λ e′ → just (arg h′ l′ e′)
  decodeArgE _ = nothing

  decodeExprs : List SExpr → Maybe (List Expr)
  decodeExprs []       = just []
  decodeExprs (e ∷ es) = decodeExpr e >>= λ e′ → decodeExprs es >>= λ es′ → just (e′ ∷ es′)

  decodeBind : SExpr → Maybe Bind
  decodeBind (list (sym "bind" ∷ h ∷ list xs ∷ t ∷ [])) =
    decodeHid h >>= λ h′ → decodeNames xs >>= λ xs′ → decodeExpr t >>= λ t′ → just (bind h′ xs′ t′)
  decodeBind _ = nothing

  decodeBinds : List SExpr → Maybe (List Bind)
  decodeBinds []       = just []
  decodeBinds (b ∷ bs) = decodeBind b >>= λ b′ → decodeBinds bs >>= λ bs′ → just (b′ ∷ bs′)

  decodeFlds : List SExpr → Maybe (List (Name × Expr))
  decodeFlds []                                   = just []
  decodeFlds (list (sym "fld" ∷ str n ∷ e ∷ []) ∷ fs) = decodeExpr e >>= λ e′ → decodeFlds fs >>= λ fs′ → just ((n , e′) ∷ fs′)
  decodeFlds (_ ∷ _)                              = nothing

  decodeLetBinds : List SExpr → Maybe (List LetBind)
  decodeLetBinds [] = just []
  decodeLetBinds (list (sym "letbind" ∷ str x ∷ t ∷ e ∷ []) ∷ bs) =
    decodeExpr t >>= λ t′ → decodeExpr e >>= λ e′ → decodeLetBinds bs >>= λ bs′ → just (letBind x t′ e′ ∷ bs′)
  decodeLetBinds (list (sym "letpat" ∷ p ∷ e ∷ []) ∷ bs) =
    decodePat p >>= λ p′ → decodeExpr e >>= λ e′ → decodeLetBinds bs >>= λ bs′ → just (letPat p′ e′ ∷ bs′)
  decodeLetBinds (_ ∷ _) = nothing

  decodePat : SExpr → Maybe Pat
  decodePat (list (sym "varp" ∷ str x ∷ []))     = just (varP x)
  decodePat (list (sym "conp" ∷ q ∷ ps))         = decodeQ q >>= λ q′ → decodePats ps >>= λ ps′ → just (conP q′ ps′)
  decodePat (list (sym "projp" ∷ q ∷ []))        = decodeQ q >>= λ q′ → just (projP q′)
  decodePat (sym "wildp")                        = just wildP
  decodePat (list (sym "litp" ∷ l ∷ []))         = decodeLit l >>= λ l′ → just (litP l′)
  decodePat (list (sym "dotp" ∷ e ∷ []))         = decodeExpr e >>= λ e′ → just (dotP e′)
  decodePat (sym "absurdp")                      = just absurdP
  decodePat (list (sym "asp" ∷ str x ∷ p ∷ []))  = decodePat p >>= λ p′ → just (asP x p′)
  decodePat (list (sym "recp" ∷ list fs ∷ []))   = decodePatFlds fs >>= λ fs′ → just (recP fs′)
  decodePat _                                    = nothing

  decodePatFlds : List SExpr → Maybe (List (Name × Pat))
  decodePatFlds []                                   = just []
  decodePatFlds (list (sym "fld" ∷ str n ∷ p ∷ []) ∷ fs) = decodePat p >>= λ p′ → decodePatFlds fs >>= λ fs′ → just ((n , p′) ∷ fs′)
  decodePatFlds (_ ∷ _)                              = nothing

  decodePats : List SExpr → Maybe (List (Arg Pat))
  decodePats [] = just []
  decodePats (list (sym "arg" ∷ h ∷ l ∷ p ∷ []) ∷ ps) =
    decodeHid h >>= λ h′ → decodeLabel l >>= λ l′ → decodePat p >>= λ p′ → decodePats ps >>= λ ps′ → just (arg h′ l′ p′ ∷ ps′)
  decodePats (_ ∷ _) = nothing

  decodeLHS : SExpr → Maybe LHS
  decodeLHS (list (sym "head" ∷ f ∷ ps))          = decodeQ f >>= λ f′ → decodePats ps >>= λ ps′ → just (head f′ ps′)
  decodeLHS (list (sym "proj" ∷ d ∷ l ∷ ps))      = decodeQ d >>= λ d′ → decodeLHS l >>= λ l′ → decodePats ps >>= λ ps′ → just (proj d′ l′ ps′)
  decodeLHS (list (sym "with" ∷ l ∷ list ws ∷ list ps ∷ [])) =
    decodeLHS l >>= λ l′ → decodePats ws >>= λ ws′ → decodePats ps >>= λ ps′ → just (with′ l′ ws′ ps′)
  decodeLHS _ = nothing

  decodeRHS : SExpr → Maybe RHS
  decodeRHS (list (sym "rhs" ∷ e ∷ []))                      = decodeExpr e >>= λ e′ → just (rhs e′)
  decodeRHS (sym "absurdrhs")                                = just absurdRHS
  decodeRHS (list (sym "withrhs" ∷ list es ∷ list cs ∷ []))  = decodeExprs es >>= λ es′ → decodeClauses cs >>= λ cs′ → just (withRHS es′ cs′)
  decodeRHS (list (sym "rewriterhs" ∷ list es ∷ r ∷ []))     = decodeExprs es >>= λ es′ → decodeRHS r >>= λ r′ → just (rewriteRHS es′ r′)
  decodeRHS _ = nothing

  decodeClause : SExpr → Maybe Clause
  decodeClause (list (sym "clause" ∷ l ∷ r ∷ list (sym "where" ∷ ws) ∷ [])) =
    decodeLHS l >>= λ l′ → decodeRHS r >>= λ r′ → decodeDecls ws >>= λ ws′ → just (clause l′ r′ ws′)
  decodeClause _ = nothing

  decodeClauses : List SExpr → Maybe (List Clause)
  decodeClauses []       = just []
  decodeClauses (c ∷ cs) = decodeClause c >>= λ c′ → decodeClauses cs >>= λ cs′ → just (c′ ∷ cs′)

  -- 构造子 / 字段列表。Dump 会把构造子自己的 fixity 声明混在里面，这里挑出来放到后面
  decodeCons : String → List SExpr → Maybe (List (Name × Expr) × List Decl)
  decodeCons tag [] = just ([] , [])
  decodeCons tag (list (sym t ∷ str n ∷ e ∷ []) ∷ cs) with t ==ˢ tag
  ... | true  = decodeExpr e >>= λ e′ → decodeCons tag cs >>= λ r → just ((n , e′) ∷ proj₁ r , proj₂ r)
  ... | false = nothing
  decodeCons tag (list (sym "fixity" ∷ a ∷ num n ∷ str x ∷ []) ∷ cs) =
    decodeAssoc a >>= λ a′ → decodeCons tag cs >>= λ r → just (proj₁ r , fixity a′ n x ∷ proj₂ r)
  decodeCons tag (_ ∷ _) = nothing

  decodeVars : List SExpr → Maybe (List (Name × Expr))
  decodeVars []                                        = just []
  decodeVars (list (sym "var" ∷ str n ∷ e ∷ []) ∷ vs)  = decodeExpr e >>= λ e′ → decodeVars vs >>= λ vs′ → just ((n , e′) ∷ vs′)
  decodeVars (_ ∷ _)                                   = nothing

  -- 一条 s-expr 可能对应几条声明（datadef 带出的 fixity）
  decodeDecl : SExpr → Maybe (List Decl)
  decodeDecl (list (sym "pragma" ∷ str s ∷ []))        = just (pragma s ∷ [])
  decodeDecl (list (sym "import" ∷ m ∷ o ∷ d ∷ list (sym "assumes" ∷ as) ∷ [])) =
    decodeQ m >>= λ m′ → decodeOpen o >>= λ o′ → decodeDir d >>= λ d′ → decodeDecls as >>= λ as′ →
    just (import′ m′ o′ d′ as′ ∷ [])
    where
      decodeOpen : SExpr → Maybe Bool
      decodeOpen (sym "open")   = just true
      decodeOpen (sym "noopen") = just false
      decodeOpen _              = nothing
  decodeDecl (list (sym "open" ∷ m ∷ d ∷ []))           = decodeQ m >>= λ m′ → decodeDir d >>= λ d′ → just (open′ m′ d′ ∷ [])
  decodeDecl (list (sym "fixity" ∷ a ∷ num n ∷ str x ∷ [])) = decodeAssoc a >>= λ a′ → just (fixity a′ n x ∷ [])
  decodeDecl (list (sym "sig" ∷ m ∷ str x ∷ e ∷ []))    = decodeMods m >>= λ m′ → decodeExpr e >>= λ e′ → just (sig m′ x e′ ∷ [])
  decodeDecl (list (sym "fun" ∷ m ∷ str x ∷ cs))        = decodeMods m >>= λ m′ → decodeClauses cs >>= λ cs′ → just (fun m′ x cs′ ∷ [])
  decodeDecl (list (sym "datasig" ∷ m ∷ str x ∷ list (sym "params" ∷ bs) ∷ e ∷ [])) =
    decodeMods m >>= λ m′ → decodeBinds bs >>= λ bs′ → decodeExpr e >>= λ e′ → just (dataSig m′ x bs′ e′ ∷ [])
  decodeDecl (list (sym "datadef" ∷ m ∷ str x ∷ list ps ∷ cs)) =
    decodeMods m >>= λ m′ → decodeNames ps >>= λ ps′ → decodeCons "con" cs >>= λ r →
    just (dataDef m′ x ps′ (proj₁ r) ∷ proj₂ r)
  decodeDecl (list (sym "recsig" ∷ m ∷ str x ∷ list (sym "params" ∷ bs) ∷ e ∷ [])) =
    decodeMods m >>= λ m′ → decodeBinds bs >>= λ bs′ → decodeExpr e >>= λ e′ → just (recSig m′ x bs′ e′ ∷ [])
  decodeDecl (list (sym "recdef" ∷ m ∷ str x ∷ list ps ∷ list (sym "recdir" ∷ ind ∷ c ∷ []) ∷ fs)) =
    decodeMods m >>= λ m′ → decodeNames ps >>= λ ps′ → decodeInd ind >>= λ ind′ → decodeConstr c >>= λ c′ →
    decodeCons "field" fs >>= λ r → just (recDef m′ x ps′ (recDir ind′ c′) (proj₁ r) ∷ proj₂ r)
    where
      decodeInd : SExpr → Maybe Bool
      decodeInd (sym "coinductive") = just true
      decodeInd (sym "inductive")   = just false
      decodeInd _                   = nothing
      decodeConstr : SExpr → Maybe (Maybe Name)
      decodeConstr (sym "_") = just nothing
      decodeConstr (str c)   = just (just c)
      decodeConstr _         = nothing
  decodeDecl (list (sym "variable" ∷ vs))               = decodeVars vs >>= λ vs′ → just (variable′ vs′ ∷ [])
  decodeDecl (list (sym "module" ∷ str x ∷ list (sym "params" ∷ bs) ∷ ds)) =
    decodeBinds bs >>= λ bs′ → decodeDecls ds >>= λ ds′ → just (module′ x bs′ ds′ ∷ [])
  decodeDecl (list (sym "patsyn" ∷ str n ∷ list xs ∷ p ∷ [])) =
    decodeNames xs >>= λ ns → decodePat p >>= λ pat → just (patSyn n ns pat ∷ [])
  decodeDecl (list (sym "unsupported" ∷ str s ∷ []))   = just (unsupported s ∷ [])
  decodeDecl _ = nothing

  decodeDecls : List SExpr → Maybe (List Decl)
  decodeDecls []       = just []
  decodeDecls (d ∷ ds) = decodeDecl d >>= λ d′ → decodeDecls ds >>= λ ds′ → just (d′ ++ ds′)

------------------------------------------------------------------------
-- 顶层
------------------------------------------------------------------------

decodeCode : SExpr → Maybe Code
decodeCode (list (sym "module" ∷ m ∷ list (sym "params" ∷ bs) ∷ ds)) =
  decodeQ m >>= λ m′ → decodeBinds bs >>= λ bs′ → decodeDecls ds >>= λ ds′ → just (code m′ bs′ ds′)
decodeCode _ = nothing

parse : String → Maybe Code
parse s = parseSExpr s >>= decodeCode

------------------------------------------------------------------------
-- 搬运计划的 s-expr：
--   (plan "why" (new DECL*) (moves (move OBJ OBJ)*))
--   OBJ := (unit "C.x") | (ext "A.x") | flags | bot
-- new 里的 DECL 和文件里的一样（LLM 写一个只含新声明的小模块，Dump 一下，把它的声明搬进来）
------------------------------------------------------------------------

decodeObj : SExpr → Maybe Obj
decodeObj (list (sym "unit" ∷ q ∷ [])) = decodeQ q >>= λ q′ → just (unit q′)
decodeObj (list (sym "ext" ∷ q ∷ []))  = decodeQ q >>= λ q′ → just (ext q′)
decodeObj (sym "flags")                = just flags
decodeObj (sym "bot")                  = just ⊥
decodeObj _                            = nothing

decodeMoves : List SExpr → Maybe (List Proarrow)
decodeMoves []                                   = just []
decodeMoves (list (sym "move" ∷ a ∷ b ∷ []) ∷ ms) = decodeObj a >>= λ a′ → decodeObj b >>= λ b′ → decodeMoves ms >>= λ ms′ → just ((a′ ⇝ b′) ∷ ms′)
decodeMoves (_ ∷ _)                              = nothing

decodePlan : SExpr → Maybe Plan
decodePlan (list (sym "plan" ∷ str why ∷ list (sym "origin" ∷ q ∷ []) ∷ list (sym "new" ∷ ds) ∷ list (sym "moves" ∷ ms) ∷ [])) =
  decodeQ q >>= λ name → decodeDecls ds >>= λ ds′ → decodeMoves ms >>= λ ms′ → just (mkPlan why (just name) ds′ ms′)
decodePlan (list (sym "plan" ∷ str why ∷ list (sym "new" ∷ ds) ∷ list (sym "moves" ∷ ms) ∷ [])) =
  decodeDecls ds >>= λ ds′ → decodeMoves ms >>= λ ms′ → just (plan why ds′ ms′)
-- 也接受直接给一个 (module …)：它的声明（去掉 import/pragma 之外的头）就是 new
decodePlan (list (sym "plan" ∷ str why ∷ m ∷ list (sym "moves" ∷ ms) ∷ [])) =
  decodeCode m >>= λ c → decodeMoves ms >>= λ ms′ → just (mkPlan why (just (modName c)) (noHeader (decls c)) ms′)
  where
    -- 小模块自己的 import 只是为了能 scope check，不是新代码的一部分；它要改 import 的话用上面那种形式
    noHeader : List Decl → List Decl
    noHeader []                   = []
    noHeader (import′ _ _ _ _ ∷ ds) = noHeader ds
    noHeader (pragma _ ∷ ds)      = noHeader ds
    noHeader (d ∷ ds)             = d ∷ noHeader ds
decodePlan _ = nothing

parsePlan : String → Maybe Plan
parsePlan s = parseSExpr s >>= decodePlan

------------------------------------------------------------------------
-- 记忆与一串声明（存盘用，Code/Encode.agda 的逆）
------------------------------------------------------------------------

decodeMemory : SExpr → Maybe Memory
decodeMemory (list (sym "memory" ∷ es)) = go es
  where
    strs : List SExpr → Maybe (List String)
    strs []           = just []
    strs (str x ∷ xs) = strs xs >>= λ r → just (x ∷ r)
    strs (_ ∷ _)      = nothing
    go : List SExpr → Maybe Memory
    go []                                = just []
    go (list (sym "note" ∷ o ∷ ns) ∷ es) = decodeObj o >>= λ o′ → strs ns >>= λ ns′ → go es >>= λ r → just ((o′ , ns′) ∷ r)
    go (_ ∷ _)                           = nothing
decodeMemory _ = nothing

decodeDeclList : SExpr → Maybe (List Decl)
decodeDeclList (list (sym "decls" ∷ ds)) = decodeDecls ds
decodeDeclList _                         = nothing

parseMemory : String → Maybe Memory
parseMemory s = parseSExpr s >>= decodeMemory

parseDecls : String → Maybe (List Decl)
parseDecls s = parseSExpr s >>= decodeDeclList

open import Code.Lift
open import Code.Shape

decodeLift : SExpr → Maybe LiftSpec
decodeLift (list (sym "lift" ∷ b ∷ u ∷ list cs ∷ list es ∷ [])) =
  decodeQ b >>= λ b′ → decodeQ u >>= λ u′ → children cs >>= λ cs′ → ends es >>= λ es′ →
  just (liftSpecTree b′ u′ cs′ es′)
  where
    children : List SExpr → Maybe (List ChildLift)
    children [] = just []
    children (list (b ∷ u ∷ []) ∷ cs) = decodeQ b >>= λ b′ → decodeQ u >>= λ u′ → children cs >>= λ rs → just (mkChildLift b′ u′ nothing ∷ rs)
    children (list (b ∷ u ∷ sub ∷ []) ∷ cs) = decodeQ b >>= λ b′ → decodeQ u >>= λ u′ → decodeLift sub >>= λ sub′ →
      children cs >>= λ rs → just (mkChildLift b′ u′ (just sub′) ∷ rs)
    children _ = nothing
    refs : List SExpr → Maybe (List QName)
    refs [] = just []
    refs (r ∷ rs) = decodeQ r >>= λ r′ → refs rs >>= λ rs′ → just (r′ ∷ rs′)
    ends : List SExpr → Maybe (List EndpointLift)
    ends [] = just []
    ends (list (b ∷ u ∷ s ∷ []) ∷ es) = decodeQ b >>= λ b′ → decodeQ u >>= λ u′ → decodeQ s >>= λ s′ → ends es >>= λ rs → just (endpointLift b′ u′ s′ ∷ rs)
    ends (list (b ∷ u ∷ s ∷ list rs ∷ []) ∷ es) = decodeQ b >>= λ b′ → decodeQ u >>= λ u′ → decodeQ s >>= λ s′ →
      refs rs >>= λ rs′ → ends es >>= λ es′ → just (endpointLiftRefs b′ u′ s′ rs′ ∷ es′)
    ends _ = nothing
decodeLift _ = nothing

parseLift : String → Maybe LiftSpec
parseLift s = parseSExpr s >>= decodeLift

decodeShape : SExpr → Maybe HomeShape
decodeShape (list (sym "node" ∷ ks)) = kids ks >>= λ rs → just (node rs)
  where
    kids : List SExpr → Maybe (List (Name × HomeShape))
    kids [] = just []
    kids (list (str n ∷ sh ∷ []) ∷ ks) = decodeShape sh >>= λ sh′ → kids ks >>= λ rs → just ((n , sh′) ∷ rs)
    kids _ = nothing
decodeShape _ = nothing

parseShape : String → Maybe HomeShape
parseShape s = parseSExpr s >>= decodeShape
