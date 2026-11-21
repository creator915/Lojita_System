------------------------------------------------------------------------
-- Code.agda —— 一个 .agda 文件在 agda 世界里的样子
--
-- 这是"精简的 abstract"：照着 Agda.Syntax.Abstract 的骨架，去掉 Range、ScopeInfo、
-- NameId、concrete 副本这些"不是结构的东西"，留下结构。
-- 怎么从真实的 .agda 文件得到它：Code/Parse.agda（吃 Dump.hs 导出的 s-expr）。
-- 怎么把它写回去：Code/Render.agda。
--
-- 第二件事（§3）：把一个 Code 值看成一个范畴。
--
--   对象   Obj   = 本文件的单元 unit（一个名字下的几条声明：签名+子句、data、record、模块…）
--                + 别的文件暴露给我的名字 ext（孩子的接口；或语境库里的东西）
--                + flags（OPTIONS 语境）
--                + ⊥（形式对象：新代码从它来，丢弃的代码到它去）
--   箭头   u → v  当 u 用到 v（直接依赖）。范畴 = 这张图生成的自由范畴（或者说预序）。
--
-- 搬运（Code/Transport.agda）就是两个这样的范畴之间的 profunctor。
-- 这个文件只负责：类型、依赖图、接口、结构相等、重命名。
------------------------------------------------------------------------
module Code where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; foldr; length; reverse; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.String
open import Data.String using (String)
open import Data.Char using (Char)
open import Agda.Builtin.String using (primStringEquality)
open import Agda.Builtin.Char using (primCharEquality)

------------------------------------------------------------------------
-- §0  小工具：Bool 版的列表操作（stdlib 的 filter 要 Dec，这里只要 Bool）
------------------------------------------------------------------------

infix 8 _==ˢ_
_==ˢ_ : String → String → Bool
_==ˢ_ = primStringEquality

filterᵇ : ∀ {A : Set} → (A → Bool) → List A → List A
filterᵇ p []       = []
filterᵇ p (x ∷ xs) = if p x then x ∷ filterᵇ p xs else filterᵇ p xs

anyᵇ : ∀ {A : Set} → (A → Bool) → List A → Bool
anyᵇ p []       = false
anyᵇ p (x ∷ xs) = p x ∨ anyᵇ p xs

allᵇ : ∀ {A : Set} → (A → Bool) → List A → Bool
allᵇ p []       = true
allᵇ p (x ∷ xs) = p x ∧ allᵇ p xs

-- 去重，保留第一次出现（需要一个 Bool 相等）
nubᵇ : ∀ {A : Set} → (A → A → Bool) → List A → List A
nubᵇ eq = go []
  where
    go : List _ → List _ → List _
    go acc []       = reverse acc
    go acc (x ∷ xs) = if anyᵇ (eq x) acc then go acc xs else go (x ∷ acc) xs

elemᵇ : ∀ {A : Set} → (A → A → Bool) → A → List A → Bool
elemᵇ eq x = anyᵇ (eq x)

-- 两个列表按位相等
eqList : ∀ {A : Set} → (A → A → Bool) → List A → List A → Bool
eqList eq []       []       = true
eqList eq (x ∷ xs) (y ∷ ys) = eq x y ∧ eqList eq xs ys
eqList eq _        _        = false

eqMaybe : ∀ {A : Set} → (A → A → Bool) → Maybe A → Maybe A → Bool
eqMaybe eq nothing  nothing  = true
eqMaybe eq (just x) (just y) = eq x y
eqMaybe eq _        _        = false

eqBool : Bool → Bool → Bool
eqBool true  true  = true
eqBool false false = true
eqBool _     _     = false

------------------------------------------------------------------------
-- §1  名字
------------------------------------------------------------------------

Name : Set
Name = String

-- 一个限定名。
--   full  ：身份。A.ℕ.suc 存成 "A" ∷ "ℕ" ∷ "suc" ∷ []。范畴里的对象用它认。
--   shown ：源码里怎么写它（"A.suc"、"ℕ"、"_+_"）。只给 Render 用，不参与相等，
--           规范化哈希时剥掉——它是"这个文件此刻的作用域"留下的痕迹，不是结构。
record QName : Set where
  constructor scopedQName
  field
    full  : List Name
    shown : Name
    alternatives : List Name  -- Other canonical paths in the scoped overload set.
open QName public

qn : List Name → Name → QName
qn path spelling = scopedQName path spelling []

infix 8 _==ᴺ_
_==ᴺ_ : QName → QName → Bool
q ==ᴺ r = eqList _==ˢ_ (full q) (full r)

-- 由一段路径造一个名字：shown 取最后一段
mkQ : List Name → QName
mkQ xs = qn xs (last xs)
  where
    last : List Name → Name
    last []           = ""
    last (x ∷ [])     = x
    last (_ ∷ y ∷ ys) = last (y ∷ ys)

-- p 是 q 的前缀（含相等）
isPrefix : List Name → List Name → Bool
isPrefix []       _        = true
isPrefix (x ∷ xs) (y ∷ ys) = (x ==ˢ y) ∧ isPrefix xs ys
isPrefix (_ ∷ _)  []       = false

------------------------------------------------------------------------
-- §2  语法：Expr / Pat / Clause / Decl
------------------------------------------------------------------------

data Hiding : Set where
  visible hidden inst : Hiding      -- x  {x}  {{x}}

eqHiding : Hiding → Hiding → Bool
eqHiding visible visible = true
eqHiding hidden  hidden  = true
eqHiding inst    inst    = true
eqHiding _       _       = false

-- 一个参数：可见性 + 可选的名字（{x = e} 那种）+ 东西本身
record Arg (A : Set) : Set where
  constructor arg
  field
    hid    : Hiding
    label  : Maybe Name
    thing  : A
open Arg public

vis : ∀ {A : Set} → A → Arg A
vis = arg visible nothing

data Lit : Set where
  natL  : ℕ → Lit
  strL  : String → Lit
  charL : Char → Lit

eqLit : Lit → Lit → Bool
eqLit (natL m)  (natL n)  = m ≡ᵇ n
eqLit (strL s)  (strL t)  = s ==ˢ t
eqLit (charL c) (charL d) = primCharEquality c d
eqLit _         _         = false

-- 终止检查的标记：{-# NON_TERMINATING #-} / {-# TERMINATING #-}（abstract 里藏在 MutualInfo 里）
data TermCheck : Set where
  check nonTerminating terminating : TermCheck

eqTermCheck : TermCheck → TermCheck → Bool
eqTermCheck check          check          = true
eqTermCheck nonTerminating nonTerminating = true
eqTermCheck terminating    terminating    = true
eqTermCheck _              _              = false

-- 声明上的标记：对应 abstract 的 DefInfo 里的 Access / IsInstance / IsAbstract，加上终止检查的标记
record Mods : Set where
  constructor mods
  field
    isPrivate  : Bool
    isInstance : Bool
    isAbstract : Bool
    termCheck  : TermCheck
open Mods public

plain : Mods
plain = mods false false false check

eqMods : Mods → Mods → Bool
eqMods (mods a b c t) (mods a′ b′ c′ t′) = eqBool a a′ ∧ eqBool b b′ ∧ eqBool c c′ ∧ eqTermCheck t t′

-- import / open 后面的 using / hiding / renaming。照 abstract 的 ImportDirective。
--   dusing = nothing  ：没写 using（UseEverything）
--   dusing = just xs  ：using (xs)
record Directive : Set where
  constructor directive
  field
    dusing    : Maybe (List Name)
    dhiding   : List Name
    drenaming : List (Name × Name)        -- (from , to)
    dpublic   : Bool                      -- open … public
open Directive public

everything : Directive
everything = directive nothing [] [] false

eqPairs : List (Name × Name) → List (Name × Name) → Bool
eqPairs []             []               = true
eqPairs ((a , b) ∷ xs) ((a′ , b′) ∷ ys) = (a ==ˢ a′) ∧ (b ==ˢ b′) ∧ eqPairs xs ys
eqPairs _              _                = false

eqDirective : Directive → Directive → Bool
eqDirective (directive u h r p) (directive u′ h′ r′ p′) =
  eqMaybe (eqList _==ˢ_) u u′ ∧ eqList _==ˢ_ h h′ ∧ eqPairs r r′ ∧ eqBool p p′

data Assoc : Set where
  infixL infixR infixN : Assoc

eqAssoc : Assoc → Assoc → Bool
eqAssoc infixL infixL = true
eqAssoc infixR infixR = true
eqAssoc infixN infixN = true
eqAssoc _      _      = false

-- record 定义上的两个开关：是不是 coinductive、构造子叫什么
record RecDir : Set where
  constructor recDir
  field
    coind       : Bool
    constr      : Maybe Name
open RecDir public

eqRecDir : RecDir → RecDir → Bool
eqRecDir (recDir a c) (recDir a′ c′) = eqBool a a′ ∧ eqMaybe _==ˢ_ c c′

mutual
  -- 表达式。构造子名照 abstract；注释里是 Agda 源码里的样子。
  data Expr : Set where
    var       : Name → Expr                      -- x           绑定变量
    def       : QName → Expr                     -- f  r.proj   定义、投影、宏
    con       : QName → Expr                     -- c           构造子
    lit       : Lit → Expr                       -- 3  "s"  'c'
    set       : ℕ → Expr                         -- Set  Set₁  Set₂ …（Set ℓ 是 app (set 0) ℓ）
    hole      : Expr                             -- ?
    meta      : Expr                             -- _
    app       : Expr → Arg Expr → Expr           -- f x         多参数是嵌套：f x y = app (app f x) y
    lam       : Arg Name → Expr → Expr           -- λ x → e     λ {x} → e
    lamT      : Bind → Expr → Expr               -- λ (x : A) → e
    absurdLam : Hiding → Expr                    -- λ ()
    lamCase   : List Clause → Expr               -- λ where …   （abstract 的 ExtendedLam）
    pi        : Bind → Expr → Expr               -- (x y : A) → B
    fun′      : Arg Expr → Expr → Expr           -- A → B       不绑定
    let′      : List LetBind → Expr → Expr       -- let … in e
    rec′      : List (Name × Expr) → Expr        -- record { f = e ; … }
    recUpd    : Expr → List (Name × Expr) → Expr -- record r { f = e }
    dot       : Expr → Expr                      -- .e

  -- 一组带类型的绑定：(x y : A)  {x : A}  {{x : A}}
  data Bind : Set where
    bind : Hiding → List Name → Expr → Bind

  data Pat : Set where
    varP    : Name → Pat                         -- x
    conP    : QName → List (Arg Pat) → Pat       -- c p₁ … pₙ
    wildP   : Pat                                -- _
    litP    : Lit → Pat                          -- 3
    dotP    : Expr → Pat                         -- .e
    absurdP : Pat                                -- ()
    asP     : Name → Pat → Pat                   -- x@p
    projP   : QName → Pat                        -- .f   余模式里的投影（LHS 的模式列表里才出现）
    recP    : List (Name × Pat) → Pat            -- record { f = p }

  -- 子句左边。照 abstract 的 LHSCore。
  data LHS : Set where
    head  : QName → List (Arg Pat) → LHS                 -- f p₁ … pₙ
    proj  : QName → LHS → List (Arg Pat) → LHS           -- 余模式：(lhs) .field pats；写作 field lhs pats
    with′ : LHS → List (Arg Pat) → List (Arg Pat) → LHS  -- with 子句的左边：lhs | w₁ | w₂  pats

  data RHS : Set where
    rhs       : Expr → RHS                       -- = e
    absurdRHS : RHS                              -- 没有右边：左边有 ()
    withRHS   : List Expr → List Clause → RHS    -- with e₁ | e₂ ，接着一串子句
    rewriteRHS : List Expr → RHS → RHS           -- rewrite eq₁ | eq₂ ，然后是右边

  -- 一条子句：左边、右边、where 块
  data Clause : Set where
    clause : LHS → RHS → List Decl → Clause

  data LetBind : Set where
    letBind : Name → Expr → Expr → LetBind       -- let x : A = e （类型不写就是 meta）
    letPat  : Pat → Expr → LetBind               -- let (x , y) = e

  -- 声明。一个"单元"是同一个名字下的几条声明：sig+fun、dataSig+dataDef、recSig+recDef。
  data Decl : Set where
    pragma    : String → Decl                                        -- {-# OPTIONS … #-} 等，原文
    import′   : QName → Bool → Directive → List Decl → Decl          -- import M；是否 open；using/hiding；
                                                                     -- 最后一项：我假设 M 暴露的接口（孩子的规约）。语境库的话为空
    open′     : QName → Directive → Decl                             -- open M （本地模块）
    fixity    : Assoc → ℕ → Name → Decl                              -- infixl 6 _+_
    sig       : Mods → Name → Expr → Decl                            -- f : A           （abstract 的 Axiom）
    fun       : Mods → Name → List Clause → Decl                     -- f p = e ; …     （FunDef）
    dataSig   : Mods → Name → List Bind → Expr → Decl                -- data D (A : Set) : Set
    dataDef   : Mods → Name → List Name → List (Name × Expr) → Decl  -- data D A where c : …
    recSig    : Mods → Name → List Bind → Expr → Decl                -- record R (A : Set) : Set
    recDef    : Mods → Name → List Name → RecDir → List (Name × Expr) → Decl  -- record R A where field f : …
    variable′ : List (Name × Expr) → Decl                            -- variable A B : Set
    module′   : Name → List Bind → List Decl → Decl                  -- module M (x : A) where …
    patSyn : Name → List Name → Pat → Decl
    unsupported : String → Decl                                      -- 这版还不认识的声明，原样记一笔（render 成注释）

-- 顶层：一个文件 = 一个模块
record Code : Set where
  constructor code
  field
    modName : QName          -- 顶层模块名；full 是模块路径（"Data" ∷ "Nat" ∷ []）
    params  : List Bind
    decls   : List Decl
open Code public

------------------------------------------------------------------------
-- §2.1  结构相等
-- 不比 shown，不比 Arg 的 label 以外的打印信息。这是"规范化哈希"看的那份结构。
------------------------------------------------------------------------

eqArg : ∀ {A : Set} → (A → A → Bool) → Arg A → Arg A → Bool
eqArg eq (arg h l x) (arg h′ l′ x′) = eqHiding h h′ ∧ eqMaybe _==ˢ_ l l′ ∧ eq x x′

mutual
  eqExpr : Expr → Expr → Bool
  eqExpr (var x)       (var y)         = x ==ˢ y
  eqExpr (def q)       (def r)         = q ==ᴺ r
  eqExpr (con q)       (con r)         = q ==ᴺ r
  eqExpr (lit l)       (lit m)         = eqLit l m
  eqExpr (set n)       (set m)         = n ≡ᵇ m
  eqExpr hole          hole            = true
  eqExpr meta          meta            = true
  eqExpr (app f a)     (app g b)       = eqExpr f g ∧ eqArgE a b
  eqExpr (lam x e)     (lam y e′)      = eqArg _==ˢ_ x y ∧ eqExpr e e′
  eqExpr (lamT b e)    (lamT b′ e′)    = eqBind b b′ ∧ eqExpr e e′
  eqExpr (absurdLam h) (absurdLam h′)  = eqHiding h h′
  eqExpr (lamCase cs)  (lamCase cs′)   = eqClauses cs cs′
  eqExpr (pi b e)      (pi b′ e′)      = eqBind b b′ ∧ eqExpr e e′
  eqExpr (fun′ a e)    (fun′ a′ e′)    = eqArgE a a′ ∧ eqExpr e e′
  eqExpr (let′ bs e)   (let′ bs′ e′)   = eqLetBinds bs bs′ ∧ eqExpr e e′
  eqExpr (rec′ fs)     (rec′ fs′)      = eqFields fs fs′
  eqExpr (recUpd r fs) (recUpd r′ fs′) = eqExpr r r′ ∧ eqFields fs fs′
  eqExpr (dot e)       (dot e′)        = eqExpr e e′
  eqExpr _             _               = false

  eqArgE : Arg Expr → Arg Expr → Bool
  eqArgE (arg h l x) (arg h′ l′ x′) = eqHiding h h′ ∧ eqMaybe _==ˢ_ l l′ ∧ eqExpr x x′

  eqFields : List (Name × Expr) → List (Name × Expr) → Bool
  eqFields []             []               = true
  eqFields ((n , e) ∷ fs) ((n′ , e′) ∷ fs′) = (n ==ˢ n′) ∧ eqExpr e e′ ∧ eqFields fs fs′
  eqFields _              _                = false

  eqBind : Bind → Bind → Bool
  eqBind (bind h xs e) (bind h′ xs′ e′) = eqHiding h h′ ∧ eqList _==ˢ_ xs xs′ ∧ eqExpr e e′

  eqBinds : List Bind → List Bind → Bool
  eqBinds []       []         = true
  eqBinds (b ∷ bs) (b′ ∷ bs′) = eqBind b b′ ∧ eqBinds bs bs′
  eqBinds _        _          = false

  eqPat : Pat → Pat → Bool
  eqPat (varP x)    (varP y)     = x ==ˢ y
  eqPat (conP q ps) (conP r ps′) = q ==ᴺ r ∧ eqPats ps ps′
  eqPat wildP       wildP        = true
  eqPat (litP l)    (litP m)     = eqLit l m
  eqPat (dotP e)    (dotP e′)    = eqExpr e e′
  eqPat absurdP     absurdP      = true
  eqPat (asP x p)   (asP y p′)   = (x ==ˢ y) ∧ eqPat p p′
  eqPat (projP q)   (projP r)    = q ==ᴺ r
  eqPat (recP fs)   (recP fs′)   = eqPatFields fs fs′
  eqPat _           _            = false

  eqPatFields : List (Name × Pat) → List (Name × Pat) → Bool
  eqPatFields []             []               = true
  eqPatFields ((n , p) ∷ fs) ((n′ , p′) ∷ fs′) = (n ==ˢ n′) ∧ eqPat p p′ ∧ eqPatFields fs fs′
  eqPatFields _              _                = false

  eqPats : List (Arg Pat) → List (Arg Pat) → Bool
  eqPats []       []         = true
  eqPats (arg h l p ∷ ps) (arg h′ l′ p′ ∷ ps′) = eqHiding h h′ ∧ eqMaybe _==ˢ_ l l′ ∧ eqPat p p′ ∧ eqPats ps ps′
  eqPats _        _          = false

  eqLHS : LHS → LHS → Bool
  eqLHS (head f ps)     (head g ps′)       = f ==ᴺ g ∧ eqPats ps ps′
  eqLHS (proj f l ps)   (proj g l′ ps′)    = f ==ᴺ g ∧ eqLHS l l′ ∧ eqPats ps ps′
  eqLHS (with′ l ws ps) (with′ l′ ws′ ps′) = eqLHS l l′ ∧ eqPats ws ws′ ∧ eqPats ps ps′
  eqLHS _               _                  = false

  eqRHS : RHS → RHS → Bool
  eqRHS (rhs e)        (rhs e′)         = eqExpr e e′
  eqRHS absurdRHS      absurdRHS        = true
  eqRHS (withRHS es cs) (withRHS es′ cs′) = eqExprs es es′ ∧ eqClauses cs cs′
  eqRHS (rewriteRHS es r) (rewriteRHS es′ r′) = eqExprs es es′ ∧ eqRHS r r′
  eqRHS _              _                = false

  eqExprs : List Expr → List Expr → Bool
  eqExprs []       []         = true
  eqExprs (e ∷ es) (e′ ∷ es′) = eqExpr e e′ ∧ eqExprs es es′
  eqExprs _        _          = false

  eqClause : Clause → Clause → Bool
  eqClause (clause l r w) (clause l′ r′ w′) = eqLHS l l′ ∧ eqRHS r r′ ∧ eqDecls w w′

  eqClauses : List Clause → List Clause → Bool
  eqClauses []       []         = true
  eqClauses (c ∷ cs) (c′ ∷ cs′) = eqClause c c′ ∧ eqClauses cs cs′
  eqClauses _        _          = false

  eqLetBind : LetBind → LetBind → Bool
  eqLetBind (letBind x t e) (letBind y t′ e′) = (x ==ˢ y) ∧ eqExpr t t′ ∧ eqExpr e e′
  eqLetBind (letPat p e)    (letPat p′ e′)    = eqPat p p′ ∧ eqExpr e e′
  eqLetBind _               _                 = false

  eqLetBinds : List LetBind → List LetBind → Bool
  eqLetBinds []       []         = true
  eqLetBinds (b ∷ bs) (b′ ∷ bs′) = eqLetBind b b′ ∧ eqLetBinds bs bs′
  eqLetBinds _        _          = false

  eqDecl : Decl → Decl → Bool
  eqDecl (pragma s)            (pragma t)                = s ==ˢ t
  eqDecl (import′ m o d i)     (import′ m′ o′ d′ i′)     = m ==ᴺ m′ ∧ eqBool o o′ ∧ eqDirective d d′ ∧ eqDecls i i′
  eqDecl (open′ m d)           (open′ m′ d′)             = m ==ᴺ m′ ∧ eqDirective d d′
  eqDecl (fixity a n x)        (fixity a′ n′ x′)         = eqAssoc a a′ ∧ (n ≡ᵇ n′) ∧ (x ==ˢ x′)
  eqDecl (sig m x e)           (sig m′ x′ e′)            = eqMods m m′ ∧ (x ==ˢ x′) ∧ eqExpr e e′
  eqDecl (fun m x cs)          (fun m′ x′ cs′)           = eqMods m m′ ∧ (x ==ˢ x′) ∧ eqClauses cs cs′
  eqDecl (dataSig m x bs e)    (dataSig m′ x′ bs′ e′)    = eqMods m m′ ∧ (x ==ˢ x′) ∧ eqBinds bs bs′ ∧ eqExpr e e′
  eqDecl (dataDef m x ps cs)   (dataDef m′ x′ ps′ cs′)   = eqMods m m′ ∧ (x ==ˢ x′) ∧ eqList _==ˢ_ ps ps′ ∧ eqFields cs cs′
  eqDecl (recSig m x bs e)     (recSig m′ x′ bs′ e′)     = eqMods m m′ ∧ (x ==ˢ x′) ∧ eqBinds bs bs′ ∧ eqExpr e e′
  eqDecl (recDef m x ps d fs)  (recDef m′ x′ ps′ d′ fs′) = eqMods m m′ ∧ (x ==ˢ x′) ∧ eqList _==ˢ_ ps ps′ ∧ eqRecDir d d′ ∧ eqFields fs fs′
  eqDecl (variable′ vs)        (variable′ vs′)           = eqFields vs vs′
  eqDecl (module′ x bs ds)     (module′ x′ bs′ ds′)      = (x ==ˢ x′) ∧ eqBinds bs bs′ ∧ eqDecls ds ds′
  eqDecl (patSyn n xs p) (patSyn m ys q) = n ==ˢ m ∧ eqList _==ˢ_ xs ys ∧ eqPat p q
  eqDecl (unsupported s)       (unsupported t)           = s ==ˢ t
  eqDecl _                     _                         = false

  eqDecls : List Decl → List Decl → Bool
  eqDecls []       []         = true
  eqDecls (d ∷ ds) (d′ ∷ ds′) = eqDecl d d′ ∧ eqDecls ds ds′
  eqDecls _        _          = false

eqCode : Code → Code → Bool
eqCode (code m ps ds) (code m′ ps′ ds′) = m ==ᴺ m′ ∧ eqBinds ps ps′ ∧ eqDecls ds ds′

-- Parent-supplied child interfaces live only on top-level import edges.
-- The official frontend leaves those edges empty when it scopes a surface.
surfaceCode : Code → Code
surfaceCode (code m ps ds) = code m ps (map scopeDecl ds)
  where
    scopeDecl : Decl → Decl
    scopeDecl (import′ q o d a) = import′ q o d []
    scopeDecl d = d

authoredPoint : List (Code × String) → Code → Maybe (Code × String)
authoredPoint views c = lookup views (surfaceCode c)
  where
    lookup : List (Code × String) → Code → Maybe (Code × String)
    lookup [] scoped = nothing
    lookup ((ir , src) ∷ rest) scoped = if eqCode ir scoped then just (ir , src) else lookup rest scoped

authoredSurface : List (Code × String) → Code → Maybe String
authoredSurface views c with authoredPoint views c
... | just (ir , src) = just src
... | nothing = nothing


------------------------------------------------------------------------
-- §2.2  重命名：把树上每个 QName 过一遍函数。搬运里"把 old 名字换成 new 名字"用它。
-- 只动引用（def/con/conP/proj/head），不动定义处的 Name——定义处由搬运直接换声明。
------------------------------------------------------------------------

mutual
  renameExpr : (QName → QName) → Expr → Expr
  renameExpr ρ (var x)        = var x
  renameExpr ρ (def q)        = def (ρ q)
  renameExpr ρ (con q)        = con (ρ q)
  renameExpr ρ (lit l)        = lit l
  renameExpr ρ (set n)        = set n
  renameExpr ρ hole           = hole
  renameExpr ρ meta           = meta
  renameExpr ρ (app f a)      = app (renameExpr ρ f) (renameArg ρ a)
  renameExpr ρ (lam x e)      = lam x (renameExpr ρ e)
  renameExpr ρ (lamT b e)     = lamT (renameBind ρ b) (renameExpr ρ e)
  renameExpr ρ (absurdLam h)  = absurdLam h
  renameExpr ρ (lamCase cs)   = lamCase (renameClauses ρ cs)
  renameExpr ρ (pi b e)       = pi (renameBind ρ b) (renameExpr ρ e)
  renameExpr ρ (fun′ a e)     = fun′ (renameArg ρ a) (renameExpr ρ e)
  renameExpr ρ (let′ bs e)    = let′ (renameLetBinds ρ bs) (renameExpr ρ e)
  renameExpr ρ (rec′ fs)      = rec′ (renameFields ρ fs)
  renameExpr ρ (recUpd r fs)  = recUpd (renameExpr ρ r) (renameFields ρ fs)
  renameExpr ρ (dot e)        = dot (renameExpr ρ e)

  renameArg : (QName → QName) → Arg Expr → Arg Expr
  renameArg ρ (arg h l e) = arg h l (renameExpr ρ e)

  renameFields : (QName → QName) → List (Name × Expr) → List (Name × Expr)
  renameFields ρ []             = []
  renameFields ρ ((n , e) ∷ fs) = (n , renameExpr ρ e) ∷ renameFields ρ fs

  renameBind : (QName → QName) → Bind → Bind
  renameBind ρ (bind h xs e) = bind h xs (renameExpr ρ e)

  renameBinds : (QName → QName) → List Bind → List Bind
  renameBinds ρ []       = []
  renameBinds ρ (b ∷ bs) = renameBind ρ b ∷ renameBinds ρ bs

  renamePat : (QName → QName) → Pat → Pat
  renamePat ρ (varP x)    = varP x
  renamePat ρ (conP q ps) = conP (ρ q) (renamePats ρ ps)
  renamePat ρ wildP       = wildP
  renamePat ρ (litP l)    = litP l
  renamePat ρ (dotP e)    = dotP (renameExpr ρ e)
  renamePat ρ absurdP     = absurdP
  renamePat ρ (asP x p)   = asP x (renamePat ρ p)
  renamePat ρ (projP q)   = projP (ρ q)
  renamePat ρ (recP fs)   = recP (renamePatFields ρ fs)

  renamePatFields : (QName → QName) → List (Name × Pat) → List (Name × Pat)
  renamePatFields ρ []             = []
  renamePatFields ρ ((n , p) ∷ fs) = (n , renamePat ρ p) ∷ renamePatFields ρ fs

  renamePats : (QName → QName) → List (Arg Pat) → List (Arg Pat)
  renamePats ρ []               = []
  renamePats ρ (arg h l p ∷ ps) = arg h l (renamePat ρ p) ∷ renamePats ρ ps

  renameLHS : (QName → QName) → LHS → LHS
  renameLHS ρ (head f ps)     = head (ρ f) (renamePats ρ ps)
  renameLHS ρ (proj f l ps)   = proj (ρ f) (renameLHS ρ l) (renamePats ρ ps)
  renameLHS ρ (with′ l ws ps) = with′ (renameLHS ρ l) (renamePats ρ ws) (renamePats ρ ps)

  renameRHS : (QName → QName) → RHS → RHS
  renameRHS ρ (rhs e)         = rhs (renameExpr ρ e)
  renameRHS ρ absurdRHS       = absurdRHS
  renameRHS ρ (withRHS es cs) = withRHS (renameExprs ρ es) (renameClauses ρ cs)
  renameRHS ρ (rewriteRHS es r) = rewriteRHS (renameExprs ρ es) (renameRHS ρ r)

  renameExprs : (QName → QName) → List Expr → List Expr
  renameExprs ρ []       = []
  renameExprs ρ (e ∷ es) = renameExpr ρ e ∷ renameExprs ρ es

  renameClause : (QName → QName) → Clause → Clause
  renameClause ρ (clause l r w) = clause (renameLHS ρ l) (renameRHS ρ r) (renameDecls ρ w)

  renameClauses : (QName → QName) → List Clause → List Clause
  renameClauses ρ []       = []
  renameClauses ρ (c ∷ cs) = renameClause ρ c ∷ renameClauses ρ cs

  renameLetBind : (QName → QName) → LetBind → LetBind
  renameLetBind ρ (letBind x t e) = letBind x (renameExpr ρ t) (renameExpr ρ e)
  renameLetBind ρ (letPat p e)    = letPat (renamePat ρ p) (renameExpr ρ e)

  renameLetBinds : (QName → QName) → List LetBind → List LetBind
  renameLetBinds ρ []       = []
  renameLetBinds ρ (b ∷ bs) = renameLetBind ρ b ∷ renameLetBinds ρ bs

  renameDecl : (QName → QName) → Decl → Decl
  renameDecl ρ (pragma s)           = pragma s
  renameDecl ρ (import′ m o d i)    = import′ m o d (renameDecls ρ i)
  renameDecl ρ (open′ m d)          = open′ m d
  renameDecl ρ (fixity a n x)       = fixity a n x
  renameDecl ρ (sig m x e)          = sig m x (renameExpr ρ e)
  renameDecl ρ (fun m x cs)         = fun m x (renameClauses ρ cs)
  renameDecl ρ (dataSig m x bs e)   = dataSig m x (renameBinds ρ bs) (renameExpr ρ e)
  renameDecl ρ (dataDef m x ps cs)  = dataDef m x ps (renameFields ρ cs)
  renameDecl ρ (recSig m x bs e)    = recSig m x (renameBinds ρ bs) (renameExpr ρ e)
  renameDecl ρ (recDef m x ps d fs) = recDef m x ps d (renameFields ρ fs)
  renameDecl ρ (variable′ vs)       = variable′ (renameFields ρ vs)
  renameDecl ρ (module′ x bs ds)    = module′ x (renameBinds ρ bs) (renameDecls ρ ds)
  renameDecl ρ (patSyn n xs p) = patSyn n xs (renamePat ρ p)
  renameDecl ρ (unsupported s)      = unsupported s

  renameDecls : (QName → QName) → List Decl → List Decl
  renameDecls ρ []       = []
  renameDecls ρ (d ∷ ds) = renameDecl ρ d ∷ renameDecls ρ ds

renameCode : (QName → QName) → Code → Code
renameCode ρ (code m ps ds) = code m (renameBinds ρ ps) (renameDecls ρ ds)

------------------------------------------------------------------------
-- §2.3  引用：树上出现了哪些 QName（def/con/conP/proj/head）
-- 这是依赖图的原料。where 块、with 子句里的引用一起收，它们属于外面那个单元。
------------------------------------------------------------------------

mutual
  refsExpr : Expr → List QName
  refsExpr (var x)        = []
  refsExpr (def q)        = q ∷ []
  refsExpr (con q)        = q ∷ []
  refsExpr (lit l)        = []
  refsExpr (set n)        = []
  refsExpr hole           = []
  refsExpr meta           = []
  refsExpr (app f (arg _ _ a)) = refsExpr f ++ refsExpr a
  refsExpr (lam x e)      = refsExpr e
  refsExpr (lamT b e)     = refsBind b ++ refsExpr e
  refsExpr (absurdLam h)  = []
  refsExpr (lamCase cs)   = refsClauses cs
  refsExpr (pi b e)       = refsBind b ++ refsExpr e
  refsExpr (fun′ (arg _ _ a) e) = refsExpr a ++ refsExpr e
  refsExpr (let′ bs e)    = refsLetBinds bs ++ refsExpr e
  refsExpr (rec′ fs)      = refsFields fs
  refsExpr (recUpd r fs)  = refsExpr r ++ refsFields fs
  refsExpr (dot e)        = refsExpr e

  refsFields : List (Name × Expr) → List QName
  refsFields []             = []
  refsFields ((_ , e) ∷ fs) = refsExpr e ++ refsFields fs

  refsBind : Bind → List QName
  refsBind (bind _ _ e) = refsExpr e

  refsBinds : List Bind → List QName
  refsBinds []       = []
  refsBinds (b ∷ bs) = refsBind b ++ refsBinds bs

  refsPat : Pat → List QName
  refsPat (varP x)    = []
  refsPat (conP q ps) = q ∷ refsPats ps
  refsPat wildP       = []
  refsPat (litP l)    = []
  refsPat (dotP e)    = refsExpr e
  refsPat absurdP     = []
  refsPat (asP x p)   = refsPat p
  refsPat (projP q)   = q ∷ []
  refsPat (recP fs)   = refsPatFields fs

  refsPatFields : List (Name × Pat) → List QName
  refsPatFields []             = []
  refsPatFields ((_ , p) ∷ fs) = refsPat p ++ refsPatFields fs

  refsPats : List (Arg Pat) → List QName
  refsPats []       = []
  refsPats (arg _ _ p ∷ ps) = refsPat p ++ refsPats ps

  -- 左边：head 的函数名是"自己"，不算引用；proj 的投影名算
  refsLHS : LHS → List QName
  refsLHS (head f ps)     = refsPats ps
  refsLHS (proj f l ps)   = f ∷ refsLHS l ++ refsPats ps
  refsLHS (with′ l ws ps) = refsLHS l ++ refsPats ws ++ refsPats ps

  refsRHS : RHS → List QName
  refsRHS (rhs e)         = refsExpr e
  refsRHS absurdRHS       = []
  refsRHS (withRHS es cs) = refsExprs es ++ refsClauses cs
  refsRHS (rewriteRHS es r) = refsExprs es ++ refsRHS r

  refsExprs : List Expr → List QName
  refsExprs []       = []
  refsExprs (e ∷ es) = refsExpr e ++ refsExprs es

  refsClause : Clause → List QName
  refsClause (clause l r w) = refsLHS l ++ refsRHS r ++ refsDecls w

  refsClauses : List Clause → List QName
  refsClauses []       = []
  refsClauses (c ∷ cs) = refsClause c ++ refsClauses cs

  refsLetBind : LetBind → List QName
  refsLetBind (letBind x t e) = refsExpr t ++ refsExpr e
  refsLetBind (letPat p e)    = refsPat p ++ refsExpr e

  refsLetBinds : List LetBind → List QName
  refsLetBinds []       = []
  refsLetBinds (b ∷ bs) = refsLetBind b ++ refsLetBinds bs

  refsDecl : Decl → List QName
  refsDecl (pragma s)           = []
  refsDecl (import′ m o d i)    = []            -- 接口里的签名引用的是别处的名字，不算本文件的依赖
  refsDecl (open′ m d)          = []
  refsDecl (fixity a n x)       = []
  refsDecl (sig m x e)          = refsExpr e
  refsDecl (fun m x cs)         = refsClauses cs
  refsDecl (dataSig m x bs e)   = refsBinds bs ++ refsExpr e
  refsDecl (dataDef m x ps cs)  = refsFields cs
  refsDecl (recSig m x bs e)    = refsBinds bs ++ refsExpr e
  refsDecl (recDef m x ps d fs) = refsFields fs
  refsDecl (variable′ vs)       = refsFields vs
  refsDecl (module′ x bs ds)    = refsBinds bs ++ refsDecls ds
  refsDecl (patSyn n xs p) = refsPat p
  refsDecl (unsupported s)      = []

  refsDecls : List Decl → List QName
  refsDecls []       = []
  refsDecls (d ∷ ds) = refsDecl d ++ refsDecls ds

------------------------------------------------------------------------
-- §3  把一个 Code 看成范畴
------------------------------------------------------------------------

-- 对象
data Obj : Set where
  unit  : QName → Obj      -- 本文件的一个单元
  ext   : QName → Obj      -- 别的文件暴露给我的一个名字
  flags : Obj              -- OPTIONS 语境：所有单元作为整体依赖它
  ⊥     : Obj              -- 形式对象。新代码从它来，丢弃的代码到它去。
                           -- 它没有接口：到它去 = 接口全丢（依赖者得搬）；从它来 = 什么也没破坏。

infix 8 _==ᴼ_
_==ᴼ_ : Obj → Obj → Bool
unit q ==ᴼ unit r = q ==ᴺ r
ext q  ==ᴼ ext r  = q ==ᴺ r
flags  ==ᴼ flags  = true
⊥      ==ᴼ ⊥      = true
_      ==ᴼ _      = false

-- 一个单元：名字 + 它那几条声明（已经在某个模块路径下）
record Unit : Set where
  constructor unitOf
  field
    uname  : QName
    udecls : List Decl
open Unit public

inUnitScope : Unit → Name → QName → Bool
inUnitScope u n q = eqList _==ˢ_ (full q) (init (full (uname u)) ++ [ n ])
  where
    init : List Name → List Name
    init []           = []
    init (_ ∷ [])     = []
    init (x ∷ y ∷ xs) = x ∷ init (y ∷ xs)

-- Data constructors and record fields live under the unit's name, but a
-- named record constructor lives in the record's enclosing module.
unitOwns : Unit → QName → Bool
unitOwns u q = isPrefix (full (uname u)) (full q) ∨ anyᵇ ownsConstructor (udecls u)
  where
    ownsConstructor : Decl → Bool
    ownsConstructor (recDef _ _ _ (recDir _ (just c)) _) = inUnitScope u c q
    ownsConstructor _ = false

-- 一条声明定义了哪个（本地）名字；pragma/import/open/fixity 没有名字
declName : Decl → Maybe Name
declName (pragma _)            = nothing
declName (import′ _ _ _ _)     = nothing
declName (open′ _ _)           = nothing
declName (fixity _ _ _)        = nothing
declName (sig _ x _)           = just x
declName (fun _ x _)           = just x
declName (dataSig _ x _ _)     = just x
declName (dataDef _ x _ _)     = just x
declName (recSig _ x _ _)      = just x
declName (recDef _ x _ _ _)    = just x
declName (variable′ _)         = nothing
declName (module′ x _ _)       = just x
declName (patSyn n _ _) = just n
declName (unsupported _)       = nothing

-- 匿名定义（_ : T ; _ = refl，测试常这么写）每一对各成一个单元，内部编号 _#0 _#1 …；
-- 这个编号只在 full 里，声明处的名字还是 _，render 不受影响。
unitsIn : List Name → List Decl → List Unit
unitsIn path ds = go ds 0 []
  where
    addTo : QName → Decl → List Unit → List Unit
    addTo q d [] = unitOf q (d ∷ []) ∷ []
    addTo q d (u ∷ us) = if uname u ==ᴺ q then unitOf q (udecls u ++ (d ∷ [])) ∷ us else u ∷ addTo q d us

    varUnits : List (Name × Expr) → List Unit → List Unit
    varUnits []             acc = acc
    varUnits ((x , e) ∷ vs) acc = varUnits vs (addTo (mkQ (path ++ (x ∷ []))) (sig plain x e) acc)

    -- 匿名单元的内部名字：_#0 _#1 …。不能就叫 _：where 块的模块段也叫 _（C._.helper），
    -- 按前缀解析时会把 where 里的局部名字错认成匿名单元
    anonName : ℕ → Name
    anonName n = Data.String._++_ "_#" (ℕshow.show n)
      where import Data.Nat.Show as ℕshow

    isSig : Decl → Bool
    isSig (sig _ _ _) = true
    isSig _           = false

    -- k：已经见过几个匿名签名；匿名的 fun 挂到最近那个匿名签名上
    go : List Decl → ℕ → List Unit → List Unit
    go []       k acc = acc
    go (d ∷ ds) k acc with declName d
    ... | nothing with d
    ...   | variable′ vs = go ds k (varUnits vs acc)
    ...   | _            = go ds k acc
    go (d ∷ ds) k acc | just x with x ==ˢ "_"
    ... | true  = if isSig d then go ds (suc k) (addTo (mkQ (path ++ (anonName k ∷ []))) d acc)
                              else go ds k (addTo (mkQ (path ++ (anonName (pred k) ∷ []))) d acc)
      where
        pred : ℕ → ℕ
        pred zero    = zero
        pred (suc n) = n
    ... | false with d
    ...   | module′ x′ bs sub = go ds k (addTo (mkQ (path ++ (x ∷ []))) d acc ++ unitsIn (path ++ (x ∷ [])) sub)
    ...   | _                 = go ds k (addTo (mkQ (path ++ (x ∷ []))) d acc)

units : Code → List Unit
units c = unitsIn (full (modName c)) (decls c)

-- 导入：每条 import 带着"我假设它暴露的接口"。接口本身是一串声明（签名、带构造子的 data …），
-- 所以孩子从父亲看来就是一个只有签名的模块——一个 postulate 块。
record Import : Set where
  constructor importOf
  field
    imod   : QName
    iopen  : Bool
    idir   : Directive
    assumes : List Decl
open Import public

imports : Code → List Import
imports c = go (decls c)
  where
    go : List Decl → List Import
    go []                     = []
    go (import′ m o d i ∷ ds) = importOf m o d i ∷ go ds
    go (_ ∷ ds)               = go ds

-- 孩子接口里的对象：按前缀解析。A.ℕ.suc 落到接口里的 A.ℕ 上（构造子归它的 data）
extUnits : Code → List Unit
extUnits c = concatMap (λ i → unitsIn (full (imod i)) (assumes i)) (imports c)

-- OPTIONS 里的 flag
flagsOf : Code → List String
flagsOf c = concatMap optionsOf (decls c)
  where
    optionsOf : Decl → List String
    optionsOf (pragma s) with Data.String.words s
    ... | "OPTIONS" ∷ fs = fs
    ... | _ = []
    optionsOf _ = []

-- 把一个引用解析成对象：
--   本文件某个单元名的前缀下   → unit（最长匹配：D.c 落到 D，M.f 落到 M.f 而不是 M）
--   record 的同层构造子名      → unit（M.c 落到 M.R）
--   某条 import 接口里的名字   → ext（孩子暴露的）
--   别的、不在本模块路径下的名字 → ext 整个名字（语境库里的东西）
--   本模块路径下但不是单元的    → nothing（where 里的局部定义、模式变量等）
longestUnit : List Unit → Maybe Unit
longestUnit [] = nothing
longestUnit (u ∷ us) with longestUnit us
... | nothing = just u
... | just v = just (if length (full (uname u)) <ᵇ length (full (uname v)) then v else u)

-- resolveIn：单元表和外部单元表预先算好传进来（一个文件只算一次，别每个引用重算一遍）
resolveIn : QName → List Unit → List Unit → QName → Maybe Obj
resolveIn top us es q = pick (longestUnit (filterᵇ (λ u → unitOwns u q) us))
  where
    pick : Maybe Unit → Maybe Obj
    pick (just u) = if full (uname u) ==ᴸ full top then nothing else just (unit (uname u))
      where
        _==ᴸ_ : List Name → List Name → Bool
        _==ᴸ_ = eqList _==ˢ_
    pick nothing with longestUnit (filterᵇ (λ u → unitOwns u q) es)
    ... | just u  = just (ext (uname u))
    ... | nothing = if isPrefix (full top) (full q) then nothing else just (ext q)

resolve : Code → QName → Maybe Obj
resolve c = resolveIn (modName c) (units c) (extUnits c)

-- 一个单元直接依赖的对象（去重，去掉自己）。每个单元还形式地依赖 flags。
depsOfIn : QName → List Unit → List Unit → Unit → List Obj
depsOfIn top us es u = nubᵇ _==ᴼ_ (filterᵇ (λ o → not (o ==ᴼ unit (uname u))) (resolveAll (refsDecls (udecls u)))) ++ (flags ∷ [])
  where
    resolveAll : List QName → List Obj
    resolveAll []       = []
    resolveAll (q ∷ qs) with resolveIn top us es q
    ... | just o  = o ∷ resolveAll qs
    ... | nothing = resolveAll qs

depsOf : Code → Unit → List Obj
depsOf c = depsOfIn (modName c) (units c) (extUnits c)

-- 生成图：所有箭头 (u , v)，读作 u 用到 v
arrowsIn : QName → List Unit → List Unit → List (Obj × Obj)
arrowsIn top us es = concatMap (λ u → map (λ v → unit (uname u) , v) (depsOfIn top us es u)) us

arrows : Code → List (Obj × Obj)
arrows c with units c | extUnits c
... | us | es = arrowsIn (modName c) us es

-- 对象全体
objectsIn : QName → List Unit → List Unit → List Obj
objectsIn top us es = map (λ u → unit (uname u)) us
  ++ nubᵇ _==ᴼ_ (map (λ u → ext (uname u)) es ++ filterᵇ isExt (map proj₂ (arrowsIn top us es)))
  ++ (flags ∷ ⊥ ∷ [])
  where
    isExt : Obj → Bool
    isExt (ext _) = true
    isExt _       = false

objects : Code → List Obj
objects c = objectsIn (modName c) (units c) (extUnits c)

-- 直接依赖者：谁用到 o（在给定的箭头表里找）
dependentsIn : List (Obj × Obj) → Obj → List Obj
dependentsIn as o = map proj₁ (filterᵇ (λ a → proj₂ a ==ᴼ o) as)

dependents : Code → Obj → List Obj
dependents c = dependentsIn (arrows c)

-- 传递依赖者（上游锥）：从 os 出发，沿"被谁用到"一路往上。有界递归（步数 = 箭头数 + 1），处理环。
coneIn : List (Obj × Obj) → List Obj → List Obj
coneIn as os = go (suc (length as)) os os
  where
    go : ℕ → List Obj → List Obj → List Obj
    go zero    seen _        = seen
    go (suc n) seen frontier with filterᵇ (λ o → not (elemᵇ _==ᴼ_ o seen)) (nubᵇ _==ᴼ_ (concatMap (dependentsIn as) frontier))
    ... | []  = seen
    ... | new = go n (seen ++ new) new

cone : Code → List Obj → List Obj
cone c = coneIn (arrows c)

------------------------------------------------------------------------
-- §4  接口：一个对象"对外承诺"的部分。依赖者只看得到这个。
--   函数 / postulate：类型
--   data：参数、sort、构造子的名字和类型（加一个构造子会让匹配它的函数不穷尽，所以算接口）
--   record：参数、sort、coinductive、构造子名、字段
--   模块：它暴露的名字
--   flags：flag 集合
--   ⊥：没有接口
------------------------------------------------------------------------

data Iface : Set where
  ifaceSig   : Expr → Iface
  ifaceData  : List Bind → Expr → List (Name × Expr) → Iface
  ifaceRec   : List Bind → Expr → RecDir → List (Name × Expr) → Iface
  ifaceMod   : List Name → Iface
  ifaceFlags : List String → Iface
  ifaceNone  : Iface

eqIface : Iface → Iface → Bool
eqIface (ifaceSig e)        (ifaceSig e′)          = eqExpr e e′
eqIface (ifaceData bs s cs) (ifaceData bs′ s′ cs′) = eqBinds bs bs′ ∧ eqExpr s s′ ∧ eqFields cs cs′
eqIface (ifaceRec bs s d fs) (ifaceRec bs′ s′ d′ fs′) = eqBinds bs bs′ ∧ eqExpr s s′ ∧ eqRecDir d d′ ∧ eqFields fs fs′
eqIface (ifaceMod ns)       (ifaceMod ns′)         = eqList _==ˢ_ ns ns′
eqIface (ifaceFlags fs)     (ifaceFlags fs′)       = eqList _==ˢ_ fs fs′
eqIface ifaceNone           ifaceNone              = true
eqIface _                   _                      = false

-- 从一个单元的声明里读出接口
ifaceOfDecls : List Decl → Iface
ifaceOfDecls ds = go ds ifaceNone
  where
    -- 把签名部分和定义部分拼起来：dataSig 给参数和 sort，dataDef 给构造子
    go : List Decl → Iface → Iface
    go []                          acc = acc
    go (sig _ _ e ∷ ds)            acc = go ds (ifaceSig e)
    go (fun _ _ _ ∷ ds)            acc = go ds acc
    go (dataSig _ _ bs s ∷ ds)     acc with acc
    ... | ifaceData _ _ cs = go ds (ifaceData bs s cs)
    ... | _                = go ds (ifaceData bs s [])
    go (dataDef _ _ _ cs ∷ ds)     acc with acc
    ... | ifaceData bs s _ = go ds (ifaceData bs s cs)
    ... | _                = go ds (ifaceData [] meta cs)
    go (recSig _ _ bs s ∷ ds)      acc with acc
    ... | ifaceRec _ _ d fs = go ds (ifaceRec bs s d fs)
    ... | _                 = go ds (ifaceRec bs s (recDir false nothing) [])
    go (recDef _ _ _ d fs ∷ ds)    acc with acc
    ... | ifaceRec bs s _ _ = go ds (ifaceRec bs s d fs)
    ... | _                 = go ds (ifaceRec [] meta d fs)
    go (module′ _ _ sub ∷ ds)      acc = go ds (ifaceMod (names sub))
      where
        names : List Decl → List Name
        names []       = []
        names (d ∷ ds) with declName d
        ... | just x  = x ∷ names ds
        ... | nothing = names ds
    go (_ ∷ ds)                    acc = go ds acc

lookupUnit : List Unit → QName → Maybe Unit
lookupUnit []       q = nothing
lookupUnit (u ∷ us) q = if uname u ==ᴺ q then just u else lookupUnit us q

iface : Code → Obj → Iface
iface c (unit q) with lookupUnit (units c) q
... | just u  = ifaceOfDecls (udecls u)
... | nothing = ifaceNone
iface c (ext q) with lookupUnit (extUnits c) q
... | just u  = ifaceOfDecls (udecls u)
... | nothing = ifaceNone                       -- 语境库里的名字：接口不在我手里，当作"不变"（见 Transport）
iface c flags = ifaceFlags (flagsOf c)
iface c ⊥     = ifaceNone

isPostulate : List Decl → Bool
isPostulate ds = anyᵇ isSig ds ∧ not (anyᵇ isDef ds)
  where
    isSig : Decl → Bool
    isSig (sig _ _ _) = true
    isSig _ = false
    isDef : Decl → Bool
    isDef (fun _ _ _)        = true
    isDef (dataDef _ _ _ _)  = true
    isDef (recDef _ _ _ _ _) = true
    isDef (dataSig _ _ _ _)  = true
    isDef (recSig _ _ _ _)   = true
    isDef (module′ _ _ _)    = true
    isDef _ = false


infective coinfective : List String
infective   = "--cubical" ∷ "--erased-cubical" ∷ "--guardedness" ∷ "--sized-types" ∷ "--prop" ∷ "--rewriting"
            ∷ "--two-level" ∷ "--cumulativity" ∷ "--cohesion" ∷ "--flat-split" ∷ "--injective-type-constructors" ∷ []
coinfective = "--safe" ∷ "--without-K" ∷ "--no-universe-polymorphism" ∷ "--no-sized-types" ∷ "--no-guardedness"
            ∷ "--level-universe" ∷ []

subsetᵇ : List String → List String → Bool
subsetᵇ xs ys = allᵇ (λ x → elemᵇ _==ˢ_ x ys) xs

-- 孩子的 flags 在父亲允许的包络里吗
flagsOK : (parent child : List String) → Bool
flagsOK pa ch = subsetᵇ (filterᵇ (λ f → elemᵇ _==ˢ_ f infective) ch) pa
              ∧ subsetᵇ (filterᵇ (λ f → elemᵇ _==ˢ_ f coinfective) pa) ch


mutual
  holesExpr : Expr → Bool
  holesExpr (var x)        = false
  holesExpr (def q)        = false
  holesExpr (con q)        = false
  holesExpr (lit l)        = false
  holesExpr (set n)        = false
  holesExpr hole           = true
  holesExpr meta           = false
  holesExpr (app f (arg _ _ a)) = holesExpr f ∨ holesExpr a
  holesExpr (lam x e)      = holesExpr e
  holesExpr (lamT b e)     = holesBind b ∨ holesExpr e
  holesExpr (absurdLam h)  = false
  holesExpr (lamCase cs)   = holesClauses cs
  holesExpr (pi b e)       = holesBind b ∨ holesExpr e
  holesExpr (fun′ (arg _ _ a) e) = holesExpr a ∨ holesExpr e
  holesExpr (let′ bs e)    = holesLetBinds bs ∨ holesExpr e
  holesExpr (rec′ fs)      = holesFields fs
  holesExpr (recUpd r fs)  = holesExpr r ∨ holesFields fs
  holesExpr (dot e)        = holesExpr e

  holesFields : List (Name × Expr) → Bool
  holesFields []             = false
  holesFields ((_ , e) ∷ fs) = holesExpr e ∨ holesFields fs

  holesBind : Bind → Bool
  holesBind (bind _ _ e) = holesExpr e

  holesBinds : List Bind → Bool
  holesBinds []       = false
  holesBinds (b ∷ bs) = holesBind b ∨ holesBinds bs

  holesPat : Pat → Bool
  holesPat (varP x)    = false
  holesPat (conP q ps) = holesPats ps
  holesPat wildP       = false
  holesPat (litP l)    = false
  holesPat (dotP e)    = holesExpr e
  holesPat absurdP     = false
  holesPat (asP x p)   = holesPat p
  holesPat (projP q)   = false
  holesPat (recP fs)   = holesPatFields fs

  holesPatFields : List (Name × Pat) → Bool
  holesPatFields []             = false
  holesPatFields ((_ , p) ∷ fs) = holesPat p ∨ holesPatFields fs

  holesPats : List (Arg Pat) → Bool
  holesPats []       = false
  holesPats (arg _ _ p ∷ ps) = holesPat p ∨ holesPats ps

  -- 左边：head 的函数名是"自己"，不算引用；proj 的投影名算
  holesLHS : LHS → Bool
  holesLHS (head f ps)     = holesPats ps
  holesLHS (proj f l ps)   = holesLHS l ∨ holesPats ps
  holesLHS (with′ l ws ps) = holesLHS l ∨ holesPats ws ∨ holesPats ps

  holesRHS : RHS → Bool
  holesRHS (rhs e)         = holesExpr e
  holesRHS absurdRHS       = false
  holesRHS (withRHS es cs) = holesExprs es ∨ holesClauses cs
  holesRHS (rewriteRHS es r) = holesExprs es ∨ holesRHS r

  holesExprs : List Expr → Bool
  holesExprs []       = false
  holesExprs (e ∷ es) = holesExpr e ∨ holesExprs es

  holesClause : Clause → Bool
  holesClause (clause l r w) = holesLHS l ∨ holesRHS r ∨ holesDecls w

  holesClauses : List Clause → Bool
  holesClauses []       = false
  holesClauses (c ∷ cs) = holesClause c ∨ holesClauses cs

  holesLetBind : LetBind → Bool
  holesLetBind (letBind x t e) = holesExpr t ∨ holesExpr e
  holesLetBind (letPat p e)    = holesPat p ∨ holesExpr e

  holesLetBinds : List LetBind → Bool
  holesLetBinds []       = false
  holesLetBinds (b ∷ bs) = holesLetBind b ∨ holesLetBinds bs

  holesDecl : Decl → Bool
  holesDecl (pragma s)           = false
  holesDecl (import′ m o d i)    = false            -- 接口里的签名引用的是别处的名字，不算本文件的依赖
  holesDecl (open′ m d)          = false
  holesDecl (fixity a n x)       = false
  holesDecl (sig m x e)          = holesExpr e
  holesDecl (fun m x cs)         = holesClauses cs
  holesDecl (dataSig m x bs e)   = holesBinds bs ∨ holesExpr e
  holesDecl (dataDef m x ps cs)  = holesFields cs
  holesDecl (recSig m x bs e)    = holesBinds bs ∨ holesExpr e
  holesDecl (recDef m x ps d fs) = holesFields fs
  holesDecl (variable′ vs)       = holesFields vs
  holesDecl (module′ x bs ds)    = holesBinds bs ∨ holesDecls ds
  holesDecl (patSyn _ _ p) = holesPat p
  holesDecl (unsupported s)      = false

  holesDecls : List Decl → Bool
  holesDecls []       = false
  holesDecls (d ∷ ds) = holesDecl d ∨ holesDecls ds


data ImplProblem : Set where
  unimplementedPostulate : QName → ImplProblem
  containsHole : QName → ImplProblem
  containsUnsupported : ImplProblem
  forbiddenTerminationBypass : ImplProblem
  flagEnvelopeViolation : ImplProblem
  unsafePrimitive : QName → ImplProblem

hasWord : String → String → Bool
hasWord word txt = elemᵇ _==ˢ_ word (Data.String.words txt)

bypassMods : Mods → Bool
bypassMods m = not (eqTermCheck (termCheck m) check)

safeQName : QName → Bool
safeQName q = not (elemᵇ _==ˢ_ "TrustMe" (full q)) ∧ not (elemᵇ _==ˢ_ "Unsafe" (full q))

-- Agda's option parser accepts unique abbreviated long options. Check their
-- prefixes as well, since conditional spec stubs prevent passing --safe
-- directly to the ordinary compiler process.
setsOption : String → String → Bool
setsOption spelling option = prefix (Data.String.toList spelling) (Data.String.toList option)
  where
    prefix : List Char → List Char → Bool
    prefix [] _ = true
    prefix (_ ∷ _) [] = false
    prefix (x ∷ xs) (y ∷ ys) = primCharEquality x y ∧ prefix xs ys

unsafeOptions : List String → Bool
unsafeOptions options = anyᵇ enabled forbidden ∨ (cubical ∧ enabled "--with-K")
  ∨ ((enabled "--without-K" ∨ cubical) ∧ enabled "--flat-split")
  where
    enabled : String → Bool
    enabled o = anyᵇ (λ s → setsOption s o) options
    cubical = enabled "--cubical" ∨ enabled "--erased-cubical" ∨ enabled "--cubical-compatible"
    forbidden = "--allow-unsolved-metas" ∷ "--allow-incomplete-matches" ∷ "--no-positivity-check"
      ∷ "--no-termination-check" ∷ "--type-in-type" ∷ "--omega-in-omega" ∷ "--cumulativity"
      ∷ "--sized-types" ∷ "--injective-type-constructors" ∷ "--irrelevant-projections"
      ∷ "--experimental-irrelevance" ∷ "--rewriting" ∷ "--no-load-primitives" ∷ "--allow-exec"
      ∷ "--no-universe-check" ∷ "--no-coverage-check" ∷ []

unsafeNames : List QName → List ImplProblem
unsafeNames qs = map unsafePrimitive (filterᵇ (λ q → not (safeQName q)) qs)

mutual
  implementationBlock : List Name → List Decl → List ImplProblem
  implementationBlock path ds = concatMap checkUnit (unitsIn path (filterᵇ local ds)) ++ implementationDecls path ds
    where
      local : Decl → Bool
      local (variable′ _) = false
      local (module′ _ _ _) = false
      local _ = true
      checkUnit : Unit → List ImplProblem
      checkUnit u = if isPostulate (udecls u) then unimplementedPostulate (uname u) ∷ [] else []

  implementationDecls : List Name → List Decl → List ImplProblem
  implementationDecls path [] = []
  implementationDecls path (d ∷ ds) = implementationDecl path d ++ implementationDecls path ds

  implementationDecl : List Name → Decl → List ImplProblem
  implementationDecl path (import′ q _ _ _) = unsafeNames (q ∷ [])
  implementationDecl path (open′ q _) = unsafeNames (q ∷ [])
  implementationDecl path (module′ n bs ds) = implementationBlock (path ++ (n ∷ [])) ds
  implementationDecl path (unsupported _) = containsUnsupported ∷ []
  implementationDecl path (pragma s) =
    if anyᵇ (λ w → hasWord w s)
        ("NON_TERMINATING" ∷ "TERMINATING" ∷ "NO_TERMINATION_CHECK" ∷ "NON_COVERING"
         ∷ "NO_POSITIVITY_CHECK" ∷ "NO_UNIVERSE_CHECK" ∷ "INJECTIVE" ∷ "ETA" ∷ "POLARITY"
         ∷ "COMPILE" ∷ "FOREIGN" ∷ "BUILTIN" ∷ "REWRITE" ∷ [])
    then forbiddenTerminationBypass ∷ [] else []
  implementationDecl path (fun m n cs) = modsProblem m ++ clausesProblem (path ++ (n ∷ [])) cs
  implementationDecl path d =
    (if holesDecl d then containsHole (mkQ path) ∷ [] else []) ++ modsProblem (declMods d)
    ++ nestedDecl path d
    where
      declMods : Decl → Mods
      declMods (sig m _ _) = m
      declMods (dataSig m _ _ _) = m
      declMods (dataDef m _ _ _) = m
      declMods (recSig m _ _ _) = m
      declMods (recDef m _ _ _ _) = m
      declMods _ = plain

  nestedExpr : List Name → Expr → List ImplProblem
  nestedExpr path (var x)        = []
  nestedExpr path (def q)        = []
  nestedExpr path (con q)        = []
  nestedExpr path (lit l)        = []
  nestedExpr path (set n)        = []
  nestedExpr path hole           = []
  nestedExpr path meta           = []
  nestedExpr path (app f (arg _ _ a)) = nestedExpr path f ++ nestedExpr path a
  nestedExpr path (lam x e)      = nestedExpr path e
  nestedExpr path (lamT b e)     = nestedBind path b ++ nestedExpr path e
  nestedExpr path (absurdLam h)  = []
  nestedExpr path (lamCase cs)   = nestedClauses path cs
  nestedExpr path (pi b e)       = nestedBind path b ++ nestedExpr path e
  nestedExpr path (fun′ (arg _ _ a) e) = nestedExpr path a ++ nestedExpr path e
  nestedExpr path (let′ bs e)    = nestedLetBinds path bs ++ nestedExpr path e
  nestedExpr path (rec′ fs)      = nestedFields path fs
  nestedExpr path (recUpd r fs)  = nestedExpr path r ++ nestedFields path fs
  nestedExpr path (dot e)        = nestedExpr path e

  nestedFields : List Name → List (Name × Expr) → List ImplProblem
  nestedFields path []             = []
  nestedFields path ((_ , e) ∷ fs) = nestedExpr path e ++ nestedFields path fs

  nestedBind : List Name → Bind → List ImplProblem
  nestedBind path (bind _ _ e) = nestedExpr path e

  nestedBinds : List Name → List Bind → List ImplProblem
  nestedBinds path []       = []
  nestedBinds path (b ∷ bs) = nestedBind path b ++ nestedBinds path bs

  nestedPat : List Name → Pat → List ImplProblem
  nestedPat path (varP x)    = []
  nestedPat path (conP q ps) = nestedPats path ps
  nestedPat path wildP       = []
  nestedPat path (litP l)    = []
  nestedPat path (dotP e)    = nestedExpr path e
  nestedPat path absurdP     = []
  nestedPat path (asP x p)   = nestedPat path p
  nestedPat path (projP q)   = []
  nestedPat path (recP fs)   = nestedPatFields path fs

  nestedPatFields : List Name → List (Name × Pat) → List ImplProblem
  nestedPatFields path []             = []
  nestedPatFields path ((_ , p) ∷ fs) = nestedPat path p ++ nestedPatFields path fs

  nestedPats : List Name → List (Arg Pat) → List ImplProblem
  nestedPats path []       = []
  nestedPats path (arg _ _ p ∷ ps) = nestedPat path p ++ nestedPats path ps

  -- 左边：head 的函数名是"自己"，不算引用；proj 的投影名算
  nestedLHS : List Name → LHS → List ImplProblem
  nestedLHS path (head f ps)     = nestedPats path ps
  nestedLHS path (proj f l ps)   = nestedLHS path l ++ nestedPats path ps
  nestedLHS path (with′ l ws ps) = nestedLHS path l ++ nestedPats path ws ++ nestedPats path ps

  nestedRHS : List Name → RHS → List ImplProblem
  nestedRHS path (rhs e)         = nestedExpr path e
  nestedRHS path absurdRHS       = []
  nestedRHS path (withRHS es cs) = nestedExprs path es ++ nestedClauses path cs
  nestedRHS path (rewriteRHS es r) = nestedExprs path es ++ nestedRHS path r

  nestedExprs : List Name → List Expr → List ImplProblem
  nestedExprs path []       = []
  nestedExprs path (e ∷ es) = nestedExpr path e ++ nestedExprs path es

  nestedClause : List Name → Clause → List ImplProblem
  nestedClause path (clause l r w) = nestedLHS path l ++ nestedRHS path r ++ implementationBlock path w

  nestedClauses : List Name → List Clause → List ImplProblem
  nestedClauses path []       = []
  nestedClauses path (c ∷ cs) = nestedClause path c ++ nestedClauses path cs

  nestedLetBind : List Name → LetBind → List ImplProblem
  nestedLetBind path (letBind x t e) = nestedExpr path t ++ nestedExpr path e
  nestedLetBind path (letPat p e)    = nestedPat path p ++ nestedExpr path e

  nestedLetBinds : List Name → List LetBind → List ImplProblem
  nestedLetBinds path []       = []
  nestedLetBinds path (b ∷ bs) = nestedLetBind path b ++ nestedLetBinds path bs

  nestedDecl : List Name → Decl → List ImplProblem
  nestedDecl path (pragma s)           = []
  nestedDecl path (import′ m o d i)    = []            -- 接口里的签名引用的是别处的名字，不算本文件的依赖
  nestedDecl path (open′ m d)          = []
  nestedDecl path (fixity a n x)       = []
  nestedDecl path (sig m x e)          = nestedExpr path e
  nestedDecl path (fun m x cs)         = nestedClauses path cs
  nestedDecl path (dataSig m x bs e)   = nestedBinds path bs ++ nestedExpr path e
  nestedDecl path (dataDef m x ps cs)  = nestedFields path cs
  nestedDecl path (recSig m x bs e)    = nestedBinds path bs ++ nestedExpr path e
  nestedDecl path (recDef m x ps d fs) = nestedFields path fs
  nestedDecl path (variable′ vs)       = nestedFields path vs
  nestedDecl path (module′ x bs ds)    = nestedBinds path bs ++ nestedDecls path ds
  nestedDecl path (patSyn _ _ p) = nestedPat path p
  nestedDecl path (unsupported s)      = []

  nestedDecls : List Name → List Decl → List ImplProblem
  nestedDecls path []       = []
  nestedDecls path (d ∷ ds) = nestedDecl path d ++ nestedDecls path ds

  modsProblem : Mods → List ImplProblem
  modsProblem m = if bypassMods m then forbiddenTerminationBypass ∷ [] else []

  clausesProblem : List Name → List Clause → List ImplProblem
  clausesProblem path [] = []
  clausesProblem path (clause l r ds ∷ cs) =
    (if holesLHS l ∨ holesRHS r then containsHole (mkQ path) ∷ [] else [])
    ++ implementationBlock path ds ++ rhsProblem path r ++ clausesProblem path cs

  rhsProblem : List Name → RHS → List ImplProblem
  rhsProblem path (rhs e) = nestedExpr path e
  rhsProblem path (withRHS es cs) = nestedExprs path es ++ clausesProblem path cs
  rhsProblem path (rewriteRHS es r) = nestedExprs path es ++ rhsProblem path r
  rhsProblem path _ = []

closedImplOK : List String → Code → List ImplProblem
closedImplOK allowed c = implementationBlock (full (modName c)) (decls c)
  ++ unsafeNames (modName c ∷ refsBinds (params c) ++ refsDecls (decls c))
  ++ (if holesBinds (params c) then containsHole (modName c) ∷ [] else [])
  ++ (if unsafeOptions (flagsOf c) then forbiddenTerminationBypass ∷ [] else [])
  ++ (if flagsOK allowed (flagsOf c) then [] else flagEnvelopeViolation ∷ [])

data RefuteProblem : Set where
  invalidImplementation : ImplProblem → RefuteProblem
  unauthorizedImport : QName → RefuteProblem
  missingBottomProof missingTabooProof missingBaseReference : RefuteProblem

contextModule : QName → Bool
contextModule q = safeQName q ∧ anyᵇ (λ p → isPrefix p (full q))
  (("Agda" ∷ "Builtin" ∷ []) ∷ ("Data" ∷ []) ∷ ("Relation" ∷ [])
   ∷ ("Function" ∷ []) ∷ ("Level" ∷ []) ∷ ("Context" ∷ []) ∷ [])

bottomExpr : Expr → Bool
bottomExpr (def q) = eqList _==ˢ_ (full q) ("Data" ∷ "Empty" ∷ "⊥" ∷ [])
                  ∨ eqList _==ˢ_ (full q) ("Agda" ∷ "Builtin" ∷ "Empty" ∷ "⊥" ∷ [])
bottomExpr _ = false

tabooExpr : Expr → Bool
tabooExpr e@(def q) = bottomExpr e ∨ eqList _==ˢ_ (full q) ("Context" ∷ "Taboo" ∷ "SafeTaboo" ∷ [])
tabooExpr _ = false

checkWitnessIn : (Name → Expr → Bool) → RefuteProblem → List QName → List QName
               → List String → Code → List RefuteProblem
checkWitnessIn target missingProof permitted imported allowed c = map invalidImplementation (closedImplOK allowed c)
  ++ map unauthorizedImport (filterᵇ (λ q → not (elemᵇ _==ᴺ_ q permitted ∨ contextModule q)) imported)
  ++ concatMap checkReference (refsDecls (decls c))
  ++ (if nullParams (params c) ∧ anyᵇ provesTarget (unitsIn (full (modName c)) (filterᵇ topLevel (decls c))) then [] else missingProof ∷ [])
  where
    -- Scope checking canonicalizes aliases. This also catches unauthorized
    -- dependencies introduced inside a where block or an extended lambda.
    checkReference : QName → List RefuteProblem
    checkReference q = if anyᵇ (λ m → isPrefix (full m) (full q)) (modName c ∷ permitted) ∨ contextModule q
      then [] else unauthorizedImport q ∷ []
    topLevel : Decl → Bool
    topLevel (module′ _ _ _) = false
    topLevel _ = true
    nullParams : List Bind → Bool
    nullParams [] = true
    nullParams _ = false
    targetSig : Decl → Bool
    targetSig (sig m n e) = not (isPrivate m) ∧ target n e
    targetSig _ = false
    provesTarget : Unit → Bool
    provesTarget u = anyᵇ targetSig (udecls u) ∧ not (isPostulate (udecls u))

checkWitness : (Expr → Bool) → RefuteProblem → QName → List String → Code → List RefuteProblem
checkWitness target missingProof specMod allowed c =
  checkWitnessIn (λ _ → target) missingProof [ specMod ] (witnessImports (decls c)) allowed c
  where
    witnessImports : List Decl → List QName
    witnessImports [] = []
    witnessImports (import′ q _ _ _ ∷ ds) = q ∷ witnessImports ds
    witnessImports (module′ _ _ inner ∷ ds) = witnessImports inner ++ witnessImports ds
    witnessImports (_ ∷ ds) = witnessImports ds

validRefutation : QName → List String → Code → List RefuteProblem
validRefutation = checkWitness bottomExpr missingBottomProof

witnessNamespaceProblems : QName → Code → List RefuteProblem
witnessNamespaceProblems specMod c = (if modName c ==ᴺ specMod then unauthorizedImport specMod ∷ [] else [])
  ++ shadow (modName c) ++ shadow specMod
  where
    -- A module named Context could define its own nested Taboo.SafeTaboo.
    -- Neither side of the witness may own the trusted goal's name.
    shadow : QName → List RefuteProblem
    shadow q = if anyᵇ (isPrefix (full q))
      (("Context" ∷ "Taboo" ∷ "SafeTaboo" ∷ []) ∷ ("Data" ∷ "Empty" ∷ "⊥" ∷ [])
       ∷ ("Agda" ∷ "Builtin" ∷ "Empty" ∷ "⊥" ∷ []) ∷ [])
      then unauthorizedImport q ∷ [] else []

validIndependence : QName → List String → Code → List RefuteProblem
validIndependence specMod allowed c = witnessNamespaceProblems specMod c
  ++ checkWitness tabooExpr missingTabooProof specMod allowed c
