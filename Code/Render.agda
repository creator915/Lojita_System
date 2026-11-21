------------------------------------------------------------------------
-- Code/Render.agda —— Code → Agda 源码
--
-- 目标只有一个：render 出来的东西 agda 要能接受。好看是其次。
-- 两条安全策略：
--   1. 括号：参数位置上任何非原子的表达式一律加括号。不算优先级，就不会算错。
--      二元算子（名字里正好两个 _，刚好两个可见参数）写成中缀 a + b；其他 mixfix 写前缀 _+_ a。
--   3. 顺序：按依赖排序再输出。原来顺序合法的话一动不动（稳定）；搬运新加的单元会被拉到
--      第一个用到它的地方前面。互递归的一组（环）先写全部签名，再写全部定义。
--
-- 丢掉的东西（abstract 里本来就没有）：注释、do 记法（变成 >>= 链）、模块应用。
------------------------------------------------------------------------
module Code.Render where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; length; reverse; foldr; replicate; [_]; zip; upTo; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList; concat; intersperse; unlines) renaming (_++_ to _++ˢ_)
open import Data.Char using (Char; toℕ; fromℕ)
open import Agda.Builtin.Char using (primCharEquality)
import Data.Nat.Show as ℕshow

open import Code

------------------------------------------------------------------------
-- §0  字符串小工具
------------------------------------------------------------------------

spaces : ℕ → String
spaces n = fromList (replicate n ' ')

-- 把一行缩进
indentLine : ℕ → String → String
indentLine n s = spaces n ++ˢ s

-- 名字按 _ 切开：_+_ → "" ∷ "+" ∷ "" ∷ []；if_then_else_ → "if" ∷ "then" ∷ "else" ∷ "" ∷ []
-- 带限定的算子 Str._≟_：只切最后一段，限定符贴到第一个非空的部分上（Agda 写 a Str.≟ b）
nameParts : Name → List String
nameParts s = attach (splitQual (toList s))
  where
    -- (限定符含点 , 最后一段)
    splitQual : List Char → List Char × List Char
    splitQual cs = go cs [] []
      where
        go : List Char → List Char → List Char → List Char × List Char
        go []       cur qual = qual , reverse cur
        go (c ∷ rest) cur qual = if primCharEquality c '.' ∧ notEmpty rest
                                 then go rest [] (qual ++ reverse cur ++ ('.' ∷ []))
                                 else go rest (c ∷ cur) qual
          where
            notEmpty : List Char → Bool
            notEmpty [] = false
            notEmpty _  = true
    split : List Char → List String
    split cs = go cs [] []
      where
        go : List Char → List Char → List String → List String
        go []       cur acc = reverse (fromList (reverse cur) ∷ acc)
        go (c ∷ cs) cur acc = if primCharEquality c '_' then go cs [] (fromList (reverse cur) ∷ acc)
                              else go cs (c ∷ cur) acc
    attach : List Char × List Char → List String
    attach ([]   , name) = split name
    attach (qual , name) = prefixFirst (split name)
      where
        prefixFirst : List String → List String
        prefixFirst []       = []
        prefixFirst (p ∷ ps) with toList p
        ... | [] = p ∷ prefixFirst ps
        ... | _  = (fromList qual ++ˢ p) ∷ ps

holes : Name → ℕ
holes s = length (nameParts s) ∸ 1

isOperator : Name → Bool
isOperator s = 1 ≤ᵇ holes s

-- mixfix：把参数填进洞里。只在"刚好这么多可见参数"时用；否则 nothing，退回前缀写法。
mixfix : Name → List String → Maybe String
mixfix op args = if (length args ≡ᵇ holes op) ∧ (1 ≤ᵇ holes op) then just (go (nameParts op) args) else nothing
  where
    go : List String → List String → String
    go (p ∷ ps) (a ∷ as) = (if isEmpty p then a else p ++ˢ " " ++ˢ a) ++ˢ (if isEmpty (rest ps as) then "" else " " ++ˢ rest ps as)
      where
        isEmpty : String → Bool
        isEmpty s with toList s
        ... | [] = true
        ... | _  = false
        rest : List String → List String → String
        rest (q ∷ qs) (b ∷ bs) = (if isEmpty q then b else q ++ˢ " " ++ˢ b) ++ˢ (if isEmpty (rest qs bs) then "" else " " ++ˢ rest qs bs)
        rest (q ∷ [])  []      = q
        rest _         _       = ""
    go (p ∷ []) [] = p
    go _        _  = ""

subscript : ℕ → String
subscript n = fromList (map sub (toList (ℕshow.show n)))
  where
    sub : Char → Char
    sub c = fromℕ (toℕ c ∸ 48 + 8320)      -- '0'(48) → '₀'(U+2080 = 8320)

escapeStr : String → String
escapeStr s = fromList (go (toList s))
  where
    go : List Char → List Char
    go []          = []
    go ('"' ∷ cs)  = '\\' ∷ '"' ∷ go cs
    go ('\\' ∷ cs) = '\\' ∷ '\\' ∷ go cs
    go ('\n' ∷ cs) = '\\' ∷ 'n' ∷ go cs
    go ('\r' ∷ cs) = '\\' ∷ 'r' ∷ go cs
    go (c ∷ cs)    = c ∷ go cs

renderLit : Lit → String
renderLit (natL n)  = ℕshow.show n
renderLit (strL s)  = "\"" ++ˢ escapeStr s ++ˢ "\""
renderLit (charL c) = if primCharEquality c '\'' then "'\\''" else "'" ++ˢ escapeStr (fromList (c ∷ [])) ++ˢ "'"

-- 按可见性加括号：x  {x}  {{x}}  {l = x}
braces : Hiding → Maybe Name → String → String
braces visible nothing  s = s
braces visible (just l) s = "(" ++ˢ l ++ˢ " = " ++ˢ s ++ˢ ")"      -- 可见的带名参数：少见，保守写法
braces hidden  nothing  s = "{" ++ˢ s ++ˢ "}"
braces hidden  (just l) s = "{" ++ˢ l ++ˢ " = " ++ˢ s ++ˢ "}"
braces inst    nothing  s = "{{" ++ˢ s ++ˢ "}}"
braces inst    (just l) s = "{{" ++ˢ l ++ˢ " = " ++ˢ s ++ˢ "}}"

------------------------------------------------------------------------
-- §1  表达式与模式
-- 所有函数带一个 ind：当前声明的缩进。只有 λ where 这种要另起一行的东西用它。
------------------------------------------------------------------------

atomicE : Expr → Bool
atomicE (var _) = true
atomicE (def _) = true
atomicE (con _) = true
atomicE (lit _) = true
atomicE (set _) = true
atomicE hole    = true
atomicE meta    = true
atomicE _       = false

atomicP : Pat → Bool
atomicP (varP _)    = true
atomicP wildP       = true
atomicP (litP _)    = true
atomicP absurdP     = true
atomicP (conP _ []) = true
atomicP _           = false

paren : String → String
paren s = "(" ++ˢ s ++ˢ ")"

-- 一串应用拆成头和参数
spine : Expr → Expr × List (Arg Expr)
spine (app f a) with spine f
... | h , as = h , as ++ (a ∷ [])
spine e = e , []

allVisible : ∀ {A : Set} → List (Arg A) → Bool
allVisible []                        = true
allVisible (arg visible nothing _ ∷ as) = allVisible as
allVisible (_ ∷ _)                   = false

headName : Expr → Maybe Name
headName (def q) = just (shown q)
headName (con q) = just (shown q)
headName _       = nothing

tryMixfix : Maybe Name → Bool → List String → Maybe String
tryMixfix (just op) true args = mixfix op args
tryMixfix _         _    _    = nothing

-- 这个应用会被写成中缀吗？（和 finishApp 的判断一致）
isInfixApp : Expr → Bool
isInfixApp e with spine e
... | h , as with headName h
...   | just op = allVisible as ∧ (length as ≡ᵇ holes op) ∧ (1 ≤ᵇ holes op)
...   | nothing = false

-- 算子的操作数位置（a + b 的 a）、函数类型的定义域（A → B 的 A）：
-- 前缀应用 f x 不用括号（应用比任何算子都紧），中缀应用和 λ、→、let 要括号
needsParenAsOperand : Expr → Bool
needsParenAsOperand e@(app _ _) = isInfixApp e
needsParenAsOperand e           = not (atomicE e)

-- 一串应用拆开的样子：头、原始参数、渲染好的参数（前缀用）、渲染好的参数（中缀用）、头的字符串
Spine : Set
Spine = Expr × List (Arg Expr) × List String × List String × String

pushArg : Spine → Arg Expr → String → String → Spine
pushArg (h , as , rs , os , hs) a r o = h , as ++ (a ∷ []) , rs ++ (r ∷ []) , os ++ (o ∷ []) , hs

-- 中缀能用就用（a + b），否则前缀（f a b）
finishApp : Spine → String
finishApp (h , as , rs , os , hs) with tryMixfix (headName h) (allVisible as) os
... | just s  = s
... | nothing = intersperse " " (hs ∷ rs)

-- 右边渲染结果 = (接在左边后面的那一截 , 后续的行)。在前面接一截：
prefixRHS : String → String × List String → String × List String
prefixRHS s (tl , more) = s ++ˢ tl , more

-- 拼一条子句：左边 + 右边第一截，然后 where 的行，然后右边带出的行（with 的子句）。
-- where 在 with 子句前面：abstract 里 where 挂在带 with 的那条子句上，写在后面会被 Agda 算到最后一条 with 子句头上
joinClause : ℕ → String → String × List String → List String → List String
joinClause ind lhs (tl , more) wh = indentLine ind (lhs ++ˢ tl) ∷ wh ++ more

-- 把一组行包进块：块名一行，里面多缩进 2
block : ℕ → String → List String → List String
block ind kw ls = indentLine ind kw ∷ map ("  " ++ˢ_) ls

-- 终止检查的 pragma 行：紧贴在单元前面（块里面）。拆成签名/定义两半输出时只跟着签名那一半（withTC 由调用者给）
tcLine : ℕ → Mods → List String
tcLine ind (mods _ _ _ check)          = []
tcLine ind (mods _ _ _ nonTerminating) = indentLine ind "{-# NON_TERMINATING #-}" ∷ []
tcLine ind (mods _ _ _ terminating)    = indentLine ind "{-# TERMINATING #-}" ∷ []

-- The next anonymous signature starts a different obligation.
hasBody : Name → List Decl → Bool
hasBody x [] = false
hasBody x (fun _ y _ ∷ ds) = (x ==ˢ y) ∨ hasBody x ds
hasBody "_" (sig _ "_" _ ∷ ds) = false
hasBody x (_ ∷ ds) = hasBody x ds

-- Decorations belong to individual declarations, including declarations in a
-- nested module or where block. Graph-ordered units already wrap the group.
decorate : Bool → ℕ → Mods → Bool → Bool → List String → List String
decorate false ind m withTC stub ls = ls
decorate true ind m withTC stub ls = wrap (isPrivate m) "private"
  (wrap (isInstance m) "instance" (wrap (isAbstract m) "abstract"
    ((if withTC then tcLine ind m else []) ++ wrap stub "postulate" ls)))
  where
    wrap : Bool → String → List String → List String
    wrap true kw ls = block ind kw ls
    wrap false kw ls = ls

mutual
  renderExpr : ℕ → Expr → String
  renderExpr ind (var x)        = x
  renderExpr ind (def q)        = shown q
  renderExpr ind (con q)        = shown q
  renderExpr ind (lit l)        = renderLit l
  renderExpr ind (set zero)     = "Set"
  renderExpr ind (set n)        = "Set" ++ˢ subscript n
  renderExpr ind hole           = "?"
  renderExpr ind meta           = "_"
  renderExpr ind (app f a)      = finishApp (pushArg (spineR ind f) a (renderArgE ind a) (operandArg ind a))
  renderExpr ind (lam (arg h l x) e) = "λ " ++ˢ braces h l x ++ˢ " " ++ˢ renderLamBinders ind e
  renderExpr ind (lamT b e)     = "λ " ++ˢ renderLamBinder ind b ++ˢ " " ++ˢ renderLamBinders ind e
  renderExpr ind (absurdLam visible) = "λ ()"
  renderExpr ind (absurdLam hidden)  = "λ {}"
  renderExpr ind (absurdLam inst)    = "λ {{}}"
  renderExpr ind (lamCase cs)   = "λ where" ++ˢ renderCaseClauses (ind + 4) cs
  renderExpr ind (pi b e)       = renderBind ind b ++ˢ " → " ++ˢ renderExpr ind e
  renderExpr ind (fun′ a e)     = renderArgDom ind a ++ˢ " → " ++ˢ renderExpr ind e
  renderExpr ind (let′ bs e)    = "let " ++ˢ renderLetBinds ind bs ++ˢ " in " ++ˢ renderExpr ind e
  renderExpr ind (rec′ fs)      = "record { " ++ˢ renderFields ind fs ++ˢ " }"
  renderExpr ind (recUpd r fs)  = "record " ++ˢ argPos ind r ++ˢ " { " ++ˢ renderFields ind fs ++ˢ " }"
  renderExpr ind (dot e)        = "." ++ˢ argPos ind e

  -- 参数位置上的裸表达式：非原子加括号
  argPos : ℕ → Expr → String
  argPos ind e = if atomicE e then renderExpr ind e else paren (renderExpr ind e)

  -- 参数位置：非原子加括号，再按可见性加花括号
  renderArgE : ℕ → Arg Expr → String
  renderArgE ind (arg h l e) = braces h l (argPos ind e)

  -- 函数类型的定义域：A → B 里的 A。中缀的要括号（A × B → C 要写 (A × B) → C），前缀应用不用
  renderArgDom : ℕ → Arg Expr → String
  renderArgDom ind (arg visible nothing e) = operandPos ind e
  renderArgDom ind (arg h l e)             = braces h l (argPos ind e)

  operandPos : ℕ → Expr → String
  operandPos ind e = if needsParenAsOperand e then paren (renderExpr ind e) else renderExpr ind e

  renderArgs : ℕ → List (Arg Expr) → List String
  renderArgs ind []       = []
  renderArgs ind (a ∷ as) = renderArgE ind a ∷ renderArgs ind as

  -- 应用：沿着 app 的左脊往下走，边走边渲染参数。
  -- 返回 (头 , 原始参数 , 渲染好的参数 , 头的字符串)。结构递归：f 和 a 都是 app f a 的子项。
  spineR : ℕ → Expr → Spine
  spineR ind (app f a) = pushArg (spineR ind f) a (renderArgE ind a) (operandArg ind a)
  spineR ind e         = e , [] , [] , [] , argPos ind e

  -- 中缀位置上的参数：{x} 这种不会出现（中缀只在全可见时用）；裸表达式按操作数规则加括号
  operandArg : ℕ → Arg Expr → String
  operandArg ind (arg _ _ e) = operandPos ind e

  -- λ 后面的一个绑定：类型是 _ 就只写名字（λ x →），否则写 (x : A)
  renderLamBinder : ℕ → Bind → String
  renderLamBinder ind (bind h (x ∷ []) meta) = braces h nothing x
  renderLamBinder ind b                = renderBind ind b

  -- λ x y (z : A) → e：连续的 λ 合并。参数 e 是 λ 的体
  renderLamBinders : ℕ → Expr → String
  renderLamBinders ind (lam (arg h l x) e) = braces h l x ++ˢ " " ++ˢ renderLamBinders ind e
  renderLamBinders ind (lamT b e)          = renderLamBinder ind b ++ˢ " " ++ˢ renderLamBinders ind e
  renderLamBinders ind e                   = "→ " ++ˢ renderExpr ind e

  -- (x y : A)  {x : A}  {{x : A}}
  renderBind : ℕ → Bind → String
  renderBind ind (bind h xs t) = wrap h (intersperse " " xs ++ˢ " : " ++ˢ renderExpr ind t)
    where
      wrap : Hiding → String → String
      wrap visible s = "(" ++ˢ s ++ˢ ")"
      wrap hidden  s = "{" ++ˢ s ++ˢ "}"
      wrap inst    s = "{{" ++ˢ s ++ˢ "}}"

  renderFields : ℕ → List (Name × Expr) → String
  renderFields ind []             = ""
  renderFields ind ((n , e) ∷ []) = n ++ˢ " = " ++ˢ renderExpr ind e
  renderFields ind ((n , e) ∷ fs) = n ++ˢ " = " ++ˢ renderExpr ind e ++ˢ " ; " ++ˢ renderFields ind fs

  -- let 的绑定用分号隔开写在一行：let x = 1; y : ℕ; y = 2 in …
  renderLetBinds : ℕ → List LetBind → String
  renderLetBinds ind []       = ""
  renderLetBinds ind (b ∷ []) = renderLetBind ind b
  renderLetBinds ind (b ∷ bs) = renderLetBind ind b ++ˢ "; " ++ˢ renderLetBinds ind bs

  renderLetBind : ℕ → LetBind → String
  renderLetBind ind (letBind x meta e) = x ++ˢ " = " ++ˢ renderExpr ind e
  renderLetBind ind (letBind x t e)    = x ++ˢ " : " ++ˢ renderExpr ind t ++ˢ "; " ++ˢ x ++ˢ " = " ++ˢ renderExpr ind e
  renderLetBind ind (letPat p e)       = (if atomicP p then renderPat ind p else paren (renderPat ind p)) ++ˢ " = " ++ˢ renderExpr ind e

  renderPat : ℕ → Pat → String
  renderPat ind (varP x)    = x
  renderPat ind (conP q []) = shown q
  renderPat ind (conP q ps) with allVisible ps | mixfix (shown q) (renderPats ind ps)
  ... | true | just s = s
  ... | _    | _      = intersperse " " (shown q ∷ renderPats ind ps)
  renderPat ind wildP       = "_"
  renderPat ind (litP l)    = renderLit l
  renderPat ind (dotP e)    = "." ++ˢ argPos ind e
  renderPat ind absurdP     = "()"
  renderPat ind (asP x p)   = x ++ˢ "@" ++ˢ (if atomicP p then renderPat ind p else paren (renderPat ind p))
  renderPat ind (projP q)   = "." ++ˢ shown q
  renderPat ind (recP fs)   = "record { " ++ˢ renderPatFields ind fs ++ˢ " }"

  renderPatFields : ℕ → List (Name × Pat) → String
  renderPatFields ind []             = ""
  renderPatFields ind ((n , p) ∷ []) = n ++ˢ " = " ++ˢ renderPat ind p
  renderPatFields ind ((n , p) ∷ fs) = n ++ˢ " = " ++ˢ renderPat ind p ++ˢ " ; " ++ˢ renderPatFields ind fs

  renderArgP : ℕ → Arg Pat → String
  renderArgP ind (arg h l p) = braces h l (if atomicP p then renderPat ind p else paren (renderPat ind p))

  renderPats : ℕ → List (Arg Pat) → List String
  renderPats ind []       = []
  renderPats ind (p ∷ ps) = renderArgP ind p ∷ renderPats ind ps

  -- 余模式里被投影的那部分：f x .proj 写成 proj (f x)；没有参数就不用括号
  projFocus : ℕ → Bool → LHS → String
  projFocus ind showHead (head x []) = shown x
  projFocus ind showHead l           = paren (renderLHS ind showHead l)

  -- 左边。showHead = false 时不写函数名（λ where 的子句）
  renderLHS : ℕ → Bool → LHS → String
  renderLHS ind showHead (head f ps) with showHead | allVisible ps | mixfix (shown f) (renderPats ind ps)
  ... | true  | true | just s = s
  ... | true  | _    | _      = intersperse " " (shown f ∷ renderPats ind ps)
  ... | false | _    | _      = intersperse " " (renderPats ind ps)
  renderLHS ind showHead (proj d l ps) = intersperse " " (shown d ∷ projFocus ind showHead l ∷ renderPats ind ps)
  renderLHS ind showHead (with′ l ws ps) =
    intersperse " " (renderLHS ind showHead l ∷ map ("| " ++ˢ_) (renderPats ind ws) ++ renderPats ind ps)

  -- 右边，接在左边后面。with / rewrite 会带出更多行（子句），所以返回"第一行的尾巴"和后续行
  renderRHS : ℕ → Bool → RHS → String × List String
  renderRHS ind showHead (rhs e)          = " = " ++ˢ renderExpr ind e , []
  renderRHS ind showHead absurdRHS        = "" , []
  renderRHS ind showHead (withRHS es cs)  = " with " ++ˢ intersperse " | " (renderOperands ind es) , renderClauses ind showHead cs
  renderRHS ind showHead (rewriteRHS es r) = prefixRHS (" rewrite " ++ˢ intersperse " | " (renderOperands ind es)) (renderRHS ind showHead r)

  -- with / rewrite 后面的表达式：按操作数规则加括号（with let … in … 要括号）
  renderOperands : ℕ → List Expr → List String
  renderOperands ind []       = []
  renderOperands ind (e ∷ es) = operandPos ind e ∷ renderOperands ind es

  renderExprs : ℕ → List Expr → List String
  renderExprs ind []       = []
  renderExprs ind (e ∷ es) = renderExpr ind e ∷ renderExprs ind es

  -- 一条子句 → 若干行（缩进 ind）
  renderClause : ℕ → Bool → Clause → List String
  renderClause ind showHead (clause l r w) = joinClause ind (renderLHS ind showHead l) (renderRHS ind showHead r) (whereLines ind w)

  whereLines : ℕ → List Decl → List String
  whereLines ind []                   = []
  whereLines ind (module′ m [] ds ∷ []) = indentLine (ind + 2) ("module " ++ˢ m ++ˢ " where") ∷ renderNestedDecls (ind + 4) ds
  whereLines ind w                    = indentLine (ind + 2) "where" ∷ renderNestedDecls (ind + 4) w

  renderClauses : ℕ → Bool → List Clause → List String
  renderClauses ind showHead []       = []
  renderClauses ind showHead (c ∷ cs) = renderClause ind showHead c ++ renderClauses ind showHead cs

  -- λ where 的子句：每条另起一行，不写头，→ 代替 =
  renderCaseClauses : ℕ → List Clause → String
  renderCaseClauses ind []       = ""
  renderCaseClauses ind (c ∷ cs) = "\n" ++ˢ intersperse "\n" (caseLines c) ++ˢ renderCaseClauses ind cs
    where
      caseLines : Clause → List String
      caseLines (clause l (rhs e) w) = joinClause ind (renderLHS ind false l)
        (" → " ++ˢ renderExpr ind e , []) (whereLines ind w)
      caseLines other = renderClause ind false other

  ----------------------------------------------------------------------
  -- 声明
  ----------------------------------------------------------------------

  renderDirective : Directive → String
  renderDirective (directive u h r p) = usingS u ++ˢ hidingS h ++ˢ renS r ++ˢ (if p then " public" else "")
    where
      names : List Name → String
      names ns = intersperse "; " ns
      usingS : Maybe (List Name) → String
      usingS nothing   = ""
      usingS (just ns) = " using (" ++ˢ names ns ++ˢ ")"
      hidingS : List Name → String
      hidingS [] = ""
      hidingS ns = " hiding (" ++ˢ names ns ++ˢ ")"
      renS : List (Name × Name) → String
      renS [] = ""
      renS rs = " renaming (" ++ˢ intersperse "; " (map (λ ab → proj₁ ab ++ˢ " to " ++ˢ proj₂ ab) rs) ++ˢ ")"

  -- 模块名：import 里写 full；shown 不同就是 as
  renderModName : QName → String
  renderModName q = intersperse "." (full q) ++ˢ (if shown q ==ˢ intersperse "." (full q) then "" else " as " ++ˢ shown q)

  renderBinds : ℕ → List Bind → String
  renderBinds ind []       = ""
  renderBinds ind (b ∷ bs) = " " ++ˢ renderBind ind b ++ˢ renderBinds ind bs

  renderSigs : ℕ → List (Name × Expr) → List String
  renderSigs ind []             = []
  renderSigs ind ((n , e) ∷ cs) = indentLine ind (n ++ˢ " : " ++ˢ renderExpr ind e) ∷ renderSigs ind cs

  -- 单条声明（不管顺序、不管 private 块；那是下面 renderDecls 的事）
  renderDecl : ℕ → Decl → List String
  renderDecl ind (pragma s)           = indentLine ind ("{-# " ++ˢ s ++ˢ " #-}") ∷ []
  renderDecl ind (import′ m o d _)    = indentLine ind ((if o then "open " else "") ++ˢ "import " ++ˢ renderModName m ++ˢ renderDirective d) ∷ []
  renderDecl ind (open′ m d)          = indentLine ind ("open " ++ˢ shown m ++ˢ renderDirective d) ∷ []
  renderDecl ind (fixity a n x)       = indentLine ind (assoc a ++ˢ " " ++ˢ ℕshow.show n ++ˢ " " ++ˢ x) ∷ []
    where
      assoc : Assoc → String
      assoc infixL = "infixl"
      assoc infixR = "infixr"
      assoc infixN = "infix"
  renderDecl ind (sig _ x e)          = indentLine ind (x ++ˢ " : " ++ˢ renderExpr ind e) ∷ []
  renderDecl ind (fun _ x cs)         = renderClauses ind true cs
  renderDecl ind (dataSig _ x bs e)   = indentLine ind ("data " ++ˢ x ++ˢ renderBinds ind bs ++ˢ " : " ++ˢ renderExpr ind e) ∷ []
  renderDecl ind (dataDef _ x ps cs)  = indentLine ind ("data " ++ˢ intersperse " " (x ∷ ps) ++ˢ " where") ∷ renderSigs (ind + 2) cs
  renderDecl ind (recSig _ x bs e)    = indentLine ind ("record " ++ˢ x ++ˢ renderBinds ind bs ++ˢ " : " ++ˢ renderExpr ind e) ∷ []
  renderDecl ind (recDef _ x ps d fs) = indentLine ind ("record " ++ˢ intersperse " " (x ∷ ps) ++ˢ " where") ∷ renderRecBody ind d fs
  renderDecl ind (variable′ vs)       = indentLine ind "variable" ∷ renderSigs (ind + 2) vs
  renderDecl ind (module′ x bs ds)    = indentLine ind ("module " ++ˢ x ++ˢ renderBinds ind bs ++ˢ " where") ∷ renderNestedDecls (ind + 2) ds
  renderDecl ind (patSyn n xs p) = indentLine ind ("pattern " ++ˢ intersperse " " (n ∷ xs) ++ˢ " = " ++ˢ renderPat ind p) ∷ []
  renderDecl ind (unsupported s)      = indentLine ind ("-- [unsupported] " ++ˢ s) ∷ []

  renderRecBody : ℕ → RecDir → List (Name × Expr) → List String
  renderRecBody ind (recDir co c) fs =
    (if co then indentLine (ind + 2) "coinductive" ∷ [] else [])
    ++ (constrLine c)
    ++ (if null fs then [] else indentLine (ind + 2) "field" ∷ renderSigs (ind + 4) fs)
    where
      null : ∀ {A : Set} → List A → Bool
      null [] = true
      null _  = false
      constrLine : Maybe Name → List String
      constrLine nothing  = []
      constrLine (just n) = indentLine (ind + 2) ("constructor " ++ˢ n) ∷ []

  -- data 的签名和定义相邻时合成一条：data D (A : Set) : Set where …
  renderDecls : ℕ → List Decl → List String
  renderDecls ind ds = renderDeclsWith ind false ds

  renderNestedDecls : ℕ → List Decl → List String
  renderNestedDecls ind ds = renderDeclsWith ind true ds

  renderDeclsWith : ℕ → Bool → List Decl → List String
  renderDeclsWith ind scoped [] = []
  renderDeclsWith ind scoped (s@(dataSig m x bs e) ∷ rest@(dataDef m′ x′ ps cs ∷ ds)) =
    if x ==ˢ x′ then decorate scoped ind m true false
      (indentLine ind ("data " ++ˢ x ++ˢ renderBinds ind bs ++ˢ " : " ++ˢ renderExpr ind e ++ˢ " where") ∷ renderSigs (ind + 2) cs)
      ++ renderDeclsWith ind scoped ds
    else decorate scoped ind m true false (renderDecl ind s) ++ renderDeclsWith ind scoped rest
  renderDeclsWith ind scoped (s@(recSig m x bs e) ∷ rest@(recDef m′ x′ ps d fs ∷ ds)) =
    if x ==ˢ x′ then decorate scoped ind m true false
      (indentLine ind ("record " ++ˢ x ++ˢ renderBinds ind bs ++ˢ " : " ++ˢ renderExpr ind e ++ˢ " where") ∷ renderRecBody ind d fs)
      ++ renderDeclsWith ind scoped ds
    else decorate scoped ind m true false (renderDecl ind s) ++ renderDeclsWith ind scoped rest
  renderDeclsWith ind scoped (variable′ vs ∷ ds) = indentLine ind "variable" ∷ renderSigs (ind + 2) vs ++ moreVars ds
    where
      moreVars : List Decl → List String
      moreVars (variable′ ws ∷ ds′) = renderSigs (ind + 2) ws ++ moreVars ds′
      moreVars ds′                  = renderDeclsWith ind scoped ds′
  renderDeclsWith ind scoped (s@(sig m n _) ∷ rest@(f@(fun m′ n′ _) ∷ ds)) =
    if n ==ˢ n′ ∧ eqMods m m′ then decorate scoped ind m true false (renderDecl ind s ++ renderDecl ind f) ++ renderDeclsWith ind scoped ds
    else decorate scoped ind m true (not (hasBody n rest)) (renderDecl ind s) ++ renderDeclsWith ind scoped rest
  renderDeclsWith ind scoped (d@(sig m n _) ∷ ds) =
    decorate scoped ind m true (not (hasBody n ds)) (renderDecl ind d) ++ renderDeclsWith ind scoped ds
  renderDeclsWith ind scoped (d@(fun m n _) ∷ ds) =
    decorate scoped ind m false false (renderDecl ind d) ++ renderDeclsWith ind scoped ds
  renderDeclsWith ind scoped (d ∷ ds) = renderDecl ind d ++ renderDeclsWith ind scoped ds

------------------------------------------------------------------------
-- §2  块：private / instance / abstract / postulate
-- 一个单元的声明如果带标记，整个单元包进一个块里。只有签名没有定义的单元是 postulate。
------------------------------------------------------------------------

modsOf : List Decl → Mods
modsOf []                       = plain
modsOf (sig m _ _ ∷ _)          = m
modsOf (fun m _ _ ∷ _)          = m
modsOf (dataSig m _ _ _ ∷ _)    = m
modsOf (recSig m _ _ _ ∷ _)     = m
modsOf (dataDef m _ _ _ ∷ _)    = m
modsOf (recDef m _ _ _ _ ∷ _)   = m
modsOf (_ ∷ ds)                 = modsOf ds

-- 块里只放有名字的声明；挂在单元后面的无名声明（pragma、open、fixity …）留在块外面
splitTrailing : List Decl → List Decl × List Decl
splitTrailing [] = [] , []
splitTrailing (d ∷ ds) with declName d | splitTrailing ds
... | just _  | named , rest = (d ∷ named) , rest
... | nothing | named , rest with d
...   | variable′ vs = (d ∷ named) , rest
...   | _            = named , (d ∷ rest)

-- isPost：这个单元整体是不是 postulate（只有签名）。拆成签名/定义两半输出时，由调用者按整个单元判断
-- withTC：这一半要不要带终止检查的 pragma（整块 / 签名那一半：要；定义那一半：不要，签名那边已经带了）
renderUnitDecls : ℕ → Bool → Bool → List Decl → List String
renderUnitDecls ind isPost withTC ds₀ with splitTrailing ds₀
... | ds , trailing = decorate true ind (modsOf ds) withTC isPost (renderDecls ind ds) ++ renderDecls ind trailing

------------------------------------------------------------------------
-- §3  顺序：按依赖把声明分块、排序
--
-- 块 Chunk = 一个单元的全部声明，加上紧跟在它后面的无名声明（fixity、open …）。
-- 文件头（pragma、import）单独放在最前面，不参与排序。
------------------------------------------------------------------------

record Chunk : Set where
  constructor chunk
  field
    cnames : List QName        -- 这块定义的名字（variable 块可能有好几个）
    cdecls : List Decl
open Chunk public

-- 文件头：import，和 OPTIONS pragma。别的 pragma（COMPILE、FOREIGN、BUILTIN …）留在原位：它们指着前面的声明
isOptions : String → Bool
isOptions s = isPrefix ("OPTIONS" ∷ []) (firstWord s)
  where
    firstWord : String → List String
    firstWord t = go (toList t) []
      where
        go : List Char → List Char → List String
        go []       cur = fromList (reverse cur) ∷ []
        go (c ∷ cs) cur = if primCharEquality c ' ' then fromList (reverse cur) ∷ [] else go cs (c ∷ cur)

isHeader : Decl → Bool
isHeader (pragma s)        = isOptions s
isHeader (import′ _ _ _ _) = true
isHeader _                 = false

-- 把一串声明切成块
chunksOf : List Name → List Decl → List Chunk
chunksOf path ds = reverse (go ds [])
  where
    nameOf : Name → QName
    nameOf x = mkQ (path ++ (x ∷ []))

    -- 挂到最后一块上
    attach : Decl → List Chunk → List Chunk
    attach d []       = chunk [] (d ∷ []) ∷ []
    attach d (c ∷ cs) = chunk (cnames c) (cdecls c ++ (d ∷ [])) ∷ cs

    -- A module and an opaque value may share their spelling. The module
    -- contributes namespaced projections and cannot implement the signature.
    sameValue : QName → Chunk → Bool
    sameValue q k = anyᵇ (λ n → n ==ᴺ q) (cnames k) ∧ not (anyᵇ isModule (cdecls k))
      where
        isModule : Decl → Bool
        isModule (module′ _ _ _) = true
        isModule _ = false

    hasUnit : QName → List Chunk → Bool
    hasUnit q = anyᵇ (sameValue q)

    mergeInto : QName → Decl → List Chunk → List Chunk
    mergeInto q d []       = chunk (q ∷ []) (d ∷ []) ∷ []
    mergeInto q d (k ∷ ks) = if sameValue q k then chunk (cnames k) (cdecls k ++ (d ∷ [])) ∷ ks
                             else k ∷ mergeInto q d ks

    -- 匿名定义：_ 的 fun 挂到最近的（也就是最后一块）匿名签名上，_ 的 sig 总是新开一块
    isAnonSig : Decl → Bool
    isAnonSig (sig _ "_" _) = true
    isAnonSig _             = false

    go : List Decl → List Chunk → List Chunk
    go [] acc = acc
    go (d@(module′ n _ _) ∷ ds) acc = go ds (chunk [ nameOf n ] [ d ] ∷ acc)
    go (d ∷ ds) acc with declName d
    ... | nothing with d
    ...   | variable′ vs = go ds (chunk (map (λ v → nameOf (proj₁ v)) vs) (d ∷ []) ∷ acc)
    ...   | _            = go ds (attach d acc)
    go (d ∷ ds) acc | just x with x ==ˢ "_"
    ... | true  = if isAnonSig d then go ds (chunk (nameOf "_#" ∷ []) (d ∷ []) ∷ acc) else go ds (attach d acc)   -- 名字别叫 _：会和 where 的模块段撞
    ... | false = if hasUnit (nameOf x) acc then go ds (mergeInto (nameOf x) d acc)
                  else go ds (chunk (nameOf x ∷ []) (d ∷ []) ∷ acc)

-- 这块依赖哪些块（下标）。引用先解析成单元名，再找包含它（或它的前缀，构造子归 data、子模块归模块）的块
-- 自己引用自己（递归、构造子提到自己的 data）不算：那不是排序意义上的环
depsOfChunk : (QName → Maybe Obj) → List Chunk → Chunk → List ℕ
depsOfChunk res cs ch = nubᵇ _≡ᵇ_ (concatMap find (refsDecls (cdecls ch)))
  where
    owns : QName → Chunk → Bool
    owns q k = anyᵇ (λ n → isPrefix (full n) (full q)) (cnames k)
    self : QName → Bool
    self u = owns u ch
    find : QName → List ℕ
    find q with res q
    ... | just (unit u) = if self u then [] else indices u 0 cs
      where
        indices : QName → ℕ → List Chunk → List ℕ
        indices u i []       = []
        indices u i (k ∷ ks) = if owns u k then i ∷ indices u (suc i) ks else indices u (suc i) ks
    ... | _ = []

lookupChunk : List Chunk → ℕ → Maybe Chunk
lookupChunk []       _       = nothing
lookupChunk (c ∷ cs) zero    = just c
lookupChunk (c ∷ cs) (suc n) = lookupChunk cs n

-- 深度优先：先放依赖，再放自己。遇到正在处理中的（环）就跳过。
-- 返回的是块下标的顺序。燃料 = 块数 + 1，每一层递归消耗一个。
dfsOrder : (ℕ → List ℕ) → ℕ → List ℕ
dfsOrder deps n = reverse (proj₁ (visitAll (suc n) (upTo n) ([] , [])))
  where
    -- 状态：(已输出（倒序）, 正在处理)
    St : Set
    St = List ℕ × List ℕ

    mutual
      visit : ℕ → ℕ → St → St
      visit zero    i st = st
      visit (suc f) i (done , busy) =
        if elemᵇ _≡ᵇ_ i done ∨ elemᵇ _≡ᵇ_ i busy then done , busy
        else (let st′ = visitAll f (deps i) (done , i ∷ busy)
              in (i ∷ proj₁ st′) , proj₂ st′)        -- busy 里的 i 留着无妨：done 里有了它

      visitAll : ℕ → List ℕ → St → St
      visitAll f []       st = st
      visitAll f (i ∷ is) st = visitAll f is (visit f i st)

-- 环：顺序 L 里，第 i 个块依赖了排在它后面（含自己之后）的块，就说 [i , j] 是一段环。
-- 把所有这样的区间并起来，区间里的块先出全部签名、再出全部定义。
-- 这里用最简单的办法：标出每个位置是否在某段环里。
cycleMask : (ℕ → List ℕ) → List ℕ → List Bool
cycleMask deps L = map inSpan (upTo (length L))
  where
    posOf : ℕ → ℕ
    posOf x = go 0 L
      where
        go : ℕ → List ℕ → ℕ
        go i []       = 0
        go i (y ∷ ys) = if x ≡ᵇ y then i else go (suc i) ys
    -- 第 p 位的块的最晚依赖位置
    spans : List (ℕ × ℕ)
    spans = concatMap (λ p → concatMap (λ x → concatMap (λ d → let q = posOf d in if (p <ᵇ q) ∨ (p ≡ᵇ q) then (p , q) ∷ [] else []) (deps x)) (maybeToList (lookup′ L p))) (upTo (length L))
      where
        maybeToList : Maybe ℕ → List ℕ
        maybeToList nothing  = []
        maybeToList (just x) = x ∷ []
        lookup′ : List ℕ → ℕ → Maybe ℕ
        lookup′ []       _       = nothing
        lookup′ (x ∷ xs) zero    = just x
        lookup′ (x ∷ xs) (suc n) = lookup′ xs n
    inSpan : ℕ → Bool
    inSpan p = anyᵇ (λ s → (proj₁ s ≤ᵇ p) ∧ (p ≤ᵇ proj₂ s)) spans

-- 签名部分 / 定义部分
sigPart defPart : List Decl → List Decl
sigPart = filterᵇ isSigD
  where
    isSigD : Decl → Bool
    isSigD (sig _ _ _)        = true
    isSigD (dataSig _ _ _ _)  = true
    isSigD (recSig _ _ _ _)   = true
    isSigD (fixity _ _ _)     = true
    isSigD (variable′ _)      = true
    isSigD (module′ _ _ _)    = true   -- 模块拆不开，整个算签名部分
    isSigD _                  = false
defPart = filterᵇ isDefD
  where
    isDefD : Decl → Bool
    isDefD (fun _ _ _)        = true
    isDefD (dataDef _ _ _ _)  = true
    isDefD (recDef _ _ _ _ _) = true
    isDefD (open′ _ _)        = true
    isDefD (patSyn _ _ _) = true
    isDefD (unsupported _)    = true
    isDefD _                  = false

maybe′ : ∀ {A B : Set} → (A → B) → B → Maybe A → B
maybe′ f b nothing  = b
maybe′ f b (just a) = f a

-- 把一串声明（某个模块里的）排好序、分好块、渲染成行。res 是预先算好的解析函数（整个文件一份）
lookupDeps : List (List ℕ) → ℕ → List ℕ
lookupDeps [] _ = []
lookupDeps (ds ∷ _) zero = ds
lookupDeps (_ ∷ rest) (suc n) = lookupDeps rest n

-- Pass computed tables as arguments. Agda's GHC backend lifts where bindings
-- to functions; recomputing chunks/graphs at every edge made large self-hosting
-- round trips unnecessarily expensive.
-- Preserve the lexical order of a well-scoped module. In particular a mutual
-- group may interleave signatures independently of the order of its bodies.
-- Transports can append a new dependency after its caller, so check references
-- before choosing the order and retain the graph scheduler for those edits.
inScopeOrder : (QName → Maybe Obj) → List Name → List QName → List Decl → Bool
inScopeOrder resolve path available [] = true
inScopeOrder resolve path available (d ∷ ds) =
  allᵇ ready (refsDecl d) ∧ inScopeOrder resolve path available′ ds
  where
    names : Decl → List Name
    names (variable′ vs) = map proj₁ vs
    names d with declName d
    ... | just n = [ n ]
    ... | nothing = []
    available′ = map (λ n → mkQ (path ++ [ n ])) (names d) ++ available
    known : Maybe Obj → Bool
    known (just (unit u)) = elemᵇ _==ᴺ_ u available′
    known _ = true
    ready : QName → Bool
    ready q = if isPrefix path (full q) then known (resolve q) else true

renderBody : (QName → Maybe Obj) → ℕ → List Name → List Decl → List String
renderBody res ind path ds = if inScopeOrder res path [] ds then renderNestedDecls ind ds
  else renderDecls ind (filterᵇ isHeader ds) ++ arrange (chunksOf path (filterᵇ (λ d → not (isHeader d)) ds))
  where
    mutual
      arrange : List Chunk → List String
      arrange cs = graph cs (map (depsOfChunk res cs) cs)

      graph : List Chunk → List (List ℕ) → List String
      graph cs table = ordered cs table (dfsOrder (lookupDeps table) (length cs))

      ordered : List Chunk → List (List ℕ) → List ℕ → List String
      ordered cs table order = emit cs (zip order (cycleMask (lookupDeps table) order))

      chunkAt : List Chunk → ℕ → List Decl
      chunkAt cs i = maybe′ cdecls [] (lookupChunk cs i)

      emitSpan : List Chunk → List ℕ → List String
      emitSpan cs span = concatMap (λ j → renderUnitDecls ind (isPostulate (chunkAt cs j)) true (sigPart (chunkAt cs j))) span
                     ++ concatMap (λ j → renderUnitDecls ind false false (defPart (chunkAt cs j))) span

      emit : List Chunk → List (ℕ × Bool) → List String
      emit cs [] = []
      emit cs ((i , false) ∷ rest) = renderUnitDecls ind (isPostulate (chunkAt cs i)) true (chunkAt cs i) ++ emit cs rest
      emit cs ((i , true) ∷ rest) = collect cs (i ∷ []) rest

      collect : List Chunk → List ℕ → List (ℕ × Bool) → List String
      collect cs acc ((j , true) ∷ rest) = collect cs (acc ++ (j ∷ [])) rest
      collect cs acc rest = emitSpan cs acc ++ emit cs rest

------------------------------------------------------------------------
-- §4  整个文件
------------------------------------------------------------------------

renderWithTables : Code → List Unit → List Unit → String
renderWithTables c us es = unlines (renderDecls 0 pragmas ++ (header ∷ "" ∷ []) ++ renderBody res 2 (full (modName c)) rest) ++ˢ "\n"
  where
    isPragma : Decl → Bool
    isPragma (pragma s) = isOptions s
    isPragma _          = false
    pragmas = filterᵇ isPragma (decls c)
    rest    = filterᵇ (λ d → not (isPragma d)) (decls c)
    header  = "module " ++ˢ intersperse "." (full (modName c)) ++ˢ renderBinds 0 (params c) ++ˢ " where"
    -- 单元表只算一次
    res : QName → Maybe Obj
    res = resolveIn (modName c) us es

render : Code → String
render c = renderWithTables c (units c) (extUnits c)
