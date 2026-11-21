------------------------------------------------------------------------
-- Test/TransportTest.agda —— 在文档里的 A、C 两个模块上试搬运。全是 refl：Agda 算给你看。
------------------------------------------------------------------------
module Test.TransportTest where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)

open import Code
open import Code.Transport
open import Code.Lift using (checkLift; liftSpec; endpointLift)
open import Code.Render using (render)

-- 文档里的两个模块，直接写成 Code 值（和 Dump 导出来的一致；要用 parse 读 s-expr 见 Test/ParseSmall）
A· C· : Name → QName
A· x = mkQ ("A" ∷ x ∷ [])
C· x = mkQ ("C" ∷ x ∷ [])

ℕᴬ : Expr
ℕᴬ = def (qn ("A" ∷ "ℕ" ∷ []) "A.ℕ")

sucᴬ zeroᴬ : Expr
sucᴬ  = con (qn ("A" ∷ "ℕ" ∷ "suc" ∷ []) "A.suc")
zeroᴬ = con (qn ("A" ∷ "ℕ" ∷ "zero" ∷ []) "A.zero")

sucP zeroP : Pat
sucP  = conP (qn ("A" ∷ "ℕ" ∷ "suc" ∷ []) "A.suc") (vis (varP "n") ∷ [])
zeroP = conP (qn ("A" ∷ "ℕ" ∷ "zero" ∷ []) "A.zero") []

-- A 暴露给 C 的接口 = A 的声明（这里 A 只有 data ℕ）。父亲建洞时填进 import′ A 的 assumes
A-iface : List Decl
A-iface = dataSig plain "ℕ" [] (set 0)
        ∷ dataDef plain "ℕ" [] (("zero" , ℕᴬ) ∷ ("suc" , fun′ (vis ℕᴬ) ℕᴬ) ∷ []) ∷ []

C₀ : Code
C₀ = code (qn ("C" ∷ []) "C") []
  ( import′ (qn ("A" ∷ []) "A") false everything A-iface
  ∷ sig plain "one" ℕᴬ
  ∷ fun plain "one" (clause (head (C· "one") []) (rhs (app sucᴬ (vis zeroᴬ))) [] ∷ [])
  ∷ sig plain "two" ℕᴬ
  ∷ fun plain "two" (clause (head (C· "two") []) (rhs (app sucᴬ (vis (def (C· "one"))))) [] ∷ [])
  ∷ sig plain "double" (fun′ (vis ℕᴬ) ℕᴬ)
  ∷ fun plain "double"
      ( clause (head (C· "double") (vis zeroP ∷ [])) (rhs zeroᴬ) []
      ∷ clause (head (C· "double") (vis sucP ∷ [])) (rhs (app sucᴬ (vis (app sucᴬ (vis (app (def (C· "double")) (vis (var "n")))))))) []
      ∷ [])
  ∷ sig plain "f" (fun′ (vis ℕᴬ) ℕᴬ)
  ∷ fun plain "f" (clause (head (C· "f") (vis (varP "n") ∷ [])) (rhs (app (def (qn ("C" ∷ "_" ∷ "helper" ∷ []) "helper")) (vis (var "n"))))
        ( sig (mods true false false check) "helper" (fun′ (vis ℕᴬ) ℕᴬ)
        ∷ fun plain "helper" (clause (head (qn ("C" ∷ "_" ∷ "helper" ∷ []) "helper") (vis (varP "m") ∷ [])) (rhs (app sucᴬ (vis (var "m")))) [] ∷ [])
        ∷ []) ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- 先看看范畴长什么样：四个单元；构造子 A.ℕ.suc 都归到接口对象 ⟨A.ℕ⟩ 上
------------------------------------------------------------------------

_ : map (shown ∘ uname) (units C₀) ≡ "one" ∷ "two" ∷ "double" ∷ "f" ∷ []
_ = refl

-- two 用到 one 和 ⟨A.ℕ⟩（还有形式上的 flags）；箭头读作 u → v
_ : map (λ a → a) (dependents C₀ (unit (C· "one"))) ≡ unit (C· "two") ∷ []
_ = refl

_ : dependents C₀ (ext (A· "ℕ")) ≡ unit (C· "one") ∷ unit (C· "two") ∷ unit (C· "double") ∷ unit (C· "f") ∷ []
_ = refl

------------------------------------------------------------------------
-- 搬运 1：改名 one → uno。接口（类型 A.ℕ）没变 ⇒ 没有义务；two 里的引用自动跟着改
------------------------------------------------------------------------

P₁ : Plan
P₁ = plan "one 这个名字太像数字了，改叫 uno"
          (sig plain "uno" ℕᴬ ∷ fun plain "uno" (clause (head (C· "uno") []) (rhs (app sucᴬ (vis zeroᴬ))) [] ∷ []) ∷ [])
          (unit (C· "one") ⇝ unit (C· "uno") ∷ [])

C₁ : Code
C₁ = apply P₁ C₀

_ : frontier C₀ C₁ P₁ ≡ []
_ = refl

_ : validate C₀ P₁ C₁ ≡ []
_ = refl

-- two 的右边现在引用 uno
_ : lookupUnit (units C₁) (C· "two") ≡
    just (unitOf (C· "two") (sig plain "two" ℕᴬ ∷ fun plain "two" (clause (head (C· "two") []) (rhs (app sucᴬ (vis (def (C· "uno"))))) [] ∷ []) ∷ []))
_ = refl

------------------------------------------------------------------------
-- 搬运 2：把 one 的类型改成 A.ℕ → A.ℕ。接口变了 ⇒ two 有义务；没人管它 ⇒ frontier 里有它
------------------------------------------------------------------------

P₂ : Plan
P₂ = plan "one 改成一个函数"
          (sig plain "one" (fun′ (vis ℕᴬ) ℕᴬ) ∷ fun plain "one" (clause (head (C· "one") (vis (varP "n") ∷ [])) (rhs (app sucᴬ (vis (var "n")))) [] ∷ []) ∷ [])
          (keep (unit (C· "one")) ∷ [])

C₂ : Code
C₂ = apply P₂ C₀

_ : changed C₀ C₂ P₂ ≡ unit (C· "one") ∷ []
_ = refl

_ : frontier C₀ C₂ P₂ ≡ unit (C· "two") ∷ []
_ = refl

_ : validate C₀ P₂ C₂ ≡ unsettled (unit (C· "two")) ∷ []
_ = refl

-- 补上"two 看过了，照旧"，义务就算完成了（对不对由 agda 说——这里 two = A.suc one 其实不再对了）
P₂′ : Plan
P₂′ = record P₂ { moves = keep (unit (C· "one")) ∷ keep (unit (C· "two")) ∷ [] }

_ : validate C₀ P₂′ (apply P₂′ C₀) ≡ []
_ = refl

------------------------------------------------------------------------
-- 搬运 3：丢掉 f（f ⇝ ⊥）。没人用 f ⇒ 没义务；f 连 where 一起消失
------------------------------------------------------------------------

P₃ : Plan
P₃ = plan "f 没人用了" [] (unit (C· "f") ⇝ ⊥ ∷ [])

_ : validate C₀ P₃ (apply P₃ C₀) ≡ []
_ = refl

_ : map (shown ∘ uname) (units (apply P₃ C₀)) ≡ "one" ∷ "two" ∷ "double" ∷ []
_ = refl

-- 反过来：丢掉 one，two 就悬空了 —— 义务没完成，而且 two 的引用指向不存在的名字
P₃′ : Plan
P₃′ = plan "丢掉 one" [] (unit (C· "one") ⇝ ⊥ ∷ [])

_ : validate C₀ P₃′ (apply P₃′ C₀) ≡ unsettled (unit (C· "two")) ∷ dangling (unit (C· "two")) (C· "one") ∷ []
_ = refl

------------------------------------------------------------------------
-- 搬运 4：拆。double 里抽出 twice（一到多：double ⇝ double , double ⇝ twice）
------------------------------------------------------------------------

P₄ : Plan
P₄ = plan "double 里 suc (suc _) 抽成 twice"
          ( sig plain "twice" (fun′ (vis ℕᴬ) ℕᴬ)
          ∷ fun plain "twice" (clause (head (C· "twice") (vis (varP "n") ∷ [])) (rhs (app sucᴬ (vis (app sucᴬ (vis (var "n")))))) [] ∷ [])
          ∷ sig plain "double" (fun′ (vis ℕᴬ) ℕᴬ)
          ∷ fun plain "double"
              ( clause (head (C· "double") (vis (conP (qn ("A" ∷ "ℕ" ∷ "zero" ∷ []) "A.zero") []) ∷ [])) (rhs zeroᴬ) []
              ∷ clause (head (C· "double") (vis (conP (qn ("A" ∷ "ℕ" ∷ "suc" ∷ []) "A.suc") (vis (varP "n") ∷ [])) ∷ []))
                       (rhs (app (def (C· "twice")) (vis (app (def (C· "double")) (vis (var "n")))))) []
              ∷ [])
          ∷ [])
          (unit (C· "double") ⇝ unit (C· "double") ∷ unit (C· "double") ⇝ unit (C· "twice") ∷ [])

_ : validate C₀ P₄ (apply P₄ C₀) ≡ []
_ = refl

_ : map (shown ∘ uname) (units (apply P₄ C₀)) ≡ "one" ∷ "two" ∷ "twice" ∷ "double" ∷ "f" ∷ []
_ = refl

------------------------------------------------------------------------
-- 搬运 5：从 ⊥ 来。新写一个 three
------------------------------------------------------------------------

P₅ : Plan
P₅ = plan "加一个 three"
          (sig plain "three" ℕᴬ ∷ fun plain "three" (clause (head (C· "three") []) (rhs (app sucᴬ (vis (def (C· "two"))))) [] ∷ []) ∷ [])
          (⊥ ⇝ unit (C· "three") ∷ [])

_ : validate C₀ P₅ (apply P₅ C₀) ≡ []
_ = refl

-- 忘了写 proarrow 的新单元会被抓出来：它从哪来的？
P₅′ : Plan
P₅′ = record P₅ { moves = [] }

_ : validate C₀ P₅′ (apply P₅′ C₀) ≡ orphanUnit (unit (C· "three")) ∷ []
_ = refl

------------------------------------------------------------------------
-- 搬运 6：动孩子的接口。C 需要 A 多暴露一个 add : ℕ → ℕ → ℕ（⊥ ⇝ ⟨A.add⟩），还顺手用上它
--   这不是 C 自己能做完的事：affectedChildren 里有 A，restrict 给出发给 A 的 SpecΔ
------------------------------------------------------------------------

A-iface′ : List Decl
A-iface′ = A-iface ++ (sig plain "add" (fun′ (vis ℕᴬ) (fun′ (vis ℕᴬ) ℕᴬ)) ∷ [])

P₆ : Plan
P₆ = plan "要 A 提供加法，two 用它来算"
          ( import′ (qn ("A" ∷ []) "A") false everything A-iface′
          ∷ sig plain "two" ℕᴬ
          ∷ fun plain "two" (clause (head (C· "two") []) (rhs (app (app (def (qn ("A" ∷ "add" ∷ []) "A.add")) (vis (def (C· "one")))) (vis (def (C· "one"))))) [] ∷ [])
          ∷ [])
          (⊥ ⇝ ext (A· "add") ∷ keep (unit (C· "two")) ∷ [])

C₆ : Code
C₆ = apply P₆ C₀

_ : validate C₀ P₆ C₆ ≡ []
_ = refl

_ : affectedChildren C₆ P₆ ≡ mkQ ("A" ∷ []) ∷ []
_ = refl

_ : restrict C₆ P₆ (mkQ ("A" ∷ [])) ≡ specΔ (mkQ ("A" ∷ [])) A-iface′ (⊥ ⇝ ext (A· "add") ∷ [])
_ = refl

-- A 那边收到 SpecΔ 以后，它的桩长这样：只有接口的模块。它要用真代码替换这个桩，接口不变
_ : map (shown ∘ uname) (units (stubOf (restrict C₆ P₆ (mkQ ("A" ∷ []))))) ≡ "ℕ" ∷ "add" ∷ []
_ = refl

-- 反过来，孩子的接口被改（A.ℕ 多一个构造子 pred）：所有用 A.ℕ 的单元都有义务（匹配可能不穷尽了）
A-iface″ : List Decl
A-iface″ = dataSig plain "ℕ" [] (set 0)
         ∷ dataDef plain "ℕ" [] (("zero" , ℕᴬ) ∷ ("suc" , fun′ (vis ℕᴬ) ℕᴬ) ∷ ("pred" , fun′ (vis ℕᴬ) ℕᴬ) ∷ []) ∷ []

P₇ : Plan
P₇ = plan "A.ℕ 多一个 pred" (import′ (qn ("A" ∷ []) "A") false everything A-iface″ ∷ []) (keep (ext (A· "ℕ")) ∷ [])

_ : changed C₀ (apply P₇ C₀) P₇ ≡ ext (A· "ℕ") ∷ []
_ = refl

_ : frontier C₀ (apply P₇ C₀) P₇ ≡ unit (C· "one") ∷ unit (C· "two") ∷ unit (C· "double") ∷ unit (C· "f") ∷ []
_ = refl

------------------------------------------------------------------------
-- 记忆沿 proarrow 走：one 的笔记跟到 uno 身上，再加上这次的 why；丢掉的 f 的笔记进 ⊥
------------------------------------------------------------------------

M₀ : Memory
M₀ = (unit (C· "one") , "one 是 1" ∷ []) ∷ (unit (C· "f") , "f 是个例子" ∷ []) ∷ []

_ : inherit P₁ M₀ ≡ (unit (C· "f") , "f 是个例子" ∷ []) ∷ (unit (C· "uno") , "one 是 1" ∷ "one 这个名字太像数字了，改叫 uno" ∷ []) ∷ []
_ = refl

_ : inherit P₃ M₀ ≡ (unit (C· "one") , "one 是 1" ∷ []) ∷ (⊥ , "f 是个例子" ∷ "f 没人用了" ∷ []) ∷ []
_ = refl

------------------------------------------------------------------------
-- flags 包络：孩子 infective 不能多，coinfective 不能少
------------------------------------------------------------------------

_ : flagsOK ("--guardedness" ∷ "--safe" ∷ []) ("--safe" ∷ []) ≡ true
_ = refl
_ : flagsOK ("--safe" ∷ []) ("--guardedness" ∷ "--safe" ∷ []) ≡ false     -- 孩子多了 infective
_ = refl
_ : flagsOK ("--safe" ∷ []) [] ≡ false                                      -- 孩子少了 coinfective
_ = refl

------------------------------------------------------------------------
-- V2 回归：未被正文引用的子接口也能作搬运靶；更新 A 不能抹掉 B 的接口。
------------------------------------------------------------------------

unusedChildLemma : Plan
unusedChildLemma = plan "给 A 增加尚未使用的引理"
  (import′ (mkQ ("A" ∷ [])) false everything
    (A-iface ++ (sig plain "unused" ℕᴬ ∷ [])) ∷ []) (⊥ ⇝ ext (A· "unused") ∷ [])

_ : validate C₀ unusedChildLemma (apply unusedChildLemma C₀)
    ≡ []
_ = refl

siblingIfaces : Code
siblingIfaces = code (mkQ ("Parent" ∷ [])) []
  (import′ (mkQ ("A" ∷ [])) false everything A-iface
   ∷ import′ (mkQ ("B" ∷ [])) false everything (sig plain "b" (set 0) ∷ []) ∷ [])

_ : map assumes (imports (withChildIface (mkQ ("A" ∷ [])) A-iface′ siblingIfaces))
    ≡ A-iface′ ∷ (sig plain "b" (set 0) ∷ []) ∷ []
_ = refl

------------------------------------------------------------------------
-- Record constructors live in the enclosing module: M.c belongs to M.R.
-- Keep signatures free of M.R so only constructor expressions/patterns
-- can create the dependency on the record.
------------------------------------------------------------------------

M· : Name → QName
M· x = mkQ ("M" ∷ x ∷ [])

R-decls : RecDir → List Decl
R-decls d = recSig plain "R" [] (set 0) ∷ recDef plain "R" [] d [] ∷ []

R-call : List Decl
R-call = sig plain "caller" meta
       ∷ fun plain "caller" (clause (head (M· "caller") []) (rhs (con (M· "c"))) [] ∷ []) ∷ []

R-match : List Decl
R-match = sig plain "match" meta
        ∷ fun plain "match"
            (clause (head (M· "match") (vis (conP (M· "c") []) ∷ [])) (rhs (set 0)) [] ∷ []) ∷ []

recordCode : RecDir → Code
recordCode d = code (mkQ ("M" ∷ [])) [] (R-decls d ++ R-call ++ R-match)

R₀ : Code
R₀ = recordCode (recDir false (just "c"))

_ : resolve R₀ (M· "c") ≡ just (unit (M· "R"))
_ = refl

-- Constructor ownership is an exact name match, not another prefix rule.
_ : resolve R₀ (mkQ ("M" ∷ "c" ∷ "extra" ∷ [])) ≡ nothing
_ = refl

_ : resolve (recordCode (recDir false nothing)) (M· "c") ≡ nothing
_ = refl

_ : validate R₀ (plan "identity" [] []) R₀ ≡ []
_ = refl

_ : arrows R₀ ≡ (unit (M· "R") , flags)
              ∷ (unit (M· "caller") , unit (M· "R")) ∷ (unit (M· "caller") , flags)
              ∷ (unit (M· "match") , unit (M· "R")) ∷ (unit (M· "match") , flags) ∷ []
_ = refl

changeR : RecDir → Plan
changeR d = plan "change record directives" (R-decls d) (keep (unit (M· "R")) ∷ [])

renameConstructor : Plan
renameConstructor = changeR (recDir false (just "c′"))

_ : preserves R₀ (apply renameConstructor R₀) renameConstructor (keep (unit (M· "R"))) ≡ false
_ = refl

_ : changed R₀ (apply renameConstructor R₀) renameConstructor ≡ unit (M· "R") ∷ []
_ = refl

_ : frontier R₀ (apply renameConstructor R₀) renameConstructor
    ≡ unit (M· "caller") ∷ unit (M· "match") ∷ []
_ = refl

-- Removing/adding a constructor and changing coinductive also change Iface.
_ : changed R₀ (apply (changeR (recDir false nothing)) R₀) (changeR (recDir false nothing))
    ≡ unit (M· "R") ∷ []
_ = refl

_ : changed (recordCode (recDir false nothing)) R₀ (changeR (recDir false (just "c")))
    ≡ unit (M· "R") ∷ []
_ = refl

_ : changed R₀ (apply (changeR (recDir true (just "c"))) R₀) (changeR (recDir true (just "c")))
    ≡ unit (M· "R") ∷ []
_ = refl

_ : satisfies (specΔ (modName R₀) (R-decls (recDir false (just "c"))) []) R₀ ≡ true
_ = refl

_ : satisfies (specΔ (modName R₀) (R-decls (recDir false (just "c′"))) []) R₀ ≡ false
_ = refl

_ : satisfies (specΔ (modName R₀) (R-decls (recDir true (just "c"))) []) R₀ ≡ false
_ = refl

-- The record wins over the shorter enclosing module for local and child units.
nestedRecord : Code
nestedRecord = code (mkQ ("M" ∷ [])) []
  (module′ "Sub" [] (R-decls (recDir false (just "c"))) ∷ [])

_ : resolve nestedRecord (mkQ ("M" ∷ "Sub" ∷ "c" ∷ []))
    ≡ just (unit (mkQ ("M" ∷ "Sub" ∷ "R" ∷ [])))
_ = refl

boxSig boxDef : Decl
boxSig = recSig plain "Box" (bind hidden ("T" ∷ []) (set 0) ∷ []) (set 1)
boxDef = recDef plain "Box" ("T" ∷ []) (recDir false (just "mkBox")) (("value" , var "T") ∷ [])

childRecord : Code
childRecord = code (mkQ ("C" ∷ [])) []
  (import′ (mkQ ("A" ∷ [])) false everything
    (boxSig ∷ boxDef ∷ module′ "Sub" [] (R-decls (recDir false (just "c"))) ∷ []) ∷ [])

_ : resolve childRecord (A· "mkBox") ≡ just (ext (A· "Box"))
_ = refl

_ : resolve childRecord (mkQ ("A" ∷ "Sub" ∷ "c" ∷ []))
    ≡ just (ext (mkQ ("A" ∷ "Sub" ∷ "R" ∷ [])))
_ = refl

-- Signatures supply parameters/sort; definitions supply directives/fields,
-- whichever order they are encountered in.
boxIface : Iface
boxIface = ifaceRec (bind hidden ("T" ∷ []) (set 0) ∷ []) (set 1)
  (recDir false (just "mkBox")) (("value" , var "T") ∷ [])

_ : ifaceOfDecls (boxSig ∷ boxDef ∷ []) ≡ boxIface
_ = refl

_ : ifaceOfDecls (boxDef ∷ boxSig ∷ []) ≡ boxIface
_ = refl

_ : ifaceOfDecls (boxSig ∷ [])
    ≡ ifaceRec (bind hidden ("T" ∷ []) (set 0) ∷ []) (set 1) (recDir false nothing) []
_ = refl

_ : ifaceOfDecls (boxDef ∷ [])
    ≡ ifaceRec [] meta (recDir false (just "mkBox")) (("value" , var "T") ∷ [])
_ = refl

-- Renaming type references leaves the record's directives intact.
_ : renameIface (requalify (mkQ ("A" ∷ [])) (mkQ ("C" ∷ [])))
      (ifaceRec (bind hidden ("T" ∷ []) (def (A· "Sort")) ∷ []) (def (A· "Sort"))
        (recDir true (just "mkBox")) (("value" , def (A· "Value")) ∷ []))
    ≡ ifaceRec (bind hidden ("T" ∷ []) (def (C· "Sort")) ∷ []) (def (C· "Sort"))
        (recDir true (just "mkBox")) (("value" , def (C· "Value")) ∷ [])
_ = refl

-- apply appends a new record after its caller; Render must move it before
-- the caller using the constructor dependency alone.
beforeRecord : Code
beforeRecord = code (mkQ ("M" ∷ [])) [] R-call

addRecord : Plan
addRecord = plan "add R" (R-decls (recDir false (just "c"))) (⊥ ⇝ unit (M· "R") ∷ [])

afterRecord : Code
afterRecord = apply addRecord beforeRecord

_ : map uname (units afterRecord) ≡ M· "caller" ∷ M· "R" ∷ []
_ = refl

_ : validate beforeRecord addRecord afterRecord ≡ []
_ = refl

_ : render afterRecord
    ≡ "module M where\n\n  record R : Set where\n    constructor c\n  caller : _\n  caller = c\n"
_ = refl

------------------------------------------------------------------------
-- Session B: core spec helpers versus named and anonymous tests.
------------------------------------------------------------------------

B-body : Name → Expr → Decl
B-body n e = fun plain n (clause (head (M· n) []) (rhs e) [] ∷ [])

B-function : Name → Expr → List Decl
B-function n e = sig plain n (set 0) ∷ B-body n e ∷ []

B-header B-core B-fixture B-named B-anonymous B-tests B-iface : List Decl
B-header = pragma "OPTIONS --safe"
  ∷ import′ (mkQ ("Agda" ∷ "Builtin" ∷ "Nat" ∷ [])) false everything []
  ∷ open′ (mkQ ("Agda" ∷ "Builtin" ∷ "Nat" ∷ [])) everything
  ∷ variable′ (("T" , set 0) ∷ []) ∷ []
-- law -> helper -> leaf -> record constructor; cycleLaw -> cycle -> cycleLaw.
-- Deliberately put the obligations first to require transitive closure.
B-core = R-decls (recDir false (just "c")) ++
  (sig plain "operation" (set 0)
  ∷ sig plain "law" (def (M· "helper"))
  ∷ sig plain "cycleLaw" (def (M· "cycle"))
  ∷ fixity infixL 5 "helper" ∷ []) ++
  B-function "leaf" (con (M· "c")) ++
  B-function "helper" (def (M· "leaf")) ++
  B-function "cycle" (def (M· "cycleLaw"))
B-fixture = B-function "fixture" (def (M· "helper"))
B-named = fixity infixR 6 "ex1" ∷ sig plain "ex1" (def (M· "fixture"))
  ∷ B-body "ex1" (def (M· "fixture")) ∷ []
B-anonymous = sig plain "_" (def (M· "helper")) ∷ B-body "_" (def (M· "helper"))
  -- Even an anonymous signature without a body must not seed the core.
  ∷ sig plain "_" (def (M· "anonymousOnly")) ∷ []
B-tests = B-fixture ++ B-named ++ B-function "anonymousOnly" (set 0) ++ B-anonymous
B-iface = B-header ++ B-core ++ B-tests

B-δ : SpecΔ
B-δ = specΔ (mkQ ("M" ∷ [])) B-iface []

B-code : List Decl → Code
B-code = code (child B-δ) []

B-stub : Code
B-stub = stubOf B-δ

_ : map shown (coreNames (child B-δ) B-iface)
    ≡ "T" ∷ "R" ∷ "operation" ∷ "law" ∷ "cycleLaw" ∷ "leaf" ∷ "helper" ∷ "cycle" ∷ []
_ = refl

-- Preserve headers, variables, core fixity and complete helper bodies.
_ : decls B-stub ≡ localizeTo (child B-δ) (B-header ++ B-core)
_ = refl

_ : satisfies B-δ B-stub ≡ true
_ = refl

-- Obligations may acquire implementations, while helpers remain unchanged.
_ : satisfies B-δ (B-code (decls B-stub ++ (B-body "operation" (set 0) ∷ []))) ≡ true
_ = refl

_ : satisfies B-δ (B-code B-iface) ≡ true
_ = refl

B-replace : Name → Expr → List Decl → List Decl
B-replace n e = map replace
  where
    replace : Decl → Decl
    replace d@(fun _ m _) with m ==ˢ n
    ... | true = B-body n e
    ... | false = d
    replace d = d

_ : satisfies B-δ (B-code (B-replace "helper" (set 1) B-iface)) ≡ false
_ = refl

-- Missing helpers and missing obligations are both rejected.
B-without : Name → List Decl → List Decl
B-without n = filterᵇ keepDecl
  where
    keepDecl : Decl → Bool
    keepDecl d with declName d
    ... | just m with m ==ˢ n
    ... | true = false
    ... | false = true
    keepDecl d | nothing = true

_ : satisfies B-δ (B-code (B-without "leaf" B-iface)) ≡ false
_ = refl

_ : satisfies B-δ (B-code (B-without "law" B-iface)) ≡ false
_ = refl

-- Omitted tests are fine; included named tests/fixtures must be verbatim.
_ : satisfies B-δ (B-code (B-replace "ex1" (set 1) B-iface)) ≡ false
_ = refl

_ : satisfies B-δ (B-code (B-replace "fixture" (set 1) B-iface)) ≡ false
_ = refl

_ : satisfies B-δ (B-code (decls B-stub ++ (sig plain "ex1" (def (M· "fixture")) ∷ []))) ≡ false
_ = refl

-- Anonymous tests never impose equality on a child's anonymous definitions.
_ : satisfies B-δ (B-code (B-replace "_" (set 1) B-iface)) ≡ true
_ = refl

-- Shared imports/opens and core helpers are never re-appended.
_ : decls (withTests B-stub B-iface)
    ≡ decls B-stub ++ localizeTo (child B-δ) B-tests
_ = refl

-- A named test already in main suppresses both its declarations and fixity;
-- a missing fixture is still appended. Anonymous tests are always appended.
_ : decls (withTests (B-code (decls B-stub ++ B-named)) B-iface)
    ≡ (decls B-stub ++ B-named) ++ localizeTo (child B-δ)
      (B-fixture ++ B-function "anonymousOnly" (set 0) ++ B-anonymous)
_ = refl

_ : decls (withTests (B-code B-iface) B-iface)
    ≡ B-iface ++ localizeTo (child B-δ) B-anonymous
_ = refl

-- New scope declarations are appended, even when tests were copied to main.
B-scope : List Decl
B-scope = import′ (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ [])) false everything []
  ∷ open′ (mkQ ("Agda" ∷ "Builtin" ∷ "Bool" ∷ [])) everything ∷ []

_ : decls (withTests (B-code B-iface) (B-scope ++ B-iface))
    ≡ B-iface ++ B-scope ++ localizeTo (child B-δ) B-anonymous
_ = refl

-- External helper references must not pull a same-spelled local test into core.
_ : coreNames (child B-δ)
      (import′ (mkQ ("A" ∷ [])) false everything (sig plain "helper" (set 0) ∷ [])
      ∷ sig plain "law" (def (A· "helper")) ∷ B-function "helper" (set 0))
    ≡ M· "law" ∷ []
_ = refl

------------------------------------------------------------------------
-- Session E: expose test propositions to refutations, validate anonymous
-- declarations, and check lifted endpoints after appending spec tests.
------------------------------------------------------------------------

E-eq : Expr → Expr → Expr
E-eq a b = app (app (def (mkQ ("Agda" ∷ "Builtin" ∷ "Equality" ∷ "_≡_" ∷ []))) (vis a)) (vis b)

E-zero E-one : Expr
E-zero = lit (natL 0)
E-one = lit (natL 1)

E-bare E-proof : List Decl
E-bare = sig plain "_" (E-eq E-zero E-one) ∷ []
E-proof = sig plain "_" (E-eq E-zero E-zero) ∷ B-body "_" (var "refl") ∷ []

_ : specProblem E-bare ≡ just "spec: anonymous '_' declarations must include a definition body (e.g. '_ = refl'); give postulated obligations an explicit name"
_ = refl

_ : specProblem E-proof ≡ nothing
_ = refl

-- A later anonymous body must not hide an earlier anonymous postulate.
_ : specProblem (E-bare ++ E-proof) ≡ specProblem E-bare
_ = refl

_ : specProblem (module′ "Nested" [] E-bare ∷ []) ≡ specProblem E-bare
_ = refl

_ : specProblem (sig plain "obligation" (E-eq E-zero E-one) ∷ []) ≡ nothing
_ = refl

E-helpers E-tests E-iface : List Decl
E-helpers = B-function "leaf" E-one ++ B-function "helper" (def (M· "leaf"))
E-tests = sig plain "namedTest" (E-eq (def (M· "helper")) E-one)
  ∷ B-body "namedTest" (var "refl")
  ∷ sig plain "_" (E-eq (def (M· "helper")) E-one) ∷ B-body "_" (var "refl")
  ∷ sig plain "_" (E-eq E-zero E-zero) ∷ B-body "_" (var "refl") ∷ []
E-iface = sig plain "specTest0" (set 0) ∷ E-helpers ++ E-tests

E-δ : SpecΔ
E-δ = specΔ (mkQ ("M" ∷ [])) E-iface []

-- The implementation stub still omits tests and their private helpers.
_ : decls (stubOf E-δ) ≡ sig plain "specTest0" (set 0) ∷ []
_ = refl

-- Helpers keep their concrete bodies, named tests lose theirs, and generated
-- names skip both the existing specTest0 and previously generated names.
_ : decls (refuteStubOf E-δ) ≡ localizeTo (child E-δ)
    ((sig plain "specTest0" (set 0) ∷ E-helpers) ++
     (sig plain "namedTest" (E-eq (def (M· "helper")) E-one)
      ∷ sig plain "specTest1" (E-eq (def (M· "helper")) E-one)
      ∷ sig plain "specTest2" (E-eq E-zero E-zero) ∷ []))
_ = refl

-- A helper mentioned only by an anonymous type is still concrete.
_ : decls (refuteStubOf (specΔ (child E-δ)
      (E-helpers ++ (sig plain "_" (E-eq (def (M· "helper")) E-one) ∷ B-body "_" (var "refl") ∷ [])) []))
    ≡ localizeTo (child E-δ) (E-helpers ++ (sig plain "specTest0" (E-eq (def (M· "helper")) E-one) ∷ []))
_ = refl

-- Only signature dependencies pull helpers in; a test proof's references
-- alone must not turn that proof or its private helpers into concrete core.
_ : decls (refuteStubOf (specΔ (child E-δ)
      (B-function "leaf" E-one ++ B-function "namedTest" (def (M· "leaf"))) []))
    ≡ sig plain "leaf" (set 0) ∷ sig plain "namedTest" (set 0) ∷ []
_ = refl

-- Structural modules keep their own scope, without duplicate postulates for
-- their members at the outer level.
E-nested : List Decl
E-nested = module′ "Nested" (bind visible ("T" ∷ []) (set 0) ∷ [])
  (sig plain "id" (fun′ (vis (var "T")) (var "T"))
   ∷ fun plain "id" (clause (head (mkQ ("M" ∷ "Nested" ∷ "id" ∷ [])) (vis (varP "x") ∷ []))
       (rhs (var "x")) [] ∷ []) ∷ []) ∷ []

_ : decls (refuteStubOf (specΔ (child E-δ) E-nested [])) ≡ localizeTo (child E-δ) E-nested
_ = refl

E-liftSpec : List Decl
E-liftSpec = B-function "endpoint" E-zero ++
  (sig plain "square" (E-eq (def (A· "endpoint")) (def (M· "endpoint")))
   ∷ B-body "square" (var "refl") ∷ [])

_ : checkLift (code (mkQ ("A" ∷ [])) [] (sig plain "endpoint" (set 0) ∷ []))
      (code (mkQ ("M" ∷ [])) [] []) E-liftSpec
      (liftSpec (mkQ ("A" ∷ [])) (mkQ ("M" ∷ [])) []
        (endpointLift (A· "endpoint") (M· "endpoint") (M· "square") ∷ [])) ≡ []
_ = refl

-- Where-bound declarations carry an internal '_' scope segment; localizeTo
-- must never turn that segment into an illegal '_.helper' concrete projection,
-- while preserving a final '_' on anonymous declarations ('_ = refl').
_ : localizeTo (mkQ ("M" ∷ []))
      (sig plain "quoteBad" (def (qn ("M" ∷ "_" ∷ "apostrophe" ∷ []) "M._.apostrophe"))
       ∷ B-body "_" (var "refl") ∷ [])
    ≡ (sig plain "quoteBad" (def (qn ("M" ∷ "_" ∷ "apostrophe" ∷ []) "apostrophe"))
       ∷ B-body "_" (var "refl") ∷ [])
_ = refl
