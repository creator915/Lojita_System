{-# OPTIONS --guardedness #-}
module Test.NamespaceTest where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using () renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.IO using (IO)

open import Code
open import Code.Namespace
open import Code.Transport using (Plan; mkPlan; origin; _⇝_; keep; apply; validate)
open import Code.AgdaTool using (writeCodes)

short : Name → QName
short n = mkQ [ n ]

-- 作用域内的定义 f 和从另一个模块引用的 M.f 有各自的 shown。
member reference : Name → Name → QName
member m n = mkQ (m ∷ n ∷ [])
reference m n = qn (m ∷ n ∷ []) (m ++ˢ "." ++ˢ n)

r1 : List Name → NamespaceCtx
r1 path = nsCtx "T1_r1" ("Root" ∷ path)

parserCtx engineCtx engineCtx₂ : NamespaceCtx
parserCtx  = r1 [ "Parser" ]
engineCtx  = r1 [ "Engine" ]
engineCtx₂ = nsCtx "T1_r2" ("Root" ∷ "Engine" ∷ [])

rootKids helperSlot : List Name
rootKids = "Parser" ∷ "Engine" ∷ []
helperSlot = [ "Helper" ]

natModule equalityModule : QName
natModule = qn ("Agda" ∷ "Builtin" ∷ "Nat" ∷ []) "Agda.Builtin.Nat"
equalityModule = qn ("Agda" ∷ "Builtin" ∷ "Equality" ∷ []) "Agda.Builtin.Equality"

natImport equalityImport : Decl
natImport = import′ natModule true everything []
equalityImport = import′ equalityModule true everything []

nat unaryNat x sucX byRefl : Expr
nat = def (mkQ (full natModule ++ [ "Nat" ]))
unaryNat = fun′ (vis nat) nat
x = var "x"
sucX = app (con (mkQ (full natModule ++ ("Nat" ∷ "suc" ∷ [])))) (vis x)
byRefl = con (mkQ (full equalityModule ++ ("_≡_" ∷ "refl" ∷ [])))

atX : QName → Expr
atX f = app (def f) (vis x)

pointwise : Expr → Expr → Expr
pointwise l r = pi (bind visible [ "x" ] nat)
  (app (app (def (mkQ (full equalityModule ++ [ "_≡_" ]))) (vis l)) (vis r))

definition : Name → Name → Expr → Expr → List Decl
definition m f t e = sig plain f t ∷
  fun plain f [ clause (head (member m f) [ vis (varP "x") ]) (rhs e) [] ] ∷ []

dependency : Name → Name → Decl
dependency m f = import′ (short m) false everything [ sig plain f unaryNat ]

-- 两个 Helper 有完全相同的局部接口。一个返回 x，一个返回 suc x。
helper : Name → Expr → Code
helper parent e = qualifyCode (r1 (parent ∷ "Helper" ∷ [])) "Helper" [] []
  (code (short "Helper") [] (natImport ∷ definition "Helper" "step" unaryNat e))

branch : Name → Name → Code
branch m f = code (short m) [] (natImport ∷ dependency "Helper" "step"
             ∷ definition m f unaryNat (atX (reference "Helper" "step")))

parser engine localEngine : Code
parser = qualifyCode parserCtx "Parser" helperSlot [] (branch "Parser" "parse")
localEngine = branch "Engine" "run"
engine = qualifyCode engineCtx "Engine" helperSlot [] localEngine

root : Code
root = qualifyCode (r1 []) "Root" rootKids [] (code (short "Root") []
  (natImport ∷ equalityImport ∷ dependency "Parser" "parse" ∷ dependency "Engine" "run"
   ∷ definition "Root" "parse-law" (pointwise (atX (reference "Parser" "parse")) x) byRefl
  ++ definition "Root" "run-law" (pointwise (atX (reference "Engine" "run")) sucX) byRefl))

-- 搬运内联了原来由 Helper 实现的 step，并在新版留下逐点交换图。
upgrade : Plan
upgrade = mkPlan "inline step and prove agreement with the previous Engine" (just (short "Engine"))
  (equalityImport ∷ dependency "OldEngine" "run"
   ∷ definition "Engine" "run" unaryNat sucX
  ++ definition "Engine" "commutes"
       (pointwise (atX (reference "OldEngine" "run")) (atX (member "Engine" "run"))) byRefl)
  ((ext (reference "Helper" "step") ⇝ ⊥) ∷ keep (unit (member "Engine" "run"))
   ∷ (⊥ ⇝ ext (reference "OldEngine" "run")) ∷ (⊥ ⇝ unit (member "Engine" "commutes")) ∷ [])

engineBases : List (Name × QName)
engineBases = [ "OldEngine" , modName engine ]

qualifyEngine₂ : Code → Code
qualifyEngine₂ = qualifyCode engineCtx₂ "Engine" helperSlot engineBases

localNew engine₂ : Code
localNew = apply upgrade localEngine
engine₂ = qualifyEngine₂ localNew

modules : List Code
modules = root ∷ parser ∷ helper "Parser" x ∷ engine ∷ helper "Engine" sucX ∷ engine₂ ∷ []

_ : modName (helper "Parser" x) ≡ qn ("Gen" ∷ "T1_r1" ∷ "Root" ∷ "Parser" ∷ "Helper" ∷ []) "Helper"
_ = refl

_ : modName (helper "Engine" sucX) ≡ qn ("Gen" ∷ "T1_r1" ∷ "Root" ∷ "Engine" ∷ "Helper" ∷ []) "Helper"
_ = refl

_ : disjointPaths modules ≡ true
_ = refl

_ : disjointPaths (modules ++ [ code (qn (full (modName root)) "AnotherAlias") [] [] ]) ≡ false
_ = refl

oldAlias : QName
oldAlias = qn ("Gen" ∷ "T1_r1" ∷ "Root" ∷ "Engine" ∷ []) "OldEngine"

_ : map imod (imports engine₂) ≡ equalityModule ∷ oldAlias ∷ natModule ∷ []
_ = refl

-- 正文的两个 run 保留各自的拼写，AST 中的身份分别落在两个 epoch。
_ : iface engine₂ (unit (mkQ (full (modName engine₂) ++ [ "commutes" ])))
    ≡ ifaceSig (pointwise (atX (qn (full oldAlias ++ [ "run" ]) "OldEngine.run"))
                          (atX (mkQ (full (modName engine₂) ++ [ "run" ]))))
_ = refl

qualifiedPlan : Plan
qualifiedPlan = qualifyPlan engineCtx "Engine" helperSlot upgrade

_ : origin qualifiedPlan ≡ just (modName engine)
_ = refl

_ : validate localEngine upgrade localNew ≡ []
_ = refl

_ : apply qualifiedPlan engine ≡ qualifyCode engineCtx "Engine" helperSlot [] localNew
_ = refl

_ : validate engine qualifiedPlan (apply qualifiedPlan engine) ≡ []
_ = refl

-- 两条路径都将 OldEngine.run 解析到 r1，当前模块的 run 则属于 r2。
upgrade₂ : Plan
upgrade₂ = qualifyPlanWithBases engineCtx₂ "Engine" helperSlot engineBases upgrade

_ : apply upgrade₂ (qualifyEngine₂ localEngine) ≡ qualifyEngine₂ (apply upgrade localEngine)
_ = refl

_ : validate (qualifyEngine₂ localEngine) upgrade₂ (apply upgrade₂ (qualifyEngine₂ localEngine)) ≡ []
_ = refl

-- 检验 new 中的子包 import 和 moves 两端的 ext、unit 以及 flags。
_ : qualifyPlan parserCtx "Parser" helperSlot
      (mkPlan "copy interface" nothing [ dependency "Helper" "step" ]
        ((unit (member "Parser" "parse") ⇝ ext (reference "Helper" "step")) ∷ keep flags ∷ []))
    ≡ mkPlan "copy interface" nothing
        [ import′ (modName (helper "Parser" x)) false everything [ sig plain "step" unaryNat ] ]
        ((unit (mkQ (full (modName parser) ++ [ "parse" ]))
           ⇝ ext (qn (full (modName (helper "Parser" x)) ++ [ "step" ]) "Helper.step"))
          ∷ keep flags ∷ [])
_ = refl

_ : allᵇ validSegment ("T1_r1" ∷ "_Node2" ∷ "Parser" ∷ []) ≡ true
_ = refl

_ : anyᵇ validSegment ("" ∷ "1st" ∷ "Foo.Bar" ∷ "A/B" ∷ "a-b" ∷ "a b"
    ∷ "module" ∷ "where" ∷ "import" ∷ "open" ∷ "postulate" ∷ "data" ∷ "record"
    ∷ "code" ∷ "memory" ∷ "spec" ∷ "ai" ∷ "dump" ∷ "agda" ∷ "child" ∷ []) ≡ false
_ = refl

_ : childCtx (r1 []) "Parser" ≡ just parserCtx
_ = refl
_ : childCtx parserCtx "Foo.Bar" ≡ nothing
_ = refl
_ : childCtx parserCtx "code" ≡ nothing
_ = refl

onlyImports : List QName → Code
onlyImports qs = code (short "Parser") [] (map (λ q → import′ q false everything []) qs)

_ : checkNodeImports parserCtx ("Helper" ∷ "code" ∷ "Helper" ∷ "Foo.Bar" ∷ []) [] (onlyImports [])
    ≡ invalidSlotSegment "code" ∷ duplicateChildSlot "Helper" ∷ invalidSlotSegment "Foo.Bar" ∷ []
_ = refl

harness ownership sibling foreignHelper : QName
harness = qn ("Code" ∷ "Harness" ∷ []) "Helper"
ownership = short "Ownership"
sibling = short "Engine"
foreignHelper = modName (helper "Engine" sucX)

_ : checkNodeImports parserCtx helperSlot (harness ∷ ownership ∷ [])
      (onlyImports (harness ∷ ownership ∷ sibling ∷ modName engine ∷ foreignHelper ∷ []))
    ≡ metaNamespaceCollision harness ∷ metaNamespaceCollision ownership
    ∷ forbiddenSiblingOrExternalImport sibling ∷ forbiddenSiblingOrExternalImport (modName engine)
    ∷ forbiddenSiblingOrExternalImport foreignHelper ∷ []
_ = refl

_ : checkNodeImports parserCtx helperSlot [] (branch "Parser" "parse") ≡ []
_ = refl
_ : checkNodeImports (r1 []) rootKids [] root ≡ []
_ = refl
_ : checkNodeImports (r1 []) rootKids [] (onlyImports [ foreignHelper ])
    ≡ [ forbiddenSiblingOrExternalImport foreignHelper ]
_ = refl
_ : checkNodeImports parserCtx helperSlot [] parser ≡ []
_ = refl
_ : checkNodeImports engineCtx₂ [] [ modName engine ] engine₂ ≡ []
_ = refl
_ : checkNodeImports engineCtx₂ [] [] engine₂ ≡ [ forbiddenSiblingOrExternalImport oldAlias ]
_ = refl
_ : checkNodeImports engineCtx₂ [] [ modName engine ] (onlyImports [ foreignHelper ])
    ≡ [ forbiddenSiblingOrExternalImport foreignHelper ]
_ = refl

_ : allᵇ isMetaModule (map short ("Ownership" ∷ "OwnershipIO" ∷ "Code" ∷ "Store" ∷ "Meta"
    ∷ "Test" ∷ "Verification" ∷ "SessionEnv" ∷ "Main" ∷ [])) ≡ true
_ = refl
_ : isMetaModule (qn ("Main" ∷ "Part" ∷ []) "Main") ≡ false
_ = refl

entryOnly : List QName
entryOnly = mkQ ("IO" ∷ "Primitive" ∷ []) ∷ mkQ ("Agda" ∷ "Builtin" ∷ "IO" ∷ [])
          ∷ map short ("Axiom" ∷ "Codata" ∷ "Effect" ∷ [])

_ : allᵇ isPreTaskContext entryOnly ≡ true
_ = refl
_ : anyᵇ isClosedWorldContext (harness ∷ entryOnly) ≡ false
_ = refl
_ : checkTaskImports parserCtx [] entryOnly (onlyImports [ mkQ ("Agda" ∷ "Builtin" ∷ "IO" ∷ []) ])
    ≡ [ forbiddenSiblingOrExternalImport (mkQ ("Agda" ∷ "Builtin" ∷ "IO" ∷ [])) ]
_ = refl
_ : allᵇ isClosedWorldContext (natModule ∷ mkQ ("Context" ∷ "Blueprint" ∷ [])
    ∷ map short ("Data" ∷ "Relation" ∷ "Function" ∷ "Level" ∷ "Algebra" ∷ "Category" ∷ "Induction" ∷ []))
    ≡ true
_ = refl

-- where 的局部作用域可以有 import/open。assumes 也要重写，门禁按当前模块实际导入判定。
scoped : QName → QName → QName → Code
scoped self kid base = code self [ bind visible [ "param" ] (def base) ]
  [ module′ "Nested" []
      [ sig plain "f" (lamCase [ clause (head self [ vis (conP kid []) ]) (rhs (def base))
          (import′ kid false everything [ open′ base everything ] ∷ open′ kid everything
           ∷ import′ base false everything [] ∷ []) ]) ] ]

_ : qualifyCode parserCtx "Parser" helperSlot [ "OldEngine" , modName engine ]
      (scoped (short "Parser") (short "Helper") (short "OldEngine"))
    ≡ scoped (modName parser) (modName (helper "Parser" x)) oldAlias
_ = refl

_ : checkNodeImports parserCtx helperSlot []
      (scoped (short "Parser") (short "Helper") harness) ≡ [ metaNamespaceCollision harness ]
_ = refl

-- 脚本在全新的同一目录运行此入口，然后让 agda 检查根和新版 Engine。
main : IO ⊤
main = writeCodes "." modules
