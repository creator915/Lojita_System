------------------------------------------------------------------------
-- Code/Transport.agda —— 搬运：两个 Code 范畴之间的 profunctor
--
-- 一个 Code 值是一个范畴（见 Code.agda §3）：对象是单元、外部名字、flags、⊥；箭头 u → v 是"u 用到 v"。
-- 一次搬运把旧 Code C 变成新 Code D。它不是一个函子（一个单元可以拆成几个、几个可以并成一个、
-- 可以凭空出现、可以消失），它是一个 profunctor  P : C ⇸ D ：一堆 proarrow（异态射）c ⇝ d，
-- 读作"c 的内容流进了 d"。记忆沿着 proarrow 继承。
--
--     旧 Code (C)                              新 Code (D)
--
--     c  ─────────────── p ───────────────⇝  d          生成子：Plan 里的一条，LLM 写的
--     ▲                                      ▲
--     │ c′ 用到 c                             │ d′ 用到 d
--     c′ ────────────── p′ ──────────────⇝  d′         交换方块：c′ 也得有去处
--
-- 交换方块就是搬运的唯一法则："被依赖的动了，依赖它的也要跟着动"：
--   * p 动了 c 的接口（类型签名 / 构造子表 / 字段表；或者 d = ⊥，接口全没了），
--     那么 c 的每个直接依赖者 c′ 都必须是某条 proarrow 的源——义务。
--   * 恒等 proarrow  c′ ⇝ c′  也算完成义务：意思是"看过了，不用改"（agda 最后会复查）。
--   * 若 p′ : c′ ⇝ d′ 没动 c′ 的接口，链到此为止；动了，c′ 的依赖者又有义务。这是终止条件。
--   * ⊥ 没有接口：到 ⊥ 去 = 丢弃，接口全丢，依赖者必须搬；从 ⊥ 来 = 新代码，什么也没破坏。
--
-- 还没完成义务的对象叫 frontier。frontier 为空、引用都解析得到、新旧两边对得上，
-- 这堆 proarrow 才真的是一个 profunctor（validate 为空），apply 才可以执行。
-- 执行完的新 Code 还要过 agda（IO 层做）——profunctor 管的是"谁该看"，类型检查管的是"对不对"。
--
-- 四种形状都是普通的 proarrow：
--   一到多  c ⇝ d₁ , c ⇝ d₂     拆       多到一  c₁ ⇝ d , c₂ ⇝ d     并
--   零到多  ⊥ ⇝ d               写新的   多到零  c ⇝ ⊥               丢弃
--
-- 文件边界：源或靶是  ext ⟨k.x⟩（孩子 k 暴露给我的名字）的 proarrow，不是本文件能做完的事：
-- 它们合起来是对 k 的新规约 SpecΔ，要沿所有权树发给 k 的 agent（Code/Harness.agda）。
------------------------------------------------------------------------
module Code.Transport where

open import Data.Nat using (ℕ; zero; suc; _+_; _≡ᵇ_)
import Data.Nat.Show as ℕshow
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; map; concatMap; length; reverse; foldr; [_])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _++ˢ_)

open import Code

------------------------------------------------------------------------
-- §1  proarrow 与 Plan
------------------------------------------------------------------------

-- 一条异态射：旧 Code 的对象 ⇝ 新 Code 的对象
record Proarrow : Set where
  constructor _⇝_
  field
    src : Obj
    tgt : Obj
open Proarrow public
infix 6 _⇝_

-- 一个搬运计划：LLM（或者工具）交上来的东西。
--   why    ：为什么搬。会写进所有靶对象的记忆里
--   new    ：新代码。靶是 unit 的那些对象的声明都在这里；也可以放新的 import′（孩子的新接口）
--            和新的 pragma（flags 变了）
--   moves  ：生成子
-- 没出现在任何 proarrow 里的旧单元 = 恒等搬运（原样保留）。
record Plan : Set where
  constructor mkPlan
  field
    why    : String
    origin : Maybe QName       -- new 里的声明是在哪个模块里 scope check 的（LLM 写的小模块）；
                               -- apply 时把那个前缀换成目标模块的。nothing = 已经是目标模块的名字
    new    : List Decl
    moves  : List Proarrow
open Plan public

plan : String → List Decl → List Proarrow → Plan
plan why ds ms = mkPlan why nothing ds ms

-- 换模块前缀：NewTwice.twice → C.twice。别的名字（外部的、语境库的）不动
requalify : QName → QName → QName → QName
requalify from to q = if isPrefix (full from) (full q) then qn (full to ++ dropN (length (full from)) (full q)) (shown q) else q
  where
    dropN : ℕ → List Name → List Name
    dropN zero    xs       = xs
    dropN (suc n) []       = []
    dropN (suc n) (_ ∷ xs) = dropN n xs

srcs tgts : Plan → List Obj
srcs p = map src (moves p)
tgts p = map tgt (moves p)

isSrc isTgt : Plan → Obj → Bool
isSrc p o = elemᵇ _==ᴼ_ o (srcs p)
isTgt p o = elemᵇ _==ᴼ_ o (tgts p)

targetsOf : Plan → Obj → List Obj
targetsOf p o = map tgt (filterᵇ (λ a → src a ==ᴼ o) (moves p))

sourcesOf : Plan → Obj → List Obj
sourcesOf p o = map src (filterᵇ (λ a → tgt a ==ᴼ o) (moves p))

-- 恒等 proarrow：c ⇝ c
keep : Obj → Proarrow
keep o = o ⇝ o

------------------------------------------------------------------------
-- §2  重命名
-- 旧名字 c 在新 Code 里叫什么？
--   c 的靶里有同名的        → 还叫 c（拆出 helper 的那种：c ⇝ c , c ⇝ helper）
--   c 恰好一个靶 d（≠ ⊥）    → 叫 d（改名；或几个并成 d）
--   别的情况（拆成几个、丢弃）→ 没有自动的答案：依赖者必须自己搬（义务会抓住它们）
------------------------------------------------------------------------

renameMap : Plan → QName → QName
renameMap p q with targetsOf p (unit q)
... | [] = q
... | ts = if anyᵇ sameName ts then q else single ts
  where
    sameName : Obj → Bool
    sameName (unit r) = r ==ᴺ q
    sameName _        = false
    single : List Obj → QName
    single (unit r ∷ []) = r
    single _             = q

-- ext 的名字也可能被孩子改掉：ext A.ℕ ⇝ ext A.Nat；保留同名 ext 时不动 shown（保住 A.x 限定前缀）
renameExt : Plan → QName → QName
renameExt p q with targetsOf p (ext q)
... | [] = q
... | ts = if anyᵇ sameExt ts then q else singleExt ts
  where
    sameExt : Obj → Bool
    sameExt (ext r) = r ==ᴺ q
    sameExt _       = false
    singleExt : List Obj → QName
    singleExt (ext r ∷ []) = r
    singleExt _            = q

ρ : Plan → QName → QName
ρ p q = renameExt p (renameMap p q)

------------------------------------------------------------------------
-- §3  接口变了没有
------------------------------------------------------------------------

-- 接口里的名字也要过一遍重命名再比（c 的类型提到 e，e 改名成 e′，不算 c 变了）
renameIface : (QName → QName) → Iface → Iface
renameIface f (ifaceSig e)        = ifaceSig (renameExpr f e)
renameIface f (ifaceData bs s cs) = ifaceData (renameBinds f bs) (renameExpr f s) (renameFields f cs)
renameIface f (ifaceRec bs s d fs) = ifaceRec (renameBinds f bs) (renameExpr f s) d (renameFields f fs)
renameIface f i                   = i

-- 一条 proarrow 是否保住了源的接口（在新 Code 里看它的靶）
preserves : Code → Code → Plan → Proarrow → Bool
preserves old new p (⊥ ⇝ _) = true                                          -- 从 ⊥ 来：没有旧接口可破坏
preserves old new p (_ ⇝ ⊥) = false                                         -- 到 ⊥ 去：接口全丢
preserves old new p (s ⇝ t) with iface new t
... | ifaceNone = isCtx s                                                   -- 语境库的名字：接口不在我手里，当作没变
  where
    isCtx : Obj → Bool
    isCtx (ext q) with iface old (ext q)
    ... | ifaceNone = true
    ... | _         = false
    isCtx _ = false
... | it = eqIface (renameIface (ρ p) (iface old s)) it

-- 源的接口被动了的那些对象
changed : Code → Code → Plan → List Obj
changed old new p = nubᵇ _==ᴼ_ (map src (filterᵇ (λ a → not (preserves old new p a)) (moves p)))

------------------------------------------------------------------------
-- §4  义务与 frontier（交换方块）
--
--   obligations：必须是某条 proarrow 之源的对象。
--     从 changed 出发：它们的直接依赖者有义务；一个有义务的对象如果自己也是 changed 的源，
--     它的依赖者又有义务……沿旧 Code 的"被谁用到"往上走，到接口没变的地方停。
--   frontier：有义务却还没有 proarrow 的。LLM 下一轮要处理的就是它们。
------------------------------------------------------------------------

obligations : Code → Code → Plan → List Obj
obligations old new p = go (suc (length as)) (changed old new p) []
  where
    as : List (Obj × Obj)
    as = arrows old
    -- 一步：这些对象的直接依赖者
    step : List Obj → List Obj
    step os = nubᵇ _==ᴼ_ (concatMap (dependentsIn as) os)
    -- 它们中接口也被动了的，继续往上传
    stillChanged : List Obj → List Obj
    stillChanged = filterᵇ (λ o → elemᵇ _==ᴼ_ o (changed old new p))
    go : ℕ → List Obj → List Obj → List Obj
    go zero    _     acc = acc
    go (suc n) front acc with filterᵇ (λ o → not (elemᵇ _==ᴼ_ o acc)) (step front)
    ... | []  = acc
    ... | nxt = go n (stillChanged nxt) (acc ++ nxt)

frontier : Code → Code → Plan → List Obj
frontier old new p = filterᵇ (λ o → not (isSrc p o)) (obligations old new p)

------------------------------------------------------------------------
-- §5  apply：执行一个计划
--   1. 被当成源的单元：声明删掉（消费旧的）
--   2. new 里的声明：放进去（生产新的）。放在第一个被删的单元原来的位置；没有就放最后
--   3. new 里的 import′ 替换同名的旧 import′；new 里的 pragma 替换旧的 pragma
--   4. 保留下来的单元里的引用，按 ρ 重命名
-- 顺序不用操心：Render 按依赖排
------------------------------------------------------------------------

private
  isPragma : Decl → Bool
  isPragma (pragma _) = true
  isPragma _          = false

  importName : Decl → Maybe QName
  importName (import′ m _ _ _) = just m
  importName _                 = nothing

  -- new 里出现的 import 模块名
  newImports : List Decl → List QName
  newImports []       = []
  newImports (d ∷ ds) with importName d
  ... | just m  = m ∷ newImports ds
  ... | nothing = newImports ds

  -- new 里有没有定义这个名字
  definesName : List Decl → Name → Bool
  definesName ds x = anyᵇ (λ d → eqMaybe _==ˢ_ (declName d) (just x)) ds

  -- 这条声明属于被消费的单元吗（按名字；where 里的归外面那条）。
  -- 恒等 proarrow（keep c）而 new 里又没有 c 的新声明：不消费，原样保留——"看过了，不用改"
  consumed : List Name → Plan → Decl → Bool
  consumed path p d with declName d
  ... | nothing = false
  ... | just x  = let o = unit (mkQ (path ++ (x ∷ []))) in
                  definesName (new p) x ∨ (isSrc p o ∧ not (isTgt p o))

-- 把 new 里的声明分成三类：pragma、import′、其他
splitNew : List Decl → List Decl × List Decl × List Decl
splitNew [] = [] , [] , []
splitNew (d ∷ ds) with splitNew ds
... | ps , is , rs with d
...   | pragma s          = (pragma s ∷ ps) , is , rs
...   | import′ m o dir a = ps , (import′ m o dir a ∷ is) , rs
...   | _                 = ps , is , (d ∷ rs)

nullᵇ : ∀ {A : Set} → List A → Bool
nullᵇ [] = true
nullᵇ _  = false

-- 顶层声明列表上执行（子模块里的单元：这版只支持顶层单元的搬运；子模块整个算一个单元）
applyDecls : List Name → Plan → List Decl → List Decl
applyDecls path p ds = freshPragmas ++ freshImports ++ go ds false false
  where
    parts      = splitNew (new p)
    newPragmas = proj₁ parts
    newImps    = proj₁ (proj₂ parts)
    newRest    = proj₂ (proj₂ parts)

    replacedImport : QName → Bool
    replacedImport m = elemᵇ _==ᴺ_ m (newImports (new p))

    pickNew : QName → List Decl
    pickNew m = filterᵇ (λ e → eqMaybe _==ᴺ_ (importName e) (just m)) newImps

    freshImports = filterᵇ (λ d → not (anyᵇ (λ old → eqMaybe _==ᴺ_ (importName d) (importName old)) ds)) newImps
    freshPragmas = if anyᵇ isPragma ds then [] else newPragmas

    removedImport : QName → List Decl → Bool
    removedImport m a = not (nullᵇ a) ∧ allᵇ (λ u → elemᵇ _==ᴼ_ ⊥ (targetsOf p (ext (uname u)))) (unitsIn (full m) a)

    -- ins：新声明是否已经放进去了；prag：新 pragma 是否已经放进去了（整体替换：旧 pragma 都不要了）
    go : List Decl → Bool → Bool → List Decl
    go [] false _ = newRest
    go [] true  _ = []
    go (pragma s ∷ ds) ins prag =
      if nullᵇ newPragmas then pragma s ∷ go ds ins prag
      else (if prag then go ds ins prag else newPragmas ++ go ds ins true)
    go (import′ m o dir a ∷ ds) ins prag =
      if replacedImport m then pickNew m ++ go ds ins prag else (if removedImport m a then go ds ins prag else import′ m o dir a ∷ go ds ins prag)
    go (d ∷ ds) ins prag =
      if consumed path p d
      then (if ins then go ds ins prag else newRest ++ go ds true prag)
      else d ∷ go ds ins prag

-- 先把 new 里的名字换成目标模块的前缀
adopt : Code → Plan → Plan
adopt c p with origin p
... | nothing   = p
... | just from = record p { origin = nothing ; new = renameDecls (requalify from (modName c)) (new p) }

apply : Plan → Code → Code
apply p₀ c = let p = adopt c p₀ in
  renameCode (ρ p) (code (modName c) (params c) (applyDecls (full (modName c)) p (decls c)))
  -- 注意：renameCode 也会过一遍 new 里的声明。new 是按新名字写的，ρ 对新名字是恒等，所以没事；
  -- 唯一的例外是 new 里又提到了一个被改名的旧名字——那本来就是错的，validate 会抓。

------------------------------------------------------------------------
-- §6  validate：这堆 proarrow 是不是真的构成 old ⇸ new 的 profunctor
-- 全部通过才算一个合法的搬运。每一条都是一个可以直接念出来的问题。
------------------------------------------------------------------------

data Problem : Set where
  unknownSrc  : Obj → Problem            -- 源不在旧 Code 里
  unknownTgt  : Obj → Problem            -- 靶不在新 Code 里
  lostUnit    : Obj → Problem            -- 旧单元消失了，却没有 proarrow 说它去了哪
  orphanUnit  : Obj → Problem            -- 新单元出现了，却没有 proarrow 说它从哪来（也不是 ⊥ 来的）
  unsettled   : Obj → Problem            -- 义务没完成：它依赖的东西接口变了，它却没人管
  dangling    : Obj → QName → Problem    -- 新代码里引用了一个已经不存在的名字

-- 新 Code 里的某个单元是不是旧 Code 里原样保留下来的
private
  keptAsIn : List Unit → List Unit → Plan → QName → Bool
  keptAsIn oldUnits newUnits p q with lookupUnit oldUnits q | lookupUnit newUnits q
  ... | just u | just v = eqDecls (renameDecls (ρ p) (udecls u)) (udecls v)
                       ∨ (isPostulate (udecls u) ∧ eqIface (ifaceOfDecls (udecls u)) (ifaceOfDecls (udecls v)))
  ... | _      | _      = false

keptAs : Code → Code → Plan → QName → Bool
keptAs old new p = keptAsIn (units old) (units new) p

validate : Code → Plan → Code → List Problem
validate old p new with units old | units new | extUnits old | extUnits new
... | oldUnits | newUnits | oldExts | newExts
  with objectsIn (modName old) oldUnits oldExts | objectsIn (modName new) newUnits newExts
... | oldObjs | newObjs =
     concatMap chkSrc (moves p)
  ++ concatMap chkTgt (moves p)
  ++ concatMap chkLost oldUnits
  ++ concatMap chkOrphan newUnits
  ++ map unsettled (frontier old new p)
  ++ concatMap chkDangling newUnits
  where
    inOld inNew : Obj → Bool
    inOld o = elemᵇ _==ᴼ_ o oldObjs
    inNew o = elemᵇ _==ᴼ_ o newObjs

    chkSrc : Proarrow → List Problem
    chkSrc (s ⇝ t) = if inOld s then [] else unknownSrc s ∷ []
    chkTgt : Proarrow → List Problem
    chkTgt (s ⇝ t) = if inNew t then [] else unknownTgt t ∷ []

    -- 旧单元：要么原样在新里，要么是某条 proarrow 的源
    chkLost : Unit → List Problem
    chkLost u = let o = unit (uname u) in
      if isSrc p o ∨ keptAsIn oldUnits newUnits p (uname u) then [] else lostUnit o ∷ []

    -- 新单元：要么是原样保留的旧单元，要么是某条 proarrow 的靶
    chkOrphan : Unit → List Problem
    chkOrphan v = let o = unit (uname v) in
      if isTgt p o ∨ keptAsIn oldUnits newUnits p (uname v) then [] else orphanUnit o ∷ []

    -- 新单元引用的名字必须解析得到（解析不到 = 指向已经不存在的东西）
    chkDangling : Unit → List Problem
    chkDangling v = concatMap bad (refsDecls (udecls v))
      where
        bad : QName → List Problem
        bad q with resolveIn (modName new) newUnits newExts q
        ... | just _  = []
        ... | nothing = if isPrefix (full (modName new)) (full q) ∧ not (isLocalOrWhere q) then dangling (unit (uname v)) q ∷ [] else []
          where
            -- 本模块路径下、但不是任何单元的名字：where 里的局部定义（C._.helper）不算悬空
            isLocalOrWhere : QName → Bool
            isLocalOrWhere r = anyᵇ (λ seg → seg ==ˢ "_") (full r)

valid : Code → Plan → Code → Bool
valid old p new with validate old p new
... | [] = true
... | _  = false

------------------------------------------------------------------------
-- §7  边界：发给孩子的规约变更
--
-- 孩子 k 在我眼里是一个 postulate 块（import′ k 的 assumes）。它暴露出来的名字是 ext ⟨k.x⟩。
-- 这次搬运里源或靶落在 ⟨k.·⟩ 上的 proarrow，就是 k 的接口的搬运——一个"接口范畴上的 profunctor"，
-- k 的 agent 要做的是把它延拓成 k 的整个 Code 上的 profunctor：
--
--     Iface(k)  ───── P|ₖ ─────⇝  Iface(k)′        我决定（这就是新的 k.test）
--        │                           │
--        │ ⊆（暴露）                  │ ⊆
--     Code(k)   ───── Pₖ ──────⇝  Code(k)′        k 的 agent 补出来的，直到 agda 接受
------------------------------------------------------------------------

record SpecΔ : Set where
  constructor specΔ
  field
    child    : QName             -- 孩子的模块名
    newIface : List Decl         -- 它的新接口（新的 assumes；没变就是旧的）
    δarrows  : List Proarrow     -- 接口上的 proarrow（都是 ext ⇝ ext / ext ⇝ ⊥ / ⊥ ⇝ ext）
open SpecΔ public

underModule : QName → Obj → Bool
underModule m (ext q) = isPrefix (full m) (full q)
underModule m _       = false

-- 这个孩子被动了吗
touches : Plan → QName → Bool
touches p m = anyᵇ (λ a → underModule m (src a) ∨ underModule m (tgt a)) (moves p)

-- 被动了的孩子们（按新 Code 的 import 列表；语境库没有 assumes，不在其列）
affectedChildren : Code → Plan → List QName
affectedChildren new p = filterᵇ (touches p) (map imod (filterᵇ hasIface (imports new)))
  where
    hasIface : Import → Bool
    hasIface i with assumes i
    ... | [] = false
    ... | _  = true

restrict : Code → Plan → QName → SpecΔ
restrict new p m = specΔ m (ifaceOf (imports new)) (filterᵇ (λ a → underModule m (src a) ∨ underModule m (tgt a)) (moves p))
  where
    ifaceOf : List Import → List Decl
    ifaceOf []       = []
    ifaceOf (i ∷ is) = if imod i ==ᴺ m then assumes i else ifaceOf is

-- shown 是作用域的痕迹：父亲的 assumes 里写的是 A.ℕ，搬进模块 A 自己的文件里要写成 ℕ。
-- localizeTo m：m 名下的名字，shown 改成去掉 m 前缀的那一段（A.ℕ.suc 在 A 里是 ℕ.suc）。别的名字不动
localizeTo : QName → List Decl → List Decl
localizeTo m = renameDecls loc
  where
    dropN : ℕ → List Name → List Name
    dropN zero    xs       = xs
    dropN (suc n) []       = []
    dropN (suc n) (_ ∷ xs) = dropN n xs
    -- Non-final '_' segments represent Agda where-scopes, whereas a final '_'
    -- segment is an anonymous declaration's own name ('_ = refl').
    afterWhereScope : List Name → List Name
    afterWhereScope [] = []
    afterWhereScope (x ∷ []) = x ∷ []
    afterWhereScope ("_" ∷ y ∷ ys) = afterWhereScope (y ∷ ys)
    afterWhereScope (x ∷ y ∷ ys) with afterWhereScope (y ∷ ys)
    ... | rest = if eqList _==ˢ_ rest (y ∷ ys) then x ∷ rest else rest
    loc : QName → QName
    loc q = if isPrefix (full m) (full q)
            then qn (full q) (Data.String.intersperse "." (afterWhereScope (dropN (length (full m)) (full q))))
            else q
      where import Data.String

hasFun : List Decl → Bool
hasFun = anyᵇ body
  where
    body : Decl → Bool
    body (fun _ _ _) = true
    body _ = false

anonymousUnit : Unit → Bool
anonymousUnit u = anyᵇ anonymous (udecls u)
  where
    anonymous : Decl → Bool
    anonymous (sig _ n _) = n ==ˢ "_"
    anonymous (fun _ n _) = n ==ˢ "_"
    anonymous _ = false

specProblem : List Decl → Maybe String
specProblem ds = if anyᵇ (λ u → anonymousUnit u ∧ not (hasFun (udecls u))) (unitsIn [] ds)
  then just "spec: anonymous '_' declarations must include a definition body (e.g. '_ = refl'); give postulated obligations an explicit name"
  else nothing

specImplOK : List String → Code → List ImplProblem
specImplOK allowed c = filterᵇ nonPostulate (closedImplOK allowed c)
  where
    nonPostulate : ImplProblem → Bool
    nonPostulate (unimplementedPostulate _) = false
    nonPostulate _ = true

subspecImportProblem : QName → List QName → List Code → Code → Maybe String
subspecImportProblem parentMod siblingMods allowedBaseMods subCode
  with anyᵇ (λ i → elemᵇ _==ᴺ_ (imod i) (parentMod ∷ siblingMods)) (imports subCode)
... | true = just "subspec: sibling or parent imports are forbidden; copy shared port types/helpers directly into each child's subspec"
... | false with duplicates siblingMods
  where
    duplicates : List QName → Bool
    duplicates [] = false
    duplicates (m ∷ ms) = elemᵇ _==ᴺ_ m ms ∨ duplicates ms
... | true = just "subspec: duplicate child module name"
... | false with elemᵇ _==ᴺ_ parentMod (modName subCode ∷ siblingMods)
... | true = just "subspec: child module name collides with its parent"
... | false with anyᵇ (λ b → elemᵇ _==ᴺ_ (modName b) (modName subCode ∷ siblingMods)) allowedBaseMods
... | true = just "subspec: child module name shadows a sealed ancestor module"
... | false = nothing

-- Obligations and structural declarations seed the core. Their transitive
-- dependencies include concrete helpers, even across helper/obligation cycles.
-- Anonymous units are always tests; other functions start outside the core.
private
  -- Computed tables must be arguments/with-bound variables: Agda substitutes
  -- lets, and MAlonzo lifts where tables to functions that recompute at -O0.
  localCoreRef : QName → List Unit → List Unit → QName → List QName
  localCoreRef targetMod us es q with resolveIn targetMod us es q
  ... | just (unit n) = n ∷ []
  ... | _ = []

  -- Only the new frontier is expanded. A unit's adjacency list is visited
  -- once, including in cycles; no accumulated dependency closure is rebuilt.
  closeCore : ℕ → List (QName × List QName) → List QName → List QName → List QName
  closeCore zero edges seen frontier = seen
  closeCore (suc fuel) edges seen [] = seen
  closeCore (suc fuel) edges seen frontier@(_ ∷ _)
    with filterᵇ (λ q → not (elemᵇ _==ᴺ_ q seen))
      (nubᵇ _==ᴺ_ (concatMap proj₂ (filterᵇ (λ e → elemᵇ _==ᴺ_ (proj₁ e) frontier) edges)))
  ... | [] = seen
  ... | nextFrontier = closeCore fuel edges (seen ++ nextFrontier) nextFrontier

  coreNamesIn : QName → List Unit → List Unit → List QName
  coreNamesIn targetMod us es with filterᵇ (λ u → not (anonymousUnit u)) us
  ... | named
    with map (λ u → uname u , concatMap (localCoreRef targetMod us es) (refsDecls (udecls u))) named
       | map uname (filterᵇ (λ u → not (hasFun (udecls u))) named)
  ... | edges | seedCore with closeCore (suc (length named)) edges seedCore seedCore
  -- Keep the original declaration order, independently of discovery order.
  ... | seen = map uname (filterᵇ (λ u → elemᵇ _==ᴺ_ (uname u) seen) named)

coreNames : QName → List Decl → List QName
coreNames targetMod rawIface with localizeTo targetMod rawIface
... | loc = coreNamesIn targetMod (unitsIn (full targetMod) loc) (extUnits (code targetMod [] loc))

-- Keep core bodies as well as their signatures: laws can mention helpers,
-- and those helpers can in turn call postulated operations in the stub.
stubDecls : QName → List Decl → List Decl
stubDecls targetMod rawIface with localizeTo targetMod rawIface
... | loc with coreNamesIn targetMod (unitsIn (full targetMod) loc) (extUnits (code targetMod [] loc))
... | core = filterᵇ keepDecl loc
  where
    coreName : Name → Bool
    coreName n = elemᵇ _==ᴺ_ (mkQ (full targetMod ++ (n ∷ []))) core
    keepDecl : Decl → Bool
    keepDecl (fixity _ _ n) = coreName n
    keepDecl d with declName d
    ... | just n = coreName n
    ... | nothing = true

stubOf : SpecΔ → Code
stubOf δ = code (child δ) [] (stubDecls (child δ) (newIface δ))

private
  -- In addition to the ordinary core, retain every dependency of a signature:
  -- test propositions may mention concrete helpers absent from stubOf.
  refuteCoreNamesIn : QName → List Decl → List Unit → List Unit → List QName
  refuteCoreNamesIn targetMod loc us es with filterᵇ (λ u → not (anonymousUnit u)) us
  ... | named
    with map (λ u → uname u , concatMap (localCoreRef targetMod us es) (refsDecls (udecls u))) named
       | nubᵇ _==ᴺ_ (map uname (filterᵇ (λ u → not (hasFun (udecls u))) named)
           ++ concatMap (localCoreRef targetMod us es) (concatMap sigRefs loc))
    where
      sigRefs : Decl → List QName
      sigRefs (sig _ _ t) = refsExpr t
      sigRefs _ = []
  ... | edges | seeds = closeCore (suc (length named)) edges seeds seeds

  freshSpecTest : ℕ → ℕ → List Name → Name
  freshSpecTest zero idx used = "specTest" ++ˢ ℕshow.show idx
  freshSpecTest (suc fuel) idx used with "specTest" ++ˢ ℕshow.show idx
  ... | n = if elemᵇ _==ˢ_ n used then freshSpecTest fuel (suc idx) used else n

  testPostulates : List QName → List Name → ℕ → List Unit → List Decl
  testPostulates core used idx [] = []
  testPostulates core used idx (u ∷ us) with anonymousUnit u
  ... | true with freshSpecTest (suc (length used)) idx used
  ... | n = (if hasFun (udecls u) then concatMap (anonymousSig n) (udecls u) else [])
          ++ testPostulates core (n ∷ used) (suc idx) us
    where
      anonymousSig : Name → Decl → List Decl
      anonymousSig n (sig _ "_" t) = sig plain n t ∷ []
      anonymousSig n _ = []
  testPostulates core used idx (u ∷ us) | false =
    (if elemᵇ _==ᴺ_ (uname u) core then [] else concatMap namedSig (udecls u))
    ++ testPostulates core used idx us
    where
      namedSig : Decl → List Decl
      namedSig (sig _ n t) = sig plain n t ∷ []
      namedSig _ = []

-- Refutations assume test propositions instead of their potentially impossible
-- proof bodies. Keep all shared tables with-bound for MAlonzo at -O0.
refuteStubOf : SpecΔ → Code
refuteStubOf δ with localizeTo (child δ) (newIface δ)
... | loc with unitsIn (full (child δ)) loc | extUnits (code (child δ) [] loc)
... | us | es with refuteCoreNamesIn (child δ) loc us es | map (λ u → shown (uname u)) us
... | core | used = code (child δ) []
  (filterᵇ keepDecl loc ++ testPostulates core used 0 (filterᵇ topLevel us))
  where
    -- Nested declarations remain inside their retained structural module;
    -- lifting their signatures here would lose module parameters and scope.
    topLevel : Unit → Bool
    topLevel u = uname u ==ᴺ mkQ (full (child δ) ++ (shown (uname u) ∷ []))
    keepDecl : Decl → Bool
    keepDecl (fixity _ _ _) = true
    keepDecl d with declName d
    ... | just n = elemᵇ _==ᴺ_ (mkQ (full (child δ) ++ (n ∷ []))) core
    ... | nothing = true

private
  sigRefsDecl : Decl → List QName
  sigRefsDecl (sig _ _ t) = refsExpr t
  sigRefsDecl _ = []

  postulateReachIn : QName → List Unit → List Unit → List QName
  postulateReachIn targetMod us es with filterᵇ (λ u → not (anonymousUnit u)) us
  ... | named
    with map (λ u → uname u , concatMap (localCoreRef targetMod us es) (refsDecls (udecls u))) named
       | map uname (filterᵇ (λ u → isPostulate (udecls u)) named)
  ... | edges | seeds
    with map (λ v → uname v , map proj₁ (filterᵇ (λ e → elemᵇ _==ᴺ_ (uname v) (proj₂ e)) edges)) named
  ... | revEdges = closeCore (suc (length named)) revEdges seeds seeds

  sigTouchesPost : QName → List Unit → List Unit → List QName → Unit → Bool
  sigTouchesPost targetMod us es postReach u =
    anyᵇ (λ q → elemᵇ _==ᴺ_ q postReach)
      (concatMap (localCoreRef targetMod us es) (concatMap sigRefsDecl (udecls u)))

  specExtraDecls : QName → List Unit → List Unit → List QName → List QName → List Name → ℕ → List Unit → List Decl
  specExtraDecls targetMod us es postReach core used idx [] = []
  specExtraDecls targetMod us es postReach core used idx (u ∷ rest) with anonymousUnit u
  ... | true with sigTouchesPost targetMod us es postReach u
  ...   | false = udecls u ++ specExtraDecls targetMod us es postReach core used idx rest
  ...   | true with freshSpecTest (suc (length used)) idx used
  ...     | n = (if hasFun (udecls u) then concatMap (anonymousSig n) (udecls u) else [])
              ++ specExtraDecls targetMod us es postReach core (n ∷ used) (suc idx) rest
    where
      anonymousSig : Name → Decl → List Decl
      anonymousSig n (sig _ "_" t) = sig plain n t ∷ []
      anonymousSig n _ = []
  specExtraDecls targetMod us es postReach core used idx (u ∷ rest) | false =
    (if elemᵇ _==ᴺ_ (uname u) core then [] else concatMap namedSig (udecls u))
    ++ specExtraDecls targetMod us es postReach core used idx rest
    where
      namedSig : Decl → List Decl
      namedSig (sig _ n t) = sig plain n t ∷ []
      namedSig _ = []

-- Compiler-checkable view of a specification before its postulates are
-- implemented: keeps all core units, all concrete non-postulate-indexed
-- definitions/tests with full bodies, and checks postulate-dependent test
-- signatures as postulates.
specCheckOf : SpecΔ → Code
specCheckOf δ with localizeTo (child δ) (newIface δ)
... | loc with unitsIn (full (child δ)) loc | extUnits (code (child δ) [] loc)
... | us | es with filterᵇ (λ u → not (anonymousUnit u)) us
                 | refuteCoreNamesIn (child δ) loc us es
                 | postulateReachIn (child δ) us es
                 | map (λ u → shown (uname u)) us
... | named | refuteCore | postReach | used
  with nubᵇ _==ᴺ_ (refuteCore ++ map uname (filterᵇ (λ u → not (sigTouchesPost (child δ) us es postReach u)) named))
... | specCore = code (child δ) []
  (filterᵇ keepDecl loc ++ specExtraDecls (child δ) us es postReach specCore used 0 (filterᵇ topLevel us))
  where
    topLevel : Unit → Bool
    topLevel u = uname u ==ᴺ mkQ (full (child δ) ++ (shown (uname u) ∷ []))
    keepDecl : Decl → Bool
    keepDecl (fixity _ _ _) = true
    keepDecl d with declName d
    ... | just n = elemᵇ _==ᴺ_ (mkQ (full (child δ) ++ (n ∷ []))) specCore
    ... | nothing = true

-- 父亲建洞：给 import′ k 填上"我假设 k 暴露的接口"。Dump 出来的 assumes 总是空的，由这里填
withChildIface : QName → List Decl → Code → Code
withChildIface k ifc c = code (modName c) (params c) (map fill (decls c))
  where
    fill : Decl → Decl
    fill (import′ m o d oldAssumes) = if m ==ᴺ k then import′ m o d ifc else import′ m o d oldAssumes
    fill d                 = d

-- 一个接口（一串声明）里的单元，从 ext 的角度看：也就是孩子暴露出来的对象
exposed : QName → List Decl → List Obj
exposed k ifc = map (λ u → ext (uname u)) (unitsIn (full k) ifc)

------------------------------------------------------------------------
-- §8  flags：语境对象。换 OPTIONS = flags ⇝ flags，接口（flag 集合）一变，所有单元都有义务。
-- 另外一层约束沿文件树走：孩子的 infective 不能多于父亲，coinfective 不能少于父亲。
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §9  记忆：挂在对象上，沿 proarrow 继承
--   d 的记忆 = 所有 c ⇝ d 的 c 的记忆 + 这次的 why
--   c ⇝ ⊥：c 的记忆进 ⊥（坟场）——丢掉的东西也留一笔
--   没被碰的单元：记忆原样
------------------------------------------------------------------------

Memory : Set
Memory = List (Obj × List String)

notesOf : Memory → Obj → List String
notesOf []             o = []
notesOf ((o′ , ns) ∷ m) o = if o ==ᴼ o′ then ns ++ notesOf m o else notesOf m o

inherit : Plan → Memory → Memory
inherit p m = untouched ++ map forTarget (filterᵇ notBot (nubᵇ _==ᴼ_ (tgts p))) ++ graveyard
  where
    notBot : Obj → Bool
    notBot ⊥ = false
    notBot _ = true
    untouched : Memory
    untouched = filterᵇ (λ e → not (isSrc p (proj₁ e)) ∧ not (isTgt p (proj₁ e))) m
    -- 靶 t 的记忆：所有源的记忆接起来，再加这次的 why
    forTarget : Obj → Obj × List String
    forTarget t = t , (concatMap (notesOf m) (sourcesOf p t) ++ (why p ∷ []))
    -- 坟场：丢掉的东西的记忆，加上为什么丢
    graveyard : Memory
    graveyard with sourcesOf p ⊥
    ... | [] = []
    ... | ds = (⊥ , concatMap (notesOf m) ds ++ (why p ∷ [])) ∷ []

------------------------------------------------------------------------
-- §10  报告：孩子做完以后说什么
------------------------------------------------------------------------

data Verdict : Set where
  ok : Verdict
  contradiction : Code → Verdict

data CheckResult : Set where
  pass : CheckResult
  fail : String → CheckResult

isOk : Verdict → Bool
isOk ok = true
isOk _ = false

isPass : CheckResult → Bool
isPass pass = true
isPass _ = false

------------------------------------------------------------------------
-- §11  孩子那边要用的零件
------------------------------------------------------------------------

-- Core units are mandatory. Concrete helpers and any included named tests
-- must be verbatim; obligations need matching interfaces and may gain bodies.
-- Equality compares full names, so parent and child spellings agree.
satisfies : SpecΔ → Code → Bool
satisfies δ new with localizeTo (child δ) (newIface δ)
... | loc with unitsIn (full (child δ)) loc | units new
... | us | newUnits with coreNamesIn (child δ) us (extUnits (code (child δ) [] loc))
... | core = allᵇ present us
  where
    present : Unit → Bool
    present u with anonymousUnit u | lookupUnit newUnits (uname u)
    ... | true | _ = true
    ... | false | nothing = not (elemᵇ _==ᴺ_ (uname u) core)
    ... | false | just v =
      if elemᵇ _==ᴺ_ (uname u) core ∧ not (hasFun (udecls u))
      then eqIface (ifaceOfDecls (udecls u)) (ifaceOfDecls (udecls v))
      else eqDecls (udecls u) (udecls v)

-- Append tests and their scope declarations without duplicating concrete
-- core helpers, named tests already supplied by the child, or imports/opens.
withTests : Code → List Decl → Code
withTests c rawIface with localizeTo (modName c) rawIface
... | loc with unitsIn (full (modName c)) loc | units c
... | us | existing with coreNamesIn (modName c) us (extUnits (code (modName c) [] loc))
... | core = code (modName c) (params c) (decls c ++ filterᵇ appendDecl loc)
  where
    missingTest : Name → Bool
    missingTest n with lookupUnit us q | lookupUnit existing q
      where q = mkQ (full (modName c) ++ (n ∷ []))
    ... | just u | nothing = not (elemᵇ _==ᴺ_ (uname u) core)
    ... | _ | _ = false

    appendDecl : Decl → Bool
    appendDecl d@(import′ _ _ _ _) = not (anyᵇ (eqDecl d) (decls c))
    appendDecl d@(open′ _ _) = not (anyᵇ (eqDecl d) (decls c))
    appendDecl (fixity _ _ n) = missingTest n
    appendDecl (sig _ "_" _) = true
    appendDecl (fun _ "_" _) = true
    appendDecl d with declName d
    ... | just n = missingTest n
    ... | nothing = false

-- Interface seeds are the parent's decisions, localized to this node.
withChildIfaces : List (QName × List Decl) → Code → Code
withChildIfaces [] c = c
withChildIfaces ((k , ds) ∷ ks) c = withChildIfaces ks (withChildIface k ds c)

eqMove : Proarrow → Proarrow → Bool
eqMove (a ⇝ b) (c ⇝ d) = a ==ᴼ c ∧ b ==ᴼ d

-- A parent describes the change from its last conditional interface. A child
-- may have committed that interface, or stopped and restored an earlier one.
alignSpecΔ : Code → List Decl → SpecΔ → SpecΔ
alignSpecΔ old oldSpec raw with objects old | map uname (units (stubOf raw)) | coreNames (child raw) oldSpec
... | oldObjs | newCore | oldCore = record raw { δarrows = complete (concatMap align (δarrows raw)) }
  where
    present : QName → Bool
    present q = elemᵇ _==ᴼ_ (unit q) oldObjs

    supply : QName → Proarrow
    supply v = if present v then keep (ext v) else ⊥ ⇝ ext v

    align : Proarrow → List Proarrow
    align (⊥ ⇝ ext v) = [ supply v ]
    align a@(ext u ⇝ ext v) = [ if present u then a else supply v ]
    align a@(ext u ⇝ ⊥) = if present u then [ a ] else []
    align a = [ a ]

    complete : List Proarrow → List Proarrow
    complete aligned with map tgt aligned | map src aligned
    ... | targets | sources = nubᵇ eqMove
      (aligned ++ map supply (filterᵇ (λ v → not (elemᵇ _==ᴼ_ (ext v) targets)) newCore)
               ++ map (λ u → ext u ⇝ ⊥) (filterᵇ retired oldCore))
      where
        retired : QName → Bool
        retired u = present u ∧ not (elemᵇ _==ᴺ_ u newCore) ∧ not (elemᵇ _==ᴼ_ (ext u) sources)

reseedSelf : Code → SpecΔ → SpecΔ
reseedSelf current d = alignSpecΔ current (newIface d) d

mergeMoves : List Proarrow → List Proarrow → List Proarrow
mergeMoves xs ys = nubᵇ eqMove (xs ++ ys)

localObj : QName → Obj → Obj
localObj k (ext q) = if isPrefix (full k) (full q) then unit q else ext q
localObj k o = o

seedArrows : SpecΔ → List Proarrow
seedArrows δ = map (λ a → localObj (child δ) (src a) ⇝ localObj (child δ) (tgt a)) (δarrows δ)

extendsSeed : SpecΔ → Plan → Bool
extendsSeed δ p = allᵇ (λ a → elemᵇ eqMove a (moves p)) seeds
               ∧ allᵇ locked (moves p)
  where
    seeds = seedArrows δ
    boundary = map src seeds ++ map tgt seeds
    onBoundary : Obj → Bool
    onBoundary ⊥ = false
    onBoundary o = elemᵇ _==ᴼ_ o boundary
    locked : Proarrow → Bool
    locked a = if onBoundary (src a) ∨ onBoundary (tgt a) then elemᵇ eqMove a seeds else true

-- g records references from every theorem/function, not just anonymous tests.
testDeps : Code → List (Name × List Obj)
testDeps c = map (λ u → shown (uname u) , filterᵇ external (depsOf c u)) (units c)
  where
    external : Obj → Bool
    external (ext _) = true
    external _ = false

impactsChild : Code → Code → Plan → QName → Bool
impactsChild old cand p k =
  not (eqDecls (newIface (restrict old p k)) (newIface (restrict cand p k)))
  ∨ not (eqList sameDep (atChild old) (atChild cand))
  ∨ anyᵇ changedBoundary (moves p)
  where
    atChild : Code → List (Name × List Obj)
    atChild c = filterᵇ (λ e → not (nullᵇ (proj₂ e)))
      (map (λ e → proj₁ e , filterᵇ (underModule k) (proj₂ e)) (testDeps c))
    sameDep : (Name × List Obj) → (Name × List Obj) → Bool
    sameDep (n , xs) (m , ys) = n ==ˢ m ∧ eqList _==ᴼ_ xs ys
    changedBoundary : Proarrow → Bool
    changedBoundary a = (underModule k (src a) ∨ underModule k (tgt a)) ∧ not (preserves old cand p a)

restrictMemory : QName → Memory → Memory
restrictMemory k m = map (λ e → localObj k (proj₁ e) , proj₂ e) (filterᵇ (λ e → underModule k (proj₁ e)) m)

absorbDeadMemory : QName → Memory → Memory → Memory
absorbDeadMemory k childMem parentMem =
  filterᵇ (λ e → not (proj₁ e ==ᴼ ⊥) ∧ not (underModule k (proj₁ e))) parentMem
  ++ ((⊥ , notesOf parentMem ⊥ ++ concatMap proj₂ childMem
         ++ concatMap proj₂ (filterᵇ (λ e → underModule k (proj₁ e)) parentMem)) ∷ [])
