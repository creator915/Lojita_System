------------------------------------------------------------------------
-- Ownership.agda  （第四版：开放世界）
--
-- 用 Agda 脚本代替 shell：   文件 = 数据 ⊗ 资源，   脚本 = 树到树的箭头
--
--   数据 ：Agda 的普通类型（Set）。笛卡尔。字节怎么变成它是 IO 层的事（Main.agda）。
--   资源 ：St。线性：状态是一棵树；一格是文件、目录，或者一根信道——子树交出去以后留下的收据。
--   脚本 ：Prog Ψ s s′ A。一段有限的、类型检查过的脚本；Ψ 是它用到的外部接口清单。
--
-- 这个文件描述的是结构，不是整个系统的一生：
--   对面坐着人和 LLM，完整的过程不可预期；能预先规划的只有形状（St）和协议（Session）。
--   IO 层在需要的时候把现实世界接到 Chan 格子上。内核里没有 IO，没有 postulate。
--
-- 和第三版相比：
--   * 层数 ℓ 删掉了。它是封闭世界的产物：为了让 eval 钻进孩子的程序还能终止。
--   * fork z q κ（父亲的程序里装着孩子的程序 q）换成 exec：只交出接口 S，不交出程序。
--       孩子的程序由环境在需要时提供。纯模型里环境是一张假设清单 Ψ 的解释 Env Ψ
--       （root.test 里的模拟接口）；现实里是 LLM + agda 检查 + 调度器。
--   * Prog / Proc / Server 多了一个索引 Ψ : List Spec。一条 Spec = (名字, 子树形状, 协议)，
--       读作相继式 Γ ⊢ S："谁拿到这棵子树，就要兑现这个协议"。按名字找，和目录里找格子一样。
--       父亲对 Ψ 负责，孩子各自对自己那一条负责，连接（cut）在运行时发生——
--       这就是 A.test × B.test × root ⊢ root.test 那一步。
--   * eval 多了一个参数 env : Env Ψ。eval 不再递归进孩子，所以不需要任何终止量。
--   * 新增命令 recover：岛结束后把子树原地收回（和 stop 对称）。父亲的动词只有两个：交出去、收回来。
--   * 定理 cut-data / cut-res / serve-stop 改名 link-*：把 env 取成 provide q，结论仍是 refl。
--   * "自己 fork 自己再 call 它"的服务不再被类型拒绝：它不在类型里，它是环境的事。
--
-- 读法建议：先看 §3 末尾的例子（例 5、6、8 是开放世界的样子），再回头看 §2，最后看 §4。
-- 检查方式：agda -i . -i <stdlib路径> Ownership.agda   (Agda 2.6.3, stdlib 1.7.3)
------------------------------------------------------------------------
{-# OPTIONS --guardedness #-}
module Ownership where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (Bool; true; false; not; T; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

import Data.String.Properties as Str
import Data.List.Relation.Binary.Permutation.Propositional as Perm

variable
  A B Q R I : Set

------------------------------------------------------------------------
-- §1  数据侧：就是 Set
------------------------------------------------------------------------

-- 数据是 Agda 里任何一个普通类型的值。复制、丢弃不需要任何许可：
-- 这就是 ! 的 δ 和 ε。这里没有"定义数据"——不需要。内核不知道也不关心数据的形状。
copy : A → A × A
copy a = a , a

-- 关键的不是数据长什么样，而是数据里装不着资源：
-- 资源不是值，是下面 St 里的"索引"（类型层的东西）。索引没法被装进一个值里
-- 再偷运出去，所以无论 A 是什么，File A 里的东西都复制不出一份资源。

------------------------------------------------------------------------
-- §2  资源侧：状态是一棵树，树上可以长出信道
------------------------------------------------------------------------

Name : Set
Name = String

data St      : Set₁
Ctx          : Set₁
data Ty      : Set₁
data Session : Set₁

-- 资源的状态。
--   File A  ：一个文件，内容类型是 A。内容在数据侧，这里只记"有一个 A"。
--   Dir Γ   ：一个目录，持有孩子们。孩子的状态嵌在父亲的状态里——
--             这一句就是所有权：file 1 持有 file 2 = file 2 的状态是 file 1 状态的一部分。
--   Chan S  ：一根信道的一端。子树交出去以后留在原位的收据：格子、位置、名字都还在，
--             里面没有文件，只有一张单子 S——"对面将来会给我什么"。空间的格子里装着时间。
--
-- 没有 Absent  ：不存在的东西就是不在父亲的清单里；Dir [] 已经是"空"（幺半范畴的单位）。
-- 没有 Open/Closed：open 只是向运行时领一个读者份额，类型层看不见它。
-- 没有 write   ：内容只在 create 时进来；"修改"就是 unlink 旧的、create 新的。
data St where
  File : Set     → St
  Dir  : Ctx     → St
  Chan : Session → St

Ctx = List (Name × St)

-- 信道上能传两种东西，正好对应两侧：
data Ty where
  Res : St  → Ty          -- 一棵子树（线性：送出去就不在我手里了）
  ∃Res : (I : Set) → (I → St) → Ty
  Dat : Set → Ty          -- 一个值（笛卡尔：送出去我手里还有）

-- 会话类型 = 线性逻辑的命题。
-- 命题没有视角：同一个 S，站在右边（提供它，Proc）是一种做法，站在左边（使用它，Cmd）
-- 是另一种做法。所以这里没有 dual——对偶就是换一边站。
-- 构造子的名字按"提供者"读：
infixr 5 _⊗_ _⊸_
data Session where
  End : Session                     -- 1      ：协议走完
  _⊗_ : Ty → Session → Session      -- t ⊗ S  ：先交出一个 t，再按 S 走
  _⊸_ : Ty → Session → Session      -- t ⊸ S  ：先收进一个 t，再按 S 走
  SrvI : (Q R I : Set) → (I → St) → Session    -- Srv Q R s′ = νX. &{ call : Dat Q ⊸ Dat R ⊗ X , stop : Res s′ ⊗ End }
                                    --   常驻服务：问一次答一次、可以无限次；或者关门，把 s′ 交还

-- 一条假设：名字 n 处的子树（形状 Γ）交出去以后，对面兑现协议 S。读作相继式 Γ ⊢ S。
-- 一段脚本的类型里带一张假设清单 Ψ：它用到哪些外部接口（服务、别的 agent……）。
-- 谁来兑现这些假设，脚本不知道，也不该知道——那是环境的事。
Srv : Set → Set → St → Session
Srv Q R s = SrvI Q R ⊤ (λ _ → s)

record Spec : Set₁ where
  constructor specI
  field
    sname : Name
    Idx   : Set
    sctx  : Idx → Ctx
    ssess : Idx → Session
open Spec public

mkSpec : Name → Ctx → Session → Spec
mkSpec n Γ S = specI n ⊤ (λ _ → Γ) (λ _ → S)

variable
  s s′ s″ r : St
  Γ Δ       : Ctx
  n n′ m    : Name
  F         : I → St
  S         : Session
  Ψ         : List Spec

-- "名字 n 在 Γ 里有一格"：一个位置证明。只按名字找，不管那一格现在是什么状态。
_↦_ : Name → Ctx → Set₁
n ↦ Γ = Any (λ e → proj₁ e ≡ n) Γ

-- "名字 n 在清单 Ψ 里有一条假设"：同样的东西，清单换成 Ψ。名字在清单里就是假设的身份。
_↦ₛ_ : Name → List Spec → Set₁
n ↦ₛ Ψ = Any (λ ψ → sname ψ ≡ n) Ψ

specOf : n ↦ₛ Ψ → Spec
specOf (here {x = ψ} _) = ψ
specOf (there h) = specOf h

idxOf : n ↦ₛ Ψ → Set
idxOf h = Idx (specOf h)

ctxAt : (h : n ↦ₛ Ψ) → idxOf h → Ctx
ctxAt h = sctx (specOf h)

sessionAt : (h : n ↦ₛ Ψ) → idxOf h → Session
sessionAt h = ssess (specOf h)

ctxOf : (h : n ↦ₛ Ψ) → {{i : idxOf h}} → Ctx
ctxOf h {{i}} = ctxAt h i

sessionOf : (h : n ↦ₛ Ψ) → {{i : idxOf h}} → Session
sessionOf h {{i}} = sessionAt h i

-- 那一格现在的状态
stateOf : n ↦ Γ → St
stateOf (here {x = e} _) = proj₂ e
stateOf (there x)        = stateOf x

-- 把那一格换成新状态 / 把那一格拿掉。
-- "没有修改，只有消费旧的、生产新的"：它们生产一个新的清单，旧清单不再是任何命令的合法起点。
set : n ↦ Γ → St → Ctx
set {Γ = e ∷ Γ} (here _)  s′ = (proj₁ e , s′) ∷ Γ
set {Γ = e ∷ Γ} (there x) s′ = e ∷ set x s′

remove : n ↦ Γ → Ctx
remove {Γ = _ ∷ Γ} (here _)  = Γ
remove {Γ = e ∷ Γ} (there x) = e ∷ remove x

-- 几个关于状态的判断。它们算成 ⊤ 或 ⊥，所以具体情况下 Agda 自己能判定。
IsFile IsDir IsEmptyDir : St → Set
IsFile (File _)     = ⊤
IsFile _            = ⊥
IsDir  (Dir _)      = ⊤
IsDir  _            = ⊥
IsEmptyDir (Dir []) = ⊤
IsEmptyDir _        = ⊥

children : St → Ctx
children (Dir Δ) = Δ
children _       = []

-- 原子命令：内核答应你的几件事，也就是工具注册表。读法：消费状态 s，产出状态 s′，交出一个 A。
-- 名字属于目录，所以生灭名字的全是目录命令；文件自己只会被读。
module Raw where
  data Cmd : St → St → Set → Set₁ where

    -- 叶子命令：唯一的一个。线性侧跨到笛卡尔侧的那一步：交出一个 A，文件还在。
    read   : Cmd (File A) (File A) A

    reorder : Γ Perm.↭ Δ → Cmd (Dir Γ) (Dir Δ) ⊤

    -- 目录命令：名字的生与灭
    create : (n : Name) → ¬ (n ↦ Γ) → A
           → Cmd (Dir Γ) (Dir ((n , File A) ∷ Γ)) ⊤
    unlink : (x : n ↦ Γ) → IsFile (stateOf x)
           → Cmd (Dir Γ) (Dir (remove x)) ⊤
    mkdir  : (n : Name) → ¬ (n ↦ Γ)
           → Cmd (Dir Γ) (Dir ((n , Dir []) ∷ Γ)) ⊤
    rmdir  : (x : n ↦ Γ) → IsEmptyDir (stateOf x)             -- 只能删空目录：所有权的核心约束
           → Cmd (Dir Γ) (Dir (remove x)) ⊤

    -- 硬链接：给同一份内容再起一个名字。这是命令版的 δ（有副作用、要记账），不是结构规则。
    -- 前提 IsFile：只有笛卡尔的东西（文件内容）才能有两个名字。给目录起别名会让一棵
    -- 线性的子树有两个主人——Unix 禁止对目录硬链接，正是为了让名字层保持是树。
    link   : (x : n ↦ Γ) → IsFile (stateOf x) → (n′ : Name) → ¬ (n′ ↦ Γ)
           → Cmd (Dir Γ) (Dir ((n′ , stateOf x) ∷ Γ)) ⊤

    -- 搬运：把子目录 n′ 里的孩子 n 提到当前目录 / 把当前目录的 n 放进子目录 n′。
    -- 守恒：树上的叶子一个不多一个不少，只是换了位置。
    up     : (x : n′ ↦ Γ) → IsDir (stateOf x) → (z : n ↦ children (stateOf x)) → ¬ (n ↦ Γ)
           → Cmd (Dir Γ) (Dir ((n , stateOf z) ∷ set x (Dir (remove z)))) ⊤
    down   : (z : n ↦ Γ) (x : n′ ↦ remove z) → IsDir (stateOf x) → ¬ (n ↦ children (stateOf x))
           → Cmd (Dir Γ) (Dir (set x (Dir ((n , stateOf z) ∷ children (stateOf x))))) ⊤

    -- 信道命令：全是左规则——"我手里有一根 Chan S，我怎么用它"。
    -- 对面交出 t（⊗），我这边就收；对面要收 t（⊸），我这边就发。
    -- 前提 stateOf c ≡ Chan … 由类型检查算出来（见 §3），用户只写名字。
    recv    : (c : n′ ↦ Γ) → stateOf c ≡ Chan (Res r ⊗ S) → (n : Name) → ¬ (n ↦ Γ)
            → Cmd (Dir Γ) (Dir ((n , r) ∷ set c (Chan S))) ⊤          -- 子树出信道，起个名字 = up
    recvD   : (c : n′ ↦ Γ) → stateOf c ≡ Chan (Dat A ⊗ S)
            → Cmd (Dir Γ) (Dir (set c (Chan S))) A                    -- 收一个值
    send    : (z : n ↦ Γ) (c : n′ ↦ remove z) → stateOf c ≡ Chan (Res (stateOf z) ⊸ S)
            → Cmd (Dir Γ) (Dir (set c (Chan S))) ⊤                    -- 子树进信道，名字消失 = down
    sendD   : (c : n′ ↦ Γ) → stateOf c ≡ Chan (Dat A ⊸ S) → A
            → Cmd (Dir Γ) (Dir (set c (Chan S))) ⊤                    -- 发一个值，手里还有
    close   : (c : n′ ↦ Γ) → stateOf c ≡ Chan End
            → Cmd (Dir Γ) (Dir (remove c)) ⊤                          -- 走完才能关 = rmdir 只删空目录
    recover : (c : n′ ↦ Γ) → stateOf c ≡ Chan (Res r ⊗ End)
            → Cmd (Dir Γ) (Dir (set c r)) ⊤                           -- 原地收回：岛结束，收据变回子树
    call    : (c : n′ ↦ Γ) → stateOf c ≡ Chan (SrvI Q R I F) → Q
            → Cmd (Dir Γ) (Dir (set c (Chan (SrvI Q R I F)))) R          -- 问一次，回到原点（ν 展开一圈）
    stop    : (c : n′ ↦ Γ) → stateOf c ≡ Chan (Srv Q R s′)
            → Cmd (Dir Γ) (Dir (set c s′)) ⊤                          -- 关门：句柄变回一棵子树

open Raw using (Cmd)

-- 三样东西互相定义：
--   Prog   ：脚本。一根线上往前走（step）、往树下走（focus）、把一棵子树交出去（exec）。
--   Proc   ：岛上的程序。相继式 Γ ⊢ S 的证明：用掉 Γ 里的资源，在一根信道上提供 S。
--   Server ：常驻的岛。余归纳：每一步有限，没有终点。
data Prog : List Spec → St → St → Set → Set₁
data Proc : List Spec → Ctx → Session → Set₁
record ServerI (Ψ : List Spec) (Q R I : Set) (Γ : Ctx) (F : I → St) : Set₁

-- 脚本 = 命令的类型化序列，外加两种 cut。
--   step  ：线性就在它的类型里——上一步的出口必须是下一步的入口。
--   focus ：把一段只认识孩子 x 的脚本，提升到父亲身上。Γ 的其余格子原样穿过。
--           这是 id_Γ ⊗ (—)：张量的函子性。借用、frame 规则、"子函数只能碰传给它的东西"全在这里。
--           父亲等孩子跑完。同一个进程，同一段事务。
--   exec  ：把目录 z 里的东西整个交出去，z 这一格变成信道。交出去的只有接口：
--           Ψ 里叫 z 的那条假设 h 说了要什么形状的子树（ctxOf h，必须和 z 下面的一样）、
--           对面会兑现什么协议（sessionOf h）。对面是谁、它的程序长什么样，这段脚本不知道。
--           父亲不等，接着跑 κ。这是 cut 的开放版本：左边不放证明，放一个洞；洞的形状就是那条假设。
data Prog where
  done  : A → Prog Ψ s s A
  step  : Cmd s s′ A → (A → Prog Ψ s′ s″ B) → Prog Ψ s s″ B
  focus : (x : n ↦ Γ) → Prog Ψ (stateOf x) s′ A
        → (A → Prog Ψ (Dir (set x s′)) s″ B) → Prog Ψ (Dir Γ) s″ B
  exec  : (z : n ↦ Γ) (p : IsDir (stateOf z)) (h : m ↦ₛ Ψ) (i : idxOf h)
        → ctxAt h i ≡ children (stateOf z)
        → Prog Ψ (Dir (set z (Chan (sessionAt h i)))) s″ B → Prog Ψ (Dir Γ) s″ B
  stopI : (c : n ↦ Γ) → stateOf c ≡ Chan (SrvI Q R I F)
        → ((i : I) → Prog Ψ (Dir (set c (F i))) s″ B) → Prog Ψ (Dir Γ) s″ B

-- 岛上的程序：构造子就是会话类型的右规则。读法：Proc Ψ Γ S = "手里有 Γ，答应对面 S"。
-- 它自己也可以用 Ψ 里的假设再开岛。
data Proc where
  run    : Prog Ψ (Dir Γ) (Dir Δ) A → (A → Proc Ψ Δ S) → Proc Ψ Γ S                   -- 静默一步：先算，再接着承诺
  end    : Proc Ψ [] End                                                             -- 1R  ：说完了，手里必须空
  giveAt : (x : n ↦ Γ) → Proc Ψ (remove x) S → Proc Ψ Γ (Res (stateOf x) ⊗ S)         -- ⊗R  ：交出一格，它从我的清单消失
  tell   : A → Proc Ψ Γ S → Proc Ψ Γ (Dat A ⊗ S)                                       -- ⊗R  ：交出一个值，手里还有
  takeAt : (n : Name) → ¬ (n ↦ Γ) → Proc Ψ ((n , r) ∷ Γ) S → Proc Ψ Γ (Res r ⊸ S)     -- ⊸R  ：收进一格，给它起个名字
  ask    : (A → Proc Ψ Γ S) → Proc Ψ Γ (Dat A ⊸ S)                                     -- ⊸R  ：收一个值
  give∃At : (i : I) (x : n ↦ Γ) → stateOf x ≡ F i
          → Proc Ψ (remove x) S → Proc Ψ Γ (∃Res I F ⊗ S)
  machine : {J : Set} {G : J → Ctx}
          → ((j : J) → Proc Ψ (G j) (Dat Q ⊸ Dat R ⊗ ∃Res J (λ j′ → Dir (G j′)) ⊗ End))
          → ((j : J) → Proc Ψ (G j) (∃Res I F ⊗ End))
          → (j : J) → Proc Ψ (G j) (SrvI Q R I F)
  give∃Dir : (i : I) → Dir Γ ≡ F i → Proc Ψ Γ (∃Res I F ⊗ End)
  stopP : (c : n ↦ Γ) → stateOf c ≡ Chan (SrvI Q R I F)
        → ((i : I) → Proc Ψ (set c (F i)) S) → Proc Ψ Γ S
  daemon : ServerI Ψ Q R I Γ F → Proc Ψ Γ (SrvI Q R I F)                                   -- νR  ：以下无限

-- 常驻的岛：对面挑哪个分支，我才算哪个——余归纳记录按需展开，正好是 & 的惰性。
--   call ：收一个 Q，答一个 R，然后又是一个服务（可能换了一副家当 Δ）
--   stop ：把手里的东西整理成一棵 s′ 交还，然后结束
-- 它的每一步是一段有限的脚本；"下一步是什么"被问到才展开——在 Harness 里，填这个字段的是 LLM。
record ServerI Ψ Q R I Γ F where
  coinductive
  field
    call : Proc Ψ Γ (Dat Q ⊸ Dat R ⊗ SrvI Q R I F)
    stop : Proc Ψ Γ (∃Res I F ⊗ End)

Server : List Spec → Set → Set → Ctx → St → Set₁
Server Ψ Q R Γ s = ServerI Ψ Q R ⊤ Γ (λ _ → s)

infixl 1 _>>=_ _>>_

_>>=_ : Prog Ψ s s′ A → (A → Prog Ψ s′ s″ B) → Prog Ψ s s″ B
done a       >>= f = f a
step c κ     >>= f = step c    λ a → κ a >>= f
focus x p κ  >>= f = focus x p λ a → κ a >>= f
exec z p h i e κ >>= f = exec z p h i e (κ >>= f)
stopI c e κ >>= f = stopI c e λ i → κ i >>= f

_>>_ : Prog Ψ s s′ A → Prog Ψ s′ s″ B → Prog Ψ s s″ B
p >> q = p >>= λ _ → q

-- 清单在一个任务里是固定的（它是语境，元层的东西），所以这里不提供 weakening；
-- 不用 exec 的脚本对 Ψ 多态，天然可以在任何清单下复用。

------------------------------------------------------------------------
-- §3  用户接口与所有权
------------------------------------------------------------------------

-- 用户只写名字；位置证明和前提由类型检查器算出来。算的方式分两条线：
--
--   对象线（出现在下一步的类型里）      member / lookupSt / delete / update ：名字层的一阶函数，在 Γ 里走一趟
--   许可线（实例参数）                  T (member n Γ)、IsFile (lookupSt n Γ)、lookupSt c Γ ≡ Chan …：算成 ⊤ / x ≡ x，
--                                      由下面几个实例接住；算成 ⊥ 就是类型错误
--
-- Raw 层要的位置证明 n ↦ Γ 只在包装里由 member-at 造出来，三条 coherence 引理（remove-at / set-at / stateOf-at）
-- 说 Raw 用位置算出来的 remove / set / stateOf 和名字层算出来的 delete / update / lookupSt 是同一个东西。
--
-- 为什么不直接把 remove (at w) 写进类型（第四版以前是这样）：那样下一步的上下文是"沿着上一步的证明再删一格"，
-- 证明的类型里又装着上一步的整个上下文——二十步就是一座二十层的塔，每层把下面的塔抄好几份，
-- 检查器的内存按指数长。现在类型里只有一阶函数套一阶函数（delete n (update m s Γ)），一条链，几十步也是几秒。
-- 效果不变：脚本还是只写名字，Raw / eval / §4 一个字不动；具体脚本上 coherence 引理算成 refl，包装里的 subst 消失。

infix 4 _==ⁿ_
_==ⁿ_ : Name → Name → Bool
_==ⁿ_ = Str._==_          -- = isYes (m ≟ n)：真的是判定，所以 T (m ==ⁿ n) 能换出 m ≡ n（toWitness）

member   : Name → Ctx → Bool        -- 名字在不在
lookupSt : Name → Ctx → St          -- 那一格的状态（找不到就给 Dir []；包装都先要 member，碰不到这里）
delete   : Name → Ctx → Ctx         -- 拿掉那一格
update   : Name → St → Ctx → Ctx    -- 换掉那一格

member n []            = false
member n ((m , _) ∷ Γ) = if m ==ⁿ n then true else member n Γ
lookupSt n []            = Dir []
lookupSt n ((m , s) ∷ Γ) = if m ==ⁿ n then s else lookupSt n Γ
delete n []            = []
delete n ((m , s) ∷ Γ) = if m ==ⁿ n then Γ else (m , s) ∷ delete n Γ
update n s′ []            = []
update n s′ ((m , s) ∷ Γ) = if m ==ⁿ n then (m , s′) ∷ Γ else (m , s) ∷ update n s′ Γ

-- 许可 → 位置。一格一格走：这一格叫 m，b 是 m ==ⁿ n 的结果，e 记着 b 的来历（b 为真时由它换出 m ≡ n）。
-- 把 b 当参数而不用 with：with 要在类型里把 m ≟ n 抽出来，可 ≟ 在不同地方展开得不一样，抽不干净。
mutual
  member-at : (n : Name) (Γ : Ctx) → T (member n Γ) → n ↦ Γ
  member-at n []            ()
  member-at n ((m , s) ∷ Γ) w = atStep n m s Γ (m ==ⁿ n) refl w

  atStep : (n m : Name) (s : St) (Γ : Ctx) (b : Bool) → b ≡ (m ==ⁿ n)
         → T (if b then true else member n Γ) → n ↦ ((m , s) ∷ Γ)
  atStep n m s Γ true  e _ = here (toWitness {Q = m Str.≟ n} (subst T e tt))
  atStep n m s Γ false e w = there (member-at n Γ w)

mutual
  ¬member : (n : Name) (Γ : Ctx) → T (not (member n Γ)) → ¬ (n ↦ Γ)
  ¬member n []            _ ()
  ¬member n ((m , s) ∷ Γ) f = ¬step n m s Γ (m ==ⁿ n) refl f

  ¬step : (n m : Name) (s : St) (Γ : Ctx) (b : Bool) → b ≡ (m ==ⁿ n)
        → T (not (if b then true else member n Γ)) → ¬ (n ↦ ((m , s) ∷ Γ))
  ¬step n m s Γ true  e ()
  ¬step n m s Γ false e f (here q)  = toWitnessFalse {Q = m Str.≟ n} (subst (λ b → T (not b)) e tt) q
  ¬step n m s Γ false e f (there x) = ¬member n Γ f x

-- coherence：Raw 沿位置算的 = 名字层算的
remove-at : (n : Name) (Γ : Ctx) (w : T (member n Γ)) → remove (member-at n Γ w) ≡ delete n Γ
remove-at n []            ()
remove-at n ((m , s) ∷ Γ) w = go (m ==ⁿ n) refl w
  where
    go : ∀ b (e : b ≡ (m ==ⁿ n)) (w : T (if b then true else member n Γ))
       → remove (atStep n m s Γ b e w) ≡ (if b then Γ else (m , s) ∷ delete n Γ)
    go true  e _ = refl
    go false e w = cong ((m , s) ∷_) (remove-at n Γ w)

set-at : (n : Name) (Γ : Ctx) (w : T (member n Γ)) (s′ : St) → set (member-at n Γ w) s′ ≡ update n s′ Γ
set-at n []            ()
set-at n ((m , s) ∷ Γ) w s′ = go (m ==ⁿ n) refl w
  where
    go : ∀ b (e : b ≡ (m ==ⁿ n)) (w : T (if b then true else member n Γ))
       → set (atStep n m s Γ b e w) s′ ≡ (if b then (m , s′) ∷ Γ else (m , s) ∷ update n s′ Γ)
    go true  e _ = refl
    go false e w = cong ((m , s) ∷_) (set-at n Γ w s′)

stateOf-at : (n : Name) (Γ : Ctx) (w : T (member n Γ)) → stateOf (member-at n Γ w) ≡ lookupSt n Γ
stateOf-at n []            ()
stateOf-at n ((m , s) ∷ Γ) w = go (m ==ⁿ n) refl w
  where
    go : ∀ b (e : b ≡ (m ==ⁿ n)) (w : T (if b then true else member n Γ))
       → stateOf (atStep n m s Γ b e w) ≡ (if b then s else lookupSt n Γ)
    go true  e _ = refl
    go false e w = stateOf-at n Γ w

-- 清单 Ψ 那边不变：Ψ 在一个任务里是固定的，不会一层层长，判定过程直接给位置证明就好
_↦ₛ?_ : (n : Name) (Ψ : List Spec) → Dec (n ↦ₛ Ψ)
n ↦ₛ? Ψ = any? (λ ψ → sname ψ Str.≟ n) Ψ

atₛ : True (n ↦ₛ? Ψ) → n ↦ₛ Ψ
atₛ = toWitness

instance
  ⊤-inst : ⊤
  ⊤-inst = tt
  ×-inst : {{a : A}} {{b : B}} → A × B
  ×-inst {{a}} {{b}} = a , b
  ≡-inst : ∀ {ℓ} {X : Set ℓ} {x : X} → x ≡ x
  ≡-inst = refl

-- 把一条 Raw 命令沿两头的等式搬过去。具体脚本上等式算成 refl，这一层就消失
castCmd : {s₁ s₁′ s₂ s₂′ : St} → s₁ ≡ s₂ → s₁′ ≡ s₂′ → Cmd s₁ s₁′ A → Cmd s₂ s₂′ A
castCmd refl refl c = c

-- 路标：什么也不做，只把此刻的目录形状写出来给人看
checkpoint : (Γ : Ctx) → Prog Ψ (Dir Γ) (Dir Γ) ⊤
checkpoint _ = done tt

read : Prog Ψ (File A) (File A) A
read = step Raw.read done

inside : (n : Name) {{w : T (member n Γ)}}
       → Prog Ψ (lookupSt n Γ) s′ A → Prog Ψ (Dir Γ) (Dir (update n s′ Γ)) A
inside {Γ = Γ} {s′ = s′} {A = A} n {{w}} p =
  subst (λ Γ′ → Prog _ (Dir Γ) (Dir Γ′) A) (set-at n Γ w s′)
    (focus (member-at n Γ w) (subst (λ s → Prog _ s s′ A) (sym (stateOf-at n Γ w)) p) done)

create : (n : Name) {{f : T (not (member n Γ))}} → A → Prog Ψ (Dir Γ) (Dir ((n , File A) ∷ Γ)) ⊤
create {Γ = Γ} n {{f}} a = step (Raw.create n (¬member n Γ f) a) done

unlink : (n : Name) {{w : T (member n Γ)}} {{p : IsFile (lookupSt n Γ)}}
       → Prog Ψ (Dir Γ) (Dir (delete n Γ)) ⊤
unlink {Γ = Γ} n {{w}} {{p}} =
  step (castCmd refl (cong Dir (remove-at n Γ w))
         (Raw.unlink (member-at n Γ w) (subst IsFile (sym (stateOf-at n Γ w)) p))) done

mkdir : (n : Name) {{f : T (not (member n Γ))}} → Prog Ψ (Dir Γ) (Dir ((n , Dir []) ∷ Γ)) ⊤
mkdir {Γ = Γ} n {{f}} = step (Raw.mkdir n (¬member n Γ f)) done

rmdir : (n : Name) {{w : T (member n Γ)}} {{p : IsEmptyDir (lookupSt n Γ)}}
      → Prog Ψ (Dir Γ) (Dir (delete n Γ)) ⊤
rmdir {Γ = Γ} n {{w}} {{p}} =
  step (castCmd refl (cong Dir (remove-at n Γ w))
         (Raw.rmdir (member-at n Γ w) (subst IsEmptyDir (sym (stateOf-at n Γ w)) p))) done

link : (n n′ : Name) {{w : T (member n Γ)}} {{p : IsFile (lookupSt n Γ)}} {{f : T (not (member n′ Γ))}}
     → Prog Ψ (Dir Γ) (Dir ((n′ , lookupSt n Γ) ∷ Γ)) ⊤
link {Γ = Γ} n n′ {{w}} {{p}} {{f}} =
  step (castCmd refl (cong (λ s → Dir ((n′ , s) ∷ Γ)) (stateOf-at n Γ w))
         (Raw.link (member-at n Γ w) (subst IsFile (sym (stateOf-at n Γ w)) p) n′ (¬member n′ Γ f))) done

-- 搬运。n′ 是子目录，n 是要搬的那一格。两层名字：先在 Γ 里找 n′，再在它的孩子里找 n
up : (n′ n : Name) {{w : T (member n′ Γ)}} {{p : IsDir (lookupSt n′ Γ)}}
     {{z : T (member n (children (lookupSt n′ Γ)))}} {{f : T (not (member n Γ))}}
   → Prog Ψ (Dir Γ) (Dir ((n , lookupSt n (children (lookupSt n′ Γ)))
                        ∷ update n′ (Dir (delete n (children (lookupSt n′ Γ)))) Γ)) ⊤
up {Γ = Γ} n′ n {{w}} {{p}} {{z}} {{f}} =
  step (castCmd refl
         (cong₂ (λ a b → Dir ((n , a) ∷ b))
            (trans (stateOf-at n D z′) (cong (λ s → lookupSt n (children s)) eX))
            (trans (set-at n′ Γ w (Dir (remove (member-at n D z′))))
                   (cong (λ d → update n′ (Dir d) Γ) (trans (remove-at n D z′) (cong (λ s → delete n (children s)) eX)))))
         (Raw.up x (subst IsDir (sym eX) p) (member-at n D z′) (¬member n Γ f))) done
  where
    x  = member-at n′ Γ w
    eX : stateOf x ≡ lookupSt n′ Γ
    eX = stateOf-at n′ Γ w
    D  = children (stateOf x)
    z′ : T (member n D)
    z′ = subst (λ s → T (member n (children s))) (sym eX) z

down : (n n′ : Name) {{z : T (member n Γ)}} {{w : T (member n′ (delete n Γ))}}
       {{p : IsDir (lookupSt n′ (delete n Γ))}} {{f : T (not (member n (children (lookupSt n′ (delete n Γ)))))}}
     → Prog Ψ (Dir Γ) (Dir (update n′ (Dir ((n , lookupSt n Γ) ∷ children (lookupSt n′ (delete n Γ)))) (delete n Γ))) ⊤
down {Γ = Γ} n n′ {{z}} {{w}} {{p}} {{f}} =
  step (castCmd refl
         (cong Dir (trans (set-at n′ Γ₁ w′ (Dir ((n , stateOf zp) ∷ children (stateOf xp))))
                          (cong₂ (λ d Γ′ → update n′ d Γ′)
                             (cong₂ (λ a b → Dir ((n , a) ∷ children b)) (stateOf-at n Γ z) eX)
                             (remove-at n Γ z))))
         (Raw.down zp xp (subst IsDir (sym eX) p) (¬member n (children (stateOf xp)) (subst (λ s → T (not (member n (children s)))) (sym eX) f)))) done
  where
    zp = member-at n Γ z
    Γ₁ = remove zp
    w′ : T (member n′ Γ₁)
    w′ = subst (λ Γ′ → T (member n′ Γ′)) (sym (remove-at n Γ z)) w
    xp = member-at n′ Γ₁ w′
    eX : stateOf xp ≡ lookupSt n′ (delete n Γ)
    eX = trans (stateOf-at n′ Γ₁ w′) (cong (lookupSt n′) (remove-at n Γ z))

-- 开岛：把目录 n 交出去。协议不用写——它由 Ψ 里那条叫 n 的假设决定（按名字判定）；
-- 假设要求的子树形状必须和 n 下面现在的一样（eq，由 ≡-inst 算）。
openAs : (n m : Name) {{w : T (member n Γ)}} {{p : IsDir (lookupSt n Γ)}}
         {{h : True (m ↦ₛ? Ψ)}} (i : idxOf (atₛ h))
         {{eq : ctxAt (atₛ h) i ≡ children (lookupSt n Γ)}}
       → Prog Ψ (Dir Γ) (Dir (update n (Chan (sessionAt (atₛ h) i)) Γ)) ⊤
openAs {Γ = Γ} n m {{w}} {{p}} {{h}} i {{eq}} =
  exec x (subst IsDir (sym eX) p) (atₛ h) i (trans eq (cong children (sym eX)))
    (subst (λ Γ′ → Prog _ (Dir (set x (Chan (sessionAt (atₛ h) i)))) (Dir Γ′) ⊤)
      (set-at n Γ w (Chan (sessionAt (atₛ h) i))) (done tt))
  where
    x = member-at n Γ w
    eX : stateOf x ≡ lookupSt n Γ
    eX = stateOf-at n Γ w

open′ : (n : Name) {{w : T (member n Γ)}} {{p : IsDir (lookupSt n Γ)}}
        {{h : True (n ↦ₛ? Ψ)}} {{i : idxOf (atₛ h)}}
        {{eq : ctxAt (atₛ h) i ≡ children (lookupSt n Γ)}}
      → Prog Ψ (Dir Γ) (Dir (update n (Chan (sessionAt (atₛ h) i)) Γ)) ⊤
open′ n {{w}} {{p}} {{h}} {{i}} {{eq}} = openAs n n {{w}} {{p}} {{h}} i {{eq}}

-- 信道的左规则，用户版。eq 由实例 ≡-inst 算出来：这一格现在的协议是什么，Agda 自己看。
recv : (c n : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan (Res r ⊗ S)}}
       {{f : T (not (member n Γ))}}
     → Prog Ψ (Dir Γ) (Dir ((n , r) ∷ update c (Chan S) Γ)) ⊤
recv {Γ = Γ} {r = r} c n {{w}} {{eq}} {{f}} =
  step (castCmd refl (cong (λ Γ′ → Dir ((n , r) ∷ Γ′)) (set-at c Γ w _))
         (Raw.recv (member-at c Γ w) (trans (stateOf-at c Γ w) eq) n (¬member n Γ f))) done

recvD : (c : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan (Dat A ⊗ S)}}
      → Prog Ψ (Dir Γ) (Dir (update c (Chan S) Γ)) A
recvD {Γ = Γ} c {{w}} {{eq}} =
  step (castCmd refl (cong Dir (set-at c Γ w _)) (Raw.recvD (member-at c Γ w) (trans (stateOf-at c Γ w) eq))) done

send : (n c : Name) {{z : T (member n Γ)}} {{w : T (member c (delete n Γ))}}
       {{eq : lookupSt c (delete n Γ) ≡ Chan (Res (lookupSt n Γ) ⊸ S)}}
     → Prog Ψ (Dir Γ) (Dir (update c (Chan S) (delete n Γ))) ⊤
send {Γ = Γ} {S = S} n c {{z}} {{w}} {{eq}} =
  step (castCmd refl (cong Dir (trans (set-at c Γ₁ w′ (Chan S)) (cong (update c (Chan S)) (remove-at n Γ z))))
         (Raw.send zp xp (trans eX (trans eq (cong (λ s → Chan (Res s ⊸ S)) (sym (stateOf-at n Γ z))))))) done
  where
    zp = member-at n Γ z
    Γ₁ = remove zp
    w′ : T (member c Γ₁)
    w′ = subst (λ Γ′ → T (member c Γ′)) (sym (remove-at n Γ z)) w
    xp = member-at c Γ₁ w′
    eX : stateOf xp ≡ lookupSt c (delete n Γ)
    eX = trans (stateOf-at c Γ₁ w′) (cong (lookupSt c) (remove-at n Γ z))

sendD : (c : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan (Dat A ⊸ S)}} → A
      → Prog Ψ (Dir Γ) (Dir (update c (Chan S) Γ)) ⊤
sendD {Γ = Γ} c {{w}} {{eq}} a =
  step (castCmd refl (cong Dir (set-at c Γ w _)) (Raw.sendD (member-at c Γ w) (trans (stateOf-at c Γ w) eq) a)) done

close : (c : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan End}}
      → Prog Ψ (Dir Γ) (Dir (delete c Γ)) ⊤
close {Γ = Γ} c {{w}} {{eq}} =
  step (castCmd refl (cong Dir (remove-at c Γ w)) (Raw.close (member-at c Γ w) (trans (stateOf-at c Γ w) eq))) done

recover : (c : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan (Res r ⊗ End)}}
        → Prog Ψ (Dir Γ) (Dir (update c r Γ)) ⊤
recover {Γ = Γ} c {{w}} {{eq}} =
  step (castCmd refl (cong Dir (set-at c Γ w _)) (Raw.recover (member-at c Γ w) (trans (stateOf-at c Γ w) eq))) done

call : (c : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan (SrvI Q R I F)}} → Q
     → Prog Ψ (Dir Γ) (Dir (update c (Chan (SrvI Q R I F)) Γ)) R
call {Γ = Γ} c {{w}} {{eq}} q =
  step (castCmd refl (cong Dir (set-at c Γ w _)) (Raw.call (member-at c Γ w) (trans (stateOf-at c Γ w) eq) q)) done

stop : (c : Name) {{w : T (member c Γ)}} {{eq : lookupSt c Γ ≡ Chan (Srv Q R s′)}}
     → Prog Ψ (Dir Γ) (Dir (update c s′ Γ)) ⊤
stop {Γ = Γ} c {{w}} {{eq}} =
  step (castCmd refl (cong Dir (set-at c Γ w _)) (Raw.stop (member-at c Γ w) (trans (stateOf-at c Γ w) eq))) done

-- 右规则的用户版：位置和新鲜性由名字层算出来
give : (n : Name) {{w : T (member n Γ)}} → Proc Ψ (delete n Γ) S → Proc Ψ Γ (Res (lookupSt n Γ) ⊗ S)
give {Γ = Γ} {S = S} n {{w}} k =
  subst (λ s → Proc _ Γ (Res s ⊗ S)) (stateOf-at n Γ w)
    (giveAt (member-at n Γ w) (subst (λ Γ′ → Proc _ Γ′ S) (sym (remove-at n Γ w)) k))

give∃ : (i : I) (n : Name) {{w : T (member n Γ)}} {{eq : lookupSt n Γ ≡ F i}}
      → Proc Ψ (delete n Γ) S → Proc Ψ Γ (∃Res I F ⊗ S)
give∃ {Γ = Γ} {S = S} i n {{w}} {{eq}} k =
  give∃At i (member-at n Γ w) (trans (stateOf-at n Γ w) eq)
    (subst (λ Γ′ → Proc _ Γ′ S) (sym (remove-at n Γ w)) k)

withEphemeral : (tmp : Name) {{fresh : T (not (member tmp Γ))}}
              → Prog Ψ (Dir []) (Dir []) A → Prog Ψ (Dir Γ) (Dir Γ) A
withEphemeral {Γ = Γ} tmp {{fresh}} p =
  step (Raw.mkdir tmp (¬member tmp Γ fresh)) λ _ →
  focus (here refl) p λ a → step (Raw.rmdir (here refl) tt) λ _ → done a

take : (n : Name) {{f : T (not (member n Γ))}} → Proc Ψ ((n , r) ∷ Γ) S → Proc Ψ Γ (Res r ⊸ S)
take {Γ = Γ} n {{f}} k = takeAt n (¬member n Γ f) k

------------------------------------------------------------------------
-- Rust 的 drop glue，在这里是一个可以证明的程序。
-- clear Γ 的类型说：无论目录里是多深的树，跑完以后目录是空的。
-- 顺序被 rmdir 的类型逼出来：只能先清空孩子，再删父亲。
--
-- 前提 Droppable：什么能被无条件丢掉？文件、目录（孩子都能丢），和"我不欠对面任何东西"的信道：
--   Chan End（关门）、Chan (Res r ⊗ End)（先收回再丢 r）、Chan (Srv …)（先 stop 再丢 s′）。
-- 话说到一半的信道不行：欠对面一个值（⊸）你变不出来；对面还要给你别的东西，你得先收。
-- 这是会话版的"父亲死前孩子必须先死"：关门前每根会话必须走到 End。
Droppable    : St  → Set
DroppableAll : Ctx → Set
Droppable (File _)                = ⊤
Droppable (Dir Γ)                 = DroppableAll Γ
Droppable (Chan End)              = ⊤
Droppable (Chan (Res r ⊗ End))    = Droppable r
Droppable (Chan (SrvI _ _ I F))   = (i : I) → Droppable (F i)
Droppable (Chan (_ ⊗ _))          = ⊥
Droppable (Chan (_ ⊸ _))          = ⊥
DroppableAll []                   = ⊤
DroppableAll ((_ , s) ∷ Γ)        = Droppable s × DroppableAll Γ

-- 同一个位置，在那一格换了状态之后仍然是同一个位置
again : (x : n ↦ Γ) → n ↦ set x s′
again (here px) = here px
again (there x) = there (again x)

stateOf-again : (x : n ↦ Γ) → stateOf (again {s′ = s′} x) ≡ s′
stateOf-again (here _)  = refl
stateOf-again (there x) = stateOf-again x

remove-again : (x : n ↦ Γ) → remove (again {s′ = s′} x) ≡ remove x
remove-again (here _)  = refl
remove-again (there x) = cong (_ ∷_) (remove-again x)

clear  : (Γ : Ctx) → DroppableAll Γ → Prog Ψ (Dir Γ) (Dir []) ⊤
dropAs : (x : n ↦ Γ) (s : St) → stateOf x ≡ s → Droppable s → Prog Ψ (Dir Γ) (Dir (remove x)) ⊤
clear []            _        = done tt
clear ((_ , s) ∷ Γ) (d , ds) = dropAs (here refl) s refl d >> clear Γ ds
dropAs x (File _) eq _ = step (Raw.unlink x (subst IsFile (sym eq) tt)) done
dropAs x (Dir Δ)  eq ds =
  focus x (subst (λ s → Prog _ s (Dir []) ⊤) (sym eq) (clear Δ ds))      -- 先清空孩子
    λ _ → step (subst (λ Γ′ → Cmd (Dir (set x (Dir []))) (Dir Γ′) ⊤)    -- 再删自己
                  (remove-again x)
                  (Raw.rmdir (again x) (subst IsEmptyDir (sym (stateOf-again x)) tt)))
               done
dropAs x (Chan End) eq _ = step (Raw.close x eq) done                      -- 说完了：关门
dropAs x (Chan (Res r ⊗ End)) eq d =                                       -- 岛会还我一棵 r：收回，再丢 r
  step (Raw.recover x eq)
    λ _ → subst (λ Γ′ → Prog _ (Dir (set x r)) (Dir Γ′) ⊤) (remove-again x)
            (dropAs (again x) r (stateOf-again x) d)
dropAs x (Chan (SrvI Q R I F)) eq d =
  stopI x eq λ i →
    subst (λ Γ′ → Prog _ (Dir (set x (F i))) (Dir Γ′) ⊤) (remove-again x)
      (dropAs (again x) (F i) (stateOf-again x) (d i))
dropAs x (Chan (Dat _ ⊗ _))         eq ()                                  -- 话没说完：写不出来
dropAs x (Chan (Res _ ⊗ (_ ⊗ _)))   eq ()
dropAs x (Chan (Res _ ⊗ (_ ⊸ _)))   eq ()
dropAs x (Chan (Res _ ⊗ SrvI _ _ _ _)) eq ()
dropAs x (Chan (∃Res _ _ ⊗ _)) eq ()
dropAs x (Chan (_ ⊸ _))             eq ()

-- 递归删除一个条目，无论它下面是多深的树。
deleteAll : (n : Name) {{w : T (member n Γ)}} {{d : Droppable (lookupSt n Γ)}}
          → Prog Ψ (Dir Γ) (Dir (delete n Γ)) ⊤
deleteAll {Γ = Γ} n {{w}} {{d}} =
  subst (λ Γ′ → Prog _ (Dir Γ) (Dir Γ′) ⊤) (remove-at n Γ w) (dropAs (member-at n Γ w) _ (stateOf-at n Γ w) d)

------------------------------------------------------------------------
-- 例子
------------------------------------------------------------------------

-- 例 1：持有与 drop glue。不同类型的文件住在同一个目录里。
-- 建一棵树，然后一句 deleteAll 把整棵子树删掉；脚本类型从空到空。不用任何外部接口：Ψ 任意。
nested : Prog Ψ (Dir []) (Dir []) ⊤
nested = do
  mkdir "d"
  inside "d" (do
    mkdir "sub"
    inside "sub" (create "x" 1)
    create "y" "two")
  deleteAll "d"            -- 此刻 "d" 下面是 Dir [("y", File String), ("sub", Dir [("x", File ℕ)])]

-- 例 2：借用 = inside。
-- 子脚本只认识交给它的那一棵子树。签名承诺：进来空目录，出去仍是空目录（原样归还）。
scratch : Prog Ψ (Dir []) (Dir []) String
scratch = do
  create "tmp" "scratch"
  d ← inside "tmp" read
  unlink "tmp"
  done d

-- 父脚本把子目录 "work" 借给 scratch。借出期间 "log" 在父目录里，scratch 碰不到它——
-- 不是因为有人检查，而是 scratch 的类型里根本没有 "log" 这一格。
borrowed : Prog Ψ (Dir []) (Dir []) String
borrowed = do
  create "log" ""
  mkdir "work"
  d ← inside "work" scratch
  rmdir "work"
  unlink "log"
  done d

-- 例 3：共享读 + 硬链接。
-- 读出的 d 是笛卡尔值（这里是一对数），两个读者共享；link 给同一份内容起第二个名字，
-- 删掉一个名字内容还在。
linked : Prog Ψ (Dir []) (Dir []) ℕ
linked = do
  create "a" (3 , 4)
  link "a" "b"
  unlink "a"
  d ← inside "b" read
  unlink "b"                                -- 名字全没了
  let (d₁ , d₂) = copy d                    -- 数据还在
  done (proj₁ d₁ + proj₂ d₂)

-- 例 4：搬运。f 从 src 升到当前目录，再降到 dst。每一步叶子数不变。
moved : Prog Ψ (Dir []) (Dir []) ⊤
moved = do
  mkdir "src"
  mkdir "dst"
  inside "src" (create "f" "x")
  up "src" "f"
  down "f" "dst"
  inside "dst" (unlink "f")
  rmdir "src"
  rmdir "dst"

-- 例 5：开岛——父亲不等的 cut。
-- 接口写在 Ψ 里，不在脚本里：名字 "w"，交出去的是空目录，对面兑现 WorkerS。
-- 对面是谁？脚本不知道。它只对"收到的东西符合 WorkerS"负责。
WorkerS : Session
WorkerS = Res (File ℕ) ⊸ Dat ℕ ⊗ Res (File ℕ) ⊗ End

-- 看 "w" 这一格的状态怎么一步步走完协议：
--   Dir [] ─open′──▶ Chan (Res (File ℕ) ⊸ Dat ℕ ⊗ Res (File ℕ) ⊗ End)
--          ─send───▶ Chan (Dat ℕ ⊗ Res (File ℕ) ⊗ End)
--          ─recvD──▶ Chan (Res (File ℕ) ⊗ End)
--          ─recv───▶ Chan End
--          ─close──▶ （格子消失）
delegated : Prog (mkSpec "w" [] WorkerS ∷ []) (Dir []) (Dir []) ℕ
delegated = do
  mkdir "w"
  open′ "w"                     -- "w" 交出去，剩一张收据
  create "f" 41
  send "f" "w"                  -- "f" 从我的清单里消失，进了信道：move
  v ← recvD "w"
  recv "w" "f"                  -- 回来了，我又叫它 "f"
  close "w"
  unlink "f"
  done (suc v)

-- 另一边：一个能兑现 WorkerS 的进程。它的类型就是它的协议：
-- 收一个 File ℕ，把值告诉对面，把文件还回去，结束。收进来的文件叫 "f"，是它自己起的名字。
-- 它自己不开岛，所以 Ψ = []。
worker : Proc [] [] WorkerS
worker = take "f" (run (inside "f" read) λ v → tell v (give "f" end))

-- 例 6：常驻服务 = 余归纳的岛。
-- 数据库：永远持有 "db"。请求 Maybe ℕ：nothing = 读，just v = 写；回答当前值。
-- stop 的时候把 "db" 这个文件本身交还给客户（所以 s′ = File ℕ）。
-- 写请求天然串行：服务手里有线性的 "db"，它没资格被复制（不能 !），只能是一根单线的循环（ν）。
DB : Ctx
DB = ("db" , File ℕ) ∷ []

DBS : Session
DBS = Srv (Maybe ℕ) ℕ (File ℕ)

dbServer : Server [] (Maybe ℕ) ℕ DB (File ℕ)
ServerI.call dbServer = ask λ where
  nothing  → run (inside "db" read)                      λ v → tell v (daemon dbServer)
  (just v) → run (unlink "db" >> create "db" v >> done v) λ v → tell v (daemon dbServer)
ServerI.stop dbServer = give∃ tt "db" end

system : Prog (mkSpec "srv" DB DBS ∷ []) (Dir []) (Dir []) ℕ
system = do
  mkdir "srv"
  inside "srv" (create "db" 0)
  open′ "srv"                    -- "srv" 这一格：Dir DB ──▶ Chan DBS。对面是谁，由环境决定。
  _ ← call "srv" (just 7)        -- 写
  a ← call "srv" nothing         -- 读
  stop "srv"                     -- 句柄变回 File ℕ：服务把 db 文件还给我
  unlink "srv"
  done a

-- 例 7：一个等着外界喂数的脚本。k 从哪里来、原来是什么字节，内核不管——那是 Main.agda 的事。
pipeline : ℕ → Prog (mkSpec "srv" DB DBS ∷ []) (Dir []) (Dir []) ℕ
pipeline k = do
  mkdir "srv"
  inside "srv" (create "db" 0)
  open′ "srv"
  _ ← call "srv" (just k)
  a ← call "srv" nothing
  stop "srv"
  unlink "srv"
  done (a + a)

-- 例 8：Harness 里的一次"打开 agent"。
-- 2 的家是一个目录（代码 + 测试）。父亲 1 要改 2 的规约：把 2 的家交出去（open′），把新规约
-- 当数据发过去（sendD），然后只能等——报告回来（recvD）、家回来（recover）。
-- 1 没法指挥 2 中途做什么：类型里没有那条命令。2 的程序由谁写？由环境（LLM）在那时候写。
Home : Ctx
Home = ("code" , File String) ∷ ("test" , File String) ∷ []

Agent : Ctx → Session
Agent home = Dat String ⊸ Dat String ⊗ Res (Dir home) ⊗ End

wake : Prog (mkSpec "2" Home (Agent Home) ∷ []) (Dir (("2" , Dir Home) ∷ [])) (Dir (("2" , Dir Home) ∷ [])) String
wake = do
  open′ "2"                      -- 2.agent open：格子变成 Chan，1 进不去了
  sendD "2" "new spec"
  report ← recvD "2"             -- 没信就不醒；信到了才有下一段
  recover "2"                    -- 2.agent close：格子变回 Dir Home，里面是新代码
  done report

-- 一个最笨的 agent 模拟（root.test 用）：照抄规约当代码，打包回家，汇报 "ok"。
-- 真实的 2.agent 在这里会调 LLM、跑 agda——那些都在它自己的 Ψ 里，与 1 无关。
mockAgent : Proc [] Home (Agent Home)
mockAgent = ask λ spec →
  run (do unlink "code"; create "code" spec
          mkdir "home"; down "test" "home"; down "code" "home")
      λ _ → tell "ok" (give "home" end)

-- 写不出来的脚本（取消注释会得到类型错误）：
--
-- leak : Prog Ψ (Dir []) (Dir []) ⊤
-- leak = create "e" 0
--   -- 终点是 Dir [("e", File ℕ)] 而不是 Dir []：资源泄漏被拒绝。
--
-- rmFull : Prog Ψ (Dir []) (Dir []) ⊤
-- rmFull = do mkdir "d"; inside "d" (create "x" 0); rmdir "d"
--   -- rmdir 的前提 IsEmptyDir 算成 ⊥：父亲还有孩子，不能死。
--
-- reachOut : Prog Ψ (Dir []) (Dir []) String
-- reachOut = do
--   create "log" ""
--   mkdir "work"
--   d ← inside "work" (inside "log" read)
--   rmdir "work"
--   unlink "log"
--   done d
--   -- 借到 "work" 的子脚本想读父目录里的 "log"：
--   -- 它的上下文是 Dir []，里面根本没有 "log" 这一格，位置算不出来。
--
-- linkDir : Prog Ψ (Dir []) (Dir []) ⊤
-- linkDir = do mkdir "d"; link "d" "e"; ...
--   -- link 的前提 IsFile 算成 ⊥：不能给目录起别名，名字层必须是树。
--
-- unlisted : Prog [] (Dir []) (Dir []) ⊤
-- unlisted = do mkdir "w"; open′ "w"; ...
--   -- Ψ 是空的：没有任何假设说 "w" 对面有人。想开岛，先把接口写进清单。
--
-- early : Prog (mkSpec "w" [] WorkerS ∷ []) (Dir []) (Dir []) ⊤
-- early = do mkdir "w"; open′ "w"; create "f" 41; send "f" "w"; close "w"
--   -- close 的前提 stateOf c ≡ Chan End 不成立：协议还没走完（对面还欠我一个 ℕ 和一个文件）。
--
-- dropMid : Prog (mkSpec "w" [] WorkerS ∷ []) (Dir []) (Dir []) ⊤
-- dropMid = do mkdir "w"; open′ "w"; create "f" 41; send "f" "w"; deleteAll "w"
--   -- Droppable (Chan (Dat ℕ ⊗ …)) 算成 ⊥：想丢掉一根信道，先把话说完。
--
-- peek : Prog (mkSpec "2" Home (Agent Home) ∷ []) (Dir (("2" , Dir Home) ∷ [])) _ String
-- peek = do open′ "2"; inside "2" (inside "code" read)
--   -- 交出去以后 "2" 是 Chan，不是 Dir：盒子不透明，focus 进不去。想要东西，走信道。
--
-- steal : Proc Ψ [] (Res (File ℕ) ⊸ End)
-- steal = take "f" end
--   -- end 要求手里是 []，但 "f" 还在：收来的资源不能悄悄扔掉。
--   -- 要么 give 回去，要么老老实实 run (unlink "f") 之后再 end——收到的东西归你，但你得交代它的去向。

------------------------------------------------------------------------
-- §4  纯模型与定理
------------------------------------------------------------------------

-- 类型层是名字树；模型层是树上每片叶子里装的东西。
--   File A 的模型   ：一个 A。
--   Dir Γ 的模型    ：孩子们的模型。
--   Chan S 的模型   ：对面那个进程剩下的行为（Offer S）。
--     对面要交出 t（⊗）：模型里就有一个 t 等着我拿；
--     对面要收进 t（⊸）：模型是一个函数，喂它一个 t；
--     对面是常驻服务   ：模型是一个余归纳的 Running，问多少次都行。
--   这就是 cut 在模型里的样子：一根信道的两端，一端是"我手里的收据"，另一端"是对面整个进程"。
--   纯模型里 Offer 是一个值；现实里它是一个正在跑的进程、一次 LLM 调用、一个人。

-- 两个字段就是 & 的两个分支：
--   onCall ：喂一个 Q，得到一个 R 和下一轮的服务   （= Offer (Dat Q ⊸ Dat R ⊗ Srv …)，见下）
--   onStop ：得到交还的那棵 s′ 的模型
record Running (Q R M′ : Set) : Set where
  coinductive
  field
    onCall : Q → R × Running Q R M′
    onStop : M′

Model  : St      → Set
Models : Ctx     → Set
Msg    : Ty      → Set
Offer  : Session → Set

Model (File A) = A
Model (Dir Γ)  = Models Γ
Model (Chan S) = Offer S

Models []            = ⊤
Models ((_ , s) ∷ Γ) = Model s × Models Γ

Msg (Res s) = Model s
Msg (Dat A) = A
Msg (∃Res I F) = Σ I (λ i → Model (F i))

Offer End          = ⊤
Offer (t ⊗ S)      = Msg t × Offer S
Offer (t ⊸ S)      = Msg t → Offer S
Offer (SrvI Q R I F) = Running Q R (Σ I (λ i → Model (F i)))

-- 一条假设的意义：给它这棵子树的模型，它给我一个 Offer。
-- 一张清单的意义：每条假设各给一个——这就是环境。root.test 里它是模拟接口；现实里 IO 层负责兑现。
⟦_⟧ : Spec → Set
⟦ specI _ I Γ S ⟧ = (i : I) → Models (Γ i) → Offer (S i)

Env : List Spec → Set₁
Env Ψ = All ⟦_⟧ Ψ

-- 按名字在环境里取那条假设的兑现者
lookupₛ : Env Ψ → (h : n ↦ₛ Ψ) → (i : idxOf h) → Models (ctxAt h i) → Offer (sessionAt h i)
lookupₛ (e ∷ _)  (here _)  = e
lookupₛ (_ ∷ es) (there h) = lookupₛ es h

-- 沿着位置证明在模型树上取 / 放 / 删
getAt : (x : n ↦ Γ) → Models Γ → Model (stateOf x)
getAt (here _)  (m , _)  = m
getAt (there x) (_ , ms) = getAt x ms

putAt : (x : n ↦ Γ) → Models Γ → Model s′ → Models (set x s′)
putAt (here _)  (_ , ms) m′ = m′ , ms
putAt (there x) (m , ms) m′ = m  , putAt x ms m′

delAt : (x : n ↦ Γ) → Models Γ → Models (remove x)
delAt (here _)  (_ , ms) = ms
delAt (there x) (m , ms) = m , delAt x ms

dirModel : (s : St) → IsDir s → Model s → Models (children s)
dirModel (Dir _) _ ms = ms

permuteModels : Γ Perm.↭ Δ → Models Γ → Models Δ
permuteModels Perm.refl m = m
permuteModels (Perm.prep _ p) (m , ms) = m , permuteModels p ms
permuteModels (Perm.swap _ _ p) (a , b , ms) = b , a , permuteModels p ms
permuteModels (Perm.trans p q) ms = permuteModels q (permuteModels p ms)

-- 每条命令的意义。
evalᶜ : Cmd s s′ A → Model s → Model s′ × A
evalᶜ (Raw.reorder p) M = permuteModels p M , tt
evalᶜ Raw.read             a = a , a                              -- read 就是 copy
evalᶜ (Raw.create n _ a)   M = (a , M) , tt
evalᶜ (Raw.unlink x _)     M = delAt x M , tt
evalᶜ (Raw.mkdir n _)      M = (tt , M) , tt
evalᶜ (Raw.rmdir x _)      M = delAt x M , tt
evalᶜ (Raw.link x _ _ _)   M = (getAt x M , M) , tt                -- 新名字绑的就是旧名字的那个值
evalᶜ (Raw.up x p z _)     M = let MΔ = dirModel _ p (getAt x M)
                               in  (getAt z MΔ , putAt x M (delAt z MΔ)) , tt
evalᶜ (Raw.down z x p _)   M = let M′ = delAt z M
                                   MΔ = dirModel _ p (getAt x M′)
                               in  putAt x M′ (getAt z M , MΔ) , tt
evalᶜ (Raw.recv c eq n _)  M = let (m , k) = subst Model eq (getAt c M)        -- 对面已经把子树放在那了
                               in  (m , putAt c M k) , tt
evalᶜ (Raw.recvD c eq)     M = let (a , k) = subst Model eq (getAt c M)
                               in  putAt c M k , a
evalᶜ (Raw.send z c eq)    M = let M′ = delAt z M                                -- 把子树喂给对面
                               in  putAt c M′ (subst Model eq (getAt c M′) (getAt z M)) , tt
evalᶜ (Raw.sendD c eq a)   M = putAt c M (subst Model eq (getAt c M) a) , tt
evalᶜ (Raw.close c _)      M = delAt c M , tt
evalᶜ (Raw.recover c eq)   M = putAt c M (proj₁ (subst Model eq (getAt c M))) , tt   -- 收据变回子树
evalᶜ (Raw.call c eq q)    M = let (r , k) = Running.onCall (subst Model eq (getAt c M)) q
                               in  putAt c M k , r
evalᶜ (Raw.stop c eq)      M = putAt c M (proj₂ (Running.onStop (subst Model eq (getAt c M)))) , tt

-- 脚本的意义：模型上的状态变换，多一个参数——环境。
-- exec 那一行就是开放的 cut：向环境要来对面的行为（一个 Offer S），放进那一格。
-- eval 不钻进任何孩子：孩子的程序不在这里，所以也没有什么需要终止。
eval : Env Ψ → Prog Ψ s s′ A → Model s → Model s′ × A
eval env (done a)       M = M , a
eval env (step c κ)     M = let (M′ , a) = evalᶜ c M in eval env (κ a) M′
eval env (focus x p κ)  M = let (M′ , a) = eval env p (getAt x M) in eval env (κ a) (putAt x M M′)  -- 一个 lens
eval env (exec z p h i e κ) M =                                                                      -- 开放的 cut
  eval env κ (putAt z M (lookupₛ env h i (subst Models (sym e) (dirModel _ p (getAt z M)))))

eval env (stopI c e κ) M = let (i , m) = Running.onStop (subst Model e (getAt c M))
                            in eval env (κ i) (putAt c M m)

-- 岛的意义：把一个 Proc 变成"对面看到的行为"——这就是 Chan S 的模型，也就是兑现一条假设的东西。
-- 这是链接：root.test 里用它把模拟接口接上去；现实里 IO 层在岛启动时做同一件事。
--   provide ：一般情形
--   stopOf  ：provide 在 stop 分支上的特例（那种进程只会 give 一格然后 end），直接算出交还的树
--   running ：把服务连同它的家当一起展开成一个余归纳的 Running
-- 三者互递归，唯一的圈是 running → provide → daemon → running：被 copattern 护着，合法的生产力递归。
provide : Env Ψ → Proc Ψ Γ S → Models Γ → Offer S
stopOf  : Env Ψ → Proc Ψ Γ (∃Res I F ⊗ End) → Models Γ → Σ I (λ i → Model (F i))
running : Env Ψ → ServerI Ψ Q R I Γ F → Models Γ → Running Q R (Σ I (λ i → Model (F i)))

machineRunning : {J : Set} {G : J → Ctx} → Env Ψ
               → ((j : J) → Proc Ψ (G j) (Dat Q ⊸ Dat R ⊗ ∃Res J (λ j′ → Dir (G j′)) ⊗ End))
               → ((j : J) → Proc Ψ (G j) (∃Res I F ⊗ End))
               → (j : J) → Models (G j) → Running Q R (Σ I (λ i → Model (F i)))

provide env (run p k)      M = let (M′ , a) = eval env p M in provide env (k a) M′
provide env end            _ = tt
provide env (giveAt x k)   M = getAt x M , provide env k (delAt x M)
provide env (tell a k)     M = a , provide env k M
provide env (takeAt n _ k) M = λ m → provide env k (m , M)
provide env (ask k)        M = λ a → provide env (k a) M
provide env (daemon srv)   M = running env srv M
provide env (machine turn halt j) M = machineRunning env turn halt j M
provide env (give∃Dir i e) M = (i , subst Model e M) , tt
provide env (give∃At i x e k) M = (i , subst Model e (getAt x M)) , provide env k (delAt x M)
provide env (stopP c e k) M = let (i , m) = Running.onStop (subst Model e (getAt c M))
                            in provide env (k i) (putAt c M m)

stopOf env (run p k)    M = let (M′ , a) = eval env p M in stopOf env (k a) M′
stopOf env (give∃Dir i e) M = i , subst Model e M
stopOf env (give∃At i x e _) M = i , subst Model e (getAt x M)
stopOf env (stopP c e k) M = let (i , m) = Running.onStop (subst Model e (getAt c M))
                           in stopOf env (k i) (putAt c M m)

Running.onCall (running env srv M) = provide env (ServerI.call srv) M
Running.onStop (running env srv M) = stopOf  env (ServerI.stop srv) M

machineCall : {J : Set} {G : J → Ctx} → Env Ψ
            → Proc Ψ Γ (Dat Q ⊸ Dat R ⊗ ∃Res J (λ j → Dir (G j)) ⊗ End)
            → Models Γ → Q → R × Σ J (λ j → Models (G j))
machineAnswer : {J : Set} {G : J → Ctx} → Env Ψ
              → Proc Ψ Γ (Dat R ⊗ ∃Res J (λ j → Dir (G j)) ⊗ End)
              → Models Γ → R × Σ J (λ j → Models (G j))
machineCall env (ask k) M q = machineAnswer env (k q) M
machineCall env (run p k) M q = let (M′ , a) = eval env p M in machineCall env (k a) M′ q
machineCall env (stopP c e k) M q = let (i , m) = Running.onStop (subst Model e (getAt c M))
                                  in machineCall env (k i) (putAt c M m) q
machineAnswer env (tell r k) M = r , stopOf env k M
machineAnswer env (run p k) M = let (M′ , a) = eval env p M in machineAnswer env (k a) M′
machineAnswer env (stopP c e k) M = let (i , m) = Running.onStop (subst Model e (getAt c M))
                                  in machineAnswer env (k i) (putAt c M m)

Running.onCall (machineRunning env turn halt j M) q =
  let (r , j′ , M′) = machineCall env (turn j) M q
  in r , machineRunning env turn halt j′ M′
Running.onStop (machineRunning env turn halt j M) = stopOf env (halt j) M

-- 定理 (get-get)：读两次 = 读一次再复制。"快照合法"的形式依据，也是不可变世界里
-- lens 三律中唯一剩下的一条。对任何内容类型 A、任何环境成立。
twice once : Prog Ψ (File A) (File A) (A × A)
twice = step Raw.read λ a₁ → step Raw.read λ a₂ → done (a₁ , a₂)
once  = step Raw.read λ a → done (copy a)

get-get : (env : Env Ψ) (a : A) → eval env twice a ≡ eval env once a
get-get env a = refl

-- 定理 (link)：硬链接之后，新名字绑定的就是旧名字的那个值。
-- 模型是纯的，看不出"一份"还是"两份"——那是表示层（存储）的事；类型层能说的只有"相等"。
link-shares : (x : n ↦ Γ) (p : IsFile (stateOf x)) (f : ¬ (n′ ↦ Γ)) (M : Models Γ)
            → proj₁ (proj₁ (evalᶜ (Raw.link x p n′ f) M)) ≡ getAt x M
link-shares x p f M = refl

-- 链接引理：把环境取成某个具体的岛（provide q），脚本和岛接上以后的行为是什么。
-- 封闭世界里这些叫 cut 消去；开放世界里它们是"对一个特定环境的陈述"——内容一样，refl 一样。

-- (数据)：岛只说一句话就结束；父亲收下那句话，关门。等于 rmdir 以后直接拿那个值往下走。通信 = 代换。
link-data : (a : A) (κ : A → Prog (mkSpec n [] (Dat A ⊗ End) ∷ []) (Dir Γ) s″ B)
            (M : Models ((n , Dir []) ∷ Γ))
  → eval {s = Dir ((n , Dir []) ∷ Γ)} ((λ _ → provide [] (tell a end)) ∷ [])
         (exec (here refl) tt (here refl) tt refl
            (step (Raw.recvD (here refl) refl) λ x →
             step (Raw.close (here refl) refl) λ _ → κ x)) M
  ≡ eval {s = Dir ((n , Dir []) ∷ Γ)} ((λ _ → provide [] (tell a end)) ∷ [])
         (step (Raw.rmdir (here refl) tt) λ _ → κ a) M
link-data a κ M = refl

-- (资源)：岛收下一格再原样交回；父亲发过去再收回来。等于什么都没发生（只多了一次 rmdir）。
-- 通信 = 搬运，叶子一个不多一个不少。
echo : Proc Ψ [] (Res r ⊸ Res r ⊗ End)
echo = takeAt "x" (λ ()) (giveAt (here refl) end)

link-res : {m : Name} (κ : Prog (mkSpec n [] (Res r ⊸ Res r ⊗ End) ∷ []) (Dir ((m , r) ∷ Γ)) s″ B)
           (f : ¬ (m ↦ ((n , Chan (Res r ⊗ End)) ∷ Γ)))
           (M : Models ((m , r) ∷ (n , Dir []) ∷ Γ))
  → eval {s = Dir ((m , r) ∷ (n , Dir []) ∷ Γ)} ((λ _ → provide [] (echo {r = r})) ∷ [])
         (exec (there (here refl)) tt (here refl) tt refl
            (step (Raw.send (here refl) (here refl) refl) λ _ →
             step (Raw.recv (here refl) refl m f) λ _ →
             step (Raw.close (there (here refl)) refl) λ _ → κ)) M
  ≡ eval {s = Dir ((m , r) ∷ (n , Dir []) ∷ Γ)} ((λ _ → provide [] (echo {r = r})) ∷ [])
         (step (Raw.rmdir (there (here refl)) tt) λ _ → κ) M
link-res κ f M = refl

-- (服务)：开门就关门 = 直接跑服务的 stop 分支，拿回它交还的东西。
link-stop : (srv : Server [] Q R Δ s′) (κ : Prog (mkSpec n Δ (Srv Q R s′) ∷ []) (Dir ((n , s′) ∷ Γ)) s″ B)
            (M : Models ((n , Dir Δ) ∷ Γ))
  → eval {s = Dir ((n , Dir Δ) ∷ Γ)} ((λ _ → provide [] (daemon srv)) ∷ [])
         (exec (here refl) tt (here refl) tt refl (step (Raw.stop (here refl) refl) λ _ → κ)) M
  ≡ eval ((λ _ → provide [] (daemon srv)) ∷ []) κ (proj₂ (stopOf [] (ServerI.stop srv) (proj₁ M)) , proj₂ M)
link-stop srv κ M = refl

-- root.test 长什么样：把模拟接口接上，跑纯模型，看结果。Agda 算给你看：
_ : eval ((λ _ → provide [] worker) ∷ []) delegated tt ≡ (tt , 42)
_ = refl

_ : eval ((λ _ → provide [] (daemon dbServer)) ∷ []) system tt ≡ (tt , 7)
_ = refl

_ : eval ((λ _ → provide [] mockAgent) ∷ []) wake (("old code" , "the test" , tt) , tt)
  ≡ ((("new spec" , "the test" , tt) , tt) , "ok")          -- 家回来了，代码换了，测试没动
_ = refl

-- "父亲死前孩子必须全死"不是定理，是 rmdir 的类型；
-- "关门前会话必须走完"不是定理，是 close 的类型；
-- "整棵树最终全部释放"不是定理，是 clear 的类型；
-- "整个系统会不会停"不是内核的事：对面坐着人和 LLM。

------------------------------------------------------------------------
-- 对照表
------------------------------------------------------------------------
--
--   Rust / 线性逻辑 / shell            这里
--   ────────────────────────────────────────────────────────────────────────
--   !A（可复制的东西）                 A : Set。File A 的内容；信道上的 Dat A
--   线性资源                           St：File / Dir / Chan，树上的一格
--   struct Dir { entries: Vec<File> }  Dir Γ：孩子的状态嵌在父亲的状态里
--   一个 .sh 文件                      Prog Ψ s s′ A：一段有限的、类型检查过的脚本
--   内建命令 / 系统调用 / 工具注册表    Cmd 的构造子，外加 exec
--   shell 解释器                       IO 层（Main.agda）
--   dry-run                            eval env：纯模型，root.test 跑在这里
--   (cd d && …)                        inside "d" p：聚焦一格，其余格子原样穿过（id_Γ ⊗ p）
--   借用期间不能动 dir                 focus 的类型里 Γ 两边相同：其余孩子正在那根线上
--   cmd & / thread::spawn              open′ "w"：目录变信道，父亲接着跑；对面是谁由环境定
--   wait / JoinHandle<T>               recvD / recover：等的是有类型的结果和子树
--   Send trait / delegation            send "f" "w"：子树进信道；recv "w" "f"：子树出信道
--   相继式 Γ ⊢ S                       Proc Ψ Γ S；一条 Spec 也是一个相继式，只是还没证
--   A.test × B.test × root ⊢ root.test root : Prog Ψ …，Ψ 里是 A、B 的接口；root.test = eval 配模拟
--   S 的右规则                         Proc 的构造子：giveAt tell takeAt ask end daemon
--   S 的左规则                         Cmd 的信道命令：recv recvD send sendD close recover call stop
--   cut（公理在左）                     step
--   cut（证明在左，父亲等）             focus
--   cut（左边是个洞，父亲不等）         exec；洞由环境填：eval 的 env / IO 层
--   ν（最大不动点）                     Server：余归纳记录，每步有限
--   ! 的 promotion 不许                 Server 手里有线性的 Γ：不能复制，只能是单线循环
--   dir.entries.remove(i) / mv         up / down：从一棵子树搬到另一棵，叶子数不变
--   drop(dir) 自动递归                 clear / deleteAll：手写的、类型保证正确的递归程序
--   drop 顺序固定、不检查              顺序被 rmdir / close 的类型逼出来
--   Rc<T> / Arc<T>                     link：命令版的 δ；内容一份是存储层的事
--   drop(Rc)                           unlink：命令版的 ε
--   &T（共享读）                       read 给的是值，之后随便复制（结构 δ，免费）
--   mem::forget（安全）                必须改签名承认泄漏
--   Rc 成环泄漏                        不可能：名字层是树（link 不接受目录），数据是归纳类型
--   整个系统是否终止                   不在内核里：孩子的程序不在父亲的项里
--   字节 ↔ 类型化的值                   不在内核里。Main.agda

-- Return an entire owned directory as an existential resource. This is the
-- directory form of give∃: every entry leaves the provider together.
-- give∃Dir consumes the whole context; it cannot retain any of its entries.
