------------------------------------------------------------------------
-- OwnershipIO.agda —— Prog 的 IO 解释器
--
-- Ownership.agda 的 eval 把脚本跑在纯模型上：树上每片叶子是一个值，每个 Chan 格子是"对面整个进程"的一个纯函数。
-- 这里是同一个解释器的 IO 版本，形状一样，差三处：
--
--   1. Chan 格子后面接真东西。OfferIO 里的每一步是一个 IO 动作：对面要交出 t，我就等（IO）；
--      对面要收 t，我就喂（IO）。常驻服务是一个带隐藏状态的句柄 RunningIO：问一次答一次（IO）。
--      隐藏状态住在 IORef 里——这正是真实服务（LLM、编译器、别的 agent）的样子：Q → IO R，状态在它自己那边。
--   2. 环境 EnvIO：每条假设给一个 IO 的兑现者。纯的 Env 可以提升成 EnvIO（liftEnv），
--      所以 root.test 里的模拟接口在 IO 里照样能用——这也是 T1 测的"纯 = IO"。
--   3. Dir / File 对应真目录 / 真文件：store / load。要存盘的树不能有没走完的会话（Codecs (Chan _) = ⊥）。
--
-- 内核不动：Prog、Cmd、Proc、Server 全是 Ownership.agda 的。这里只是另一个解释。
-- 用的是 IO.Primitive（真正的 Haskell IO）：层级保持、bind 跨层级，不会随会话长度抬高宇宙层级。
------------------------------------------------------------------------
{-# OPTIONS --guardedness #-}
module OwnershipIO where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import IO.Primitive as Prim
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import IO.Primitive.Finite as PF

open import Ownership hiding (_>>=_; _>>_; machineCall; machineAnswer)
open Ownership.Raw using (Cmd)
open import Data.Sum using (inj₁; inj₂)
open import OwnershipIO.FFI

private
  infixl 1 _>>=_ _>>_
  _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → (A → Prim.IO B) → Prim.IO B
  _>>=_ = Prim._>>=_
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → Prim.IO B → Prim.IO B
  m >> k = m >>= λ _ → k
  return : ∀ {a} {A : Set a} → A → Prim.IO A
  return = Prim.return

------------------------------------------------------------------------
-- §1  IO 侧的模型
--   Model (Chan S) = Offer S 是对面进程剩下的行为（纯函数）；
--   ModelIO (Chan S) = OfferIO S 是对面进程的句柄（每一步 IO）。别的叶子和纯模型一样。
------------------------------------------------------------------------

-- 常驻服务的句柄：问一次答一次；关门交还一棵子树。状态藏在句柄后面（IORef）。
record RunningIO (Q R M′ : Set) : Set where
  field
    onCall : Q → Prim.IO R
    onStop : Prim.IO M′
open RunningIO public

ModelIO  : St → Set
ModelsIO : Ctx → Set
MsgIO    : Ty → Set
OfferIO  : Session → Set

ModelIO (File A) = A
ModelIO (Dir Γ)  = ModelsIO Γ
ModelIO (Chan S) = OfferIO S

ModelsIO []            = ⊤
ModelsIO ((_ , s) ∷ Γ) = ModelIO s × ModelsIO Γ

MsgIO (Res s) = ModelIO s
MsgIO (Dat A) = A
MsgIO (∃Res I F) = Σ I (λ i → ModelIO (F i))

OfferIO End          = ⊤
OfferIO (t ⊗ S)      = Prim.IO (MsgIO t × OfferIO S)        -- 对面要交出 t：等它
OfferIO (t ⊸ S)      = MsgIO t → Prim.IO (OfferIO S)        -- 对面要收 t：喂它
OfferIO (SrvI Q R I F) = RunningIO Q R (Σ I (λ i → ModelIO (F i)))           -- 常驻服务：句柄

-- 一条假设在 IO 里的意义：给它这棵子树（的 IO 模型），它开一个进程，交出句柄
⟦_⟧IO : Spec → Set
⟦ specI _ I Γ S ⟧IO = (i : I) → ModelsIO (Γ i) → Prim.IO (OfferIO (S i))

EnvIO : List Spec → Set₁
EnvIO Ψ = All ⟦_⟧IO Ψ

lookupₛIO : ∀ {n Ψ} → EnvIO Ψ → (h : n ↦ₛ Ψ) → (i : idxOf h) → ModelsIO (ctxAt h i) → Prim.IO (OfferIO (sessionAt h i))
lookupₛIO (e ∷ _)  (here _)  = e
lookupₛIO (_ ∷ es) (there h) = lookupₛIO es h

-- 沿位置证明在 IO 模型树上取 / 放 / 删（和 Ownership 的 getAt/putAt/delAt 一字不差，换了个家族）
getAtIO : ∀ {n Γ} (x : n ↦ Γ) → ModelsIO Γ → ModelIO (stateOf x)
getAtIO (here _)  (m , _)  = m
getAtIO (there x) (_ , ms) = getAtIO x ms

putAtIO : ∀ {n Γ s′} (x : n ↦ Γ) → ModelsIO Γ → ModelIO s′ → ModelsIO (set x s′)
putAtIO (here _)  (_ , ms) m′ = m′ , ms
putAtIO (there x) (m , ms) m′ = m  , putAtIO x ms m′

delAtIO : ∀ {n Γ} (x : n ↦ Γ) → ModelsIO Γ → ModelsIO (remove x)
delAtIO (here _)  (_ , ms) = ms
delAtIO (there x) (m , ms) = m , delAtIO x ms

dirModelIO : (s : St) → IsDir s → ModelIO s → ModelsIO (children s)
dirModelIO (Dir _) _ ms = ms

------------------------------------------------------------------------
-- §2  每条命令的意义（IO）
--   目录命令：和纯模型一样，不碰 IO
--   信道命令：跑对面句柄里的那一步
------------------------------------------------------------------------

permuteModelsIO : ∀ {Γ Δ} → Γ Perm.↭ Δ → ModelsIO Γ → ModelsIO Δ
permuteModelsIO Perm.refl m = m
permuteModelsIO (Perm.prep _ p) (m , ms) = m , permuteModelsIO p ms
permuteModelsIO (Perm.swap _ _ p) (a , b , ms) = b , a , permuteModelsIO p ms
permuteModelsIO (Perm.trans p q) ms = permuteModelsIO q (permuteModelsIO p ms)

evalIOᶜ : ∀ {s s′ A} → Cmd s s′ A → ModelIO s → Prim.IO (ModelIO s′ × A)
evalIOᶜ (Raw.reorder p) M = return (permuteModelsIO p M , tt)
evalIOᶜ Raw.read             a = return (a , a)
evalIOᶜ (Raw.create n _ a)   M = return ((a , M) , tt)
evalIOᶜ (Raw.unlink x _)     M = return (delAtIO x M , tt)
evalIOᶜ (Raw.mkdir n _)      M = return ((tt , M) , tt)
evalIOᶜ (Raw.rmdir x _)      M = return (delAtIO x M , tt)
evalIOᶜ (Raw.link x _ _ _)   M = return ((getAtIO x M , M) , tt)
evalIOᶜ (Raw.up x p z _)     M = let MΔ = dirModelIO _ p (getAtIO x M)
                                 in return ((getAtIO z MΔ , putAtIO x M (delAtIO z MΔ)) , tt)
evalIOᶜ (Raw.down z x p _)   M = let M′ = delAtIO z M
                                     MΔ = dirModelIO _ p (getAtIO x M′)
                                 in return (putAtIO x M′ (getAtIO z M , MΔ) , tt)
evalIOᶜ (Raw.recv c eq n _)  M = subst ModelIO eq (getAtIO c M) >>= λ { (m , k) → return ((m , putAtIO c M k) , tt) }     -- 等对面把子树交出来
evalIOᶜ (Raw.recvD c eq)     M = subst ModelIO eq (getAtIO c M) >>= λ { (a , k) → return (putAtIO c M k , a) }           -- 等一个值
evalIOᶜ (Raw.send z c eq)    M = let M′ = delAtIO z M                                                                     -- 把子树喂给对面
                                 in subst ModelIO eq (getAtIO c M′) (getAtIO z M) >>= λ k → return (putAtIO c M′ k , tt)
evalIOᶜ (Raw.sendD c eq a)   M = subst ModelIO eq (getAtIO c M) a >>= λ k → return (putAtIO c M k , tt)                  -- 喂一个值
evalIOᶜ (Raw.close c _)      M = return (delAtIO c M , tt)
evalIOᶜ (Raw.recover c eq)   M = subst ModelIO eq (getAtIO c M) >>= λ { (m , _) → return (putAtIO c M m , tt) }           -- 收据变回子树
evalIOᶜ (Raw.call c eq q)    M = let h = subst ModelIO eq (getAtIO c M)                                                   -- 问服务一次；句柄不变
                                 in onCall h q >>= λ r → return (putAtIO c M h , r)
evalIOᶜ (Raw.stop c eq)      M = onStop (subst ModelIO eq (getAtIO c M)) >>= λ m′ → return (putAtIO c M (proj₂ m′) , tt)        -- 关门，拿回子树

------------------------------------------------------------------------
-- §3  脚本的意义（IO）。和 eval 一字不差，只是在 IO 里
------------------------------------------------------------------------

evalIO : ∀ {Ψ s s′ A} → EnvIO Ψ → Prog Ψ s s′ A → ModelIO s → Prim.IO (ModelIO s′ × A)
evalIO env (done a)         M = return (M , a)
evalIO env (step c κ)       M = evalIOᶜ c M >>= λ { (M′ , a) → evalIO env (κ a) M′ }
evalIO env (focus x p κ)    M = evalIO env p (getAtIO x M) >>= λ { (M′ , a) → evalIO env (κ a) (putAtIO x M M′) }
evalIO env (exec z p h i e κ) M =                                                              -- 开放的 cut：向环境要句柄
  lookupₛIO env h i (subst ModelsIO (sym e) (dirModelIO _ p (getAtIO z M))) >>= λ off → evalIO env κ (putAtIO z M off)

evalIO env (stopI c e κ) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → evalIO env (κ i) (putAtIO c M m) }

------------------------------------------------------------------------
-- §4  岛的意义（IO）：把一个 Proc 变成对面看得见的句柄
--   和纯模型的 provide 一样，除了 daemon：常驻服务不再是余归纳的值，而是一个 IORef 后面的状态机。
--   状态 = (家当的形状 , 当前的 Server , 它的家当)。每 call 一次：跑一轮 Server.call，把新状态写回去。
------------------------------------------------------------------------

-- 一个常驻服务此刻的状态
SrvState : List Spec → Set → Set → (I : Set) → (I → St) → Set₁
SrvState Ψ Q R I F = Σ Ctx (λ Γ → Proc Ψ Γ (SrvI Q R I F) × ModelsIO Γ)

callOnce : ∀ {Ψ Γ Q R I F} → EnvIO Ψ → Proc Ψ Γ (Dat Q ⊸ Dat R ⊗ SrvI Q R I F)
         → ModelsIO Γ → Q → Prim.IO (R × SrvState Ψ Q R I F)
answer : ∀ {Ψ Γ Q R I F} → EnvIO Ψ → Proc Ψ Γ (Dat R ⊗ SrvI Q R I F)
       → ModelsIO Γ → Prim.IO (R × SrvState Ψ Q R I F)
nextServer : ∀ {Ψ Γ Q R I F} → EnvIO Ψ → Proc Ψ Γ (SrvI Q R I F)
           → ModelsIO Γ → Prim.IO (SrvState Ψ Q R I F)
stopOnce : ∀ {Ψ Γ I F} → EnvIO Ψ → Proc Ψ Γ (∃Res I F ⊗ End)
         → ModelsIO Γ → Prim.IO (Σ I (λ i → ModelIO (F i)))

callOnce env (run p k) M q = evalIO env p M >>= λ { (M′ , a) → callOnce env (k a) M′ q }
callOnce env (ask k) M q = answer env (k q) M
callOnce env (stopP c e k) M q = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → callOnce env (k i) (putAtIO c M m) q }

answer env (run p k) M = evalIO env p M >>= λ { (M′ , a) → answer env (k a) M′ }
answer env (tell r k) M = nextServer env k M >>= λ st → return (r , st)
answer env (stopP c e k) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → answer env (k i) (putAtIO c M m) }

nextServer env (run p k) M = evalIO env p M >>= λ { (M′ , a) → nextServer env (k a) M′ }
nextServer env (daemon srv) M = return (_ , daemon srv , M)
nextServer env (machine turn halt j) M = return (_ , machine turn halt j , M)
nextServer env (stopP c e k) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → nextServer env (k i) (putAtIO c M m) }

stopOnce env (run p k) M = evalIO env p M >>= λ { (M′ , a) → stopOnce env (k a) M′ }
stopOnce env (give∃Dir i e) M = return (i , subst ModelIO e M)
stopOnce env (give∃At i x e _) M = return (i , subst ModelIO e (getAtIO x M))
stopOnce env (stopP c e k) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → stopOnce env (k i) (putAtIO c M m) }

callState : ∀ {Ψ Γ Q R I F} → EnvIO Ψ → Proc Ψ Γ (SrvI Q R I F) → ModelsIO Γ → Q → Prim.IO (R × SrvState Ψ Q R I F)

machineCall : ∀ {Ψ Γ Q R} {J : Set} {G : J → Ctx} → EnvIO Ψ
            → Proc Ψ Γ (Dat Q ⊸ Dat R ⊗ ∃Res J (λ j → Dir (G j)) ⊗ End)
            → ModelsIO Γ → Q → Prim.IO (R × Σ J (λ j → ModelsIO (G j)))
machineAnswer : ∀ {Ψ Γ R} {J : Set} {G : J → Ctx} → EnvIO Ψ
              → Proc Ψ Γ (Dat R ⊗ ∃Res J (λ j → Dir (G j)) ⊗ End)
              → ModelsIO Γ → Prim.IO (R × Σ J (λ j → ModelsIO (G j)))
callState env (daemon srv) M q = callOnce env (ServerI.call srv) M q
callState env (run p k) M q = evalIO env p M >>= λ { (M′ , a) → callState env (k a) M′ q }
callState env (stopP c e k) M q = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → callState env (k i) (putAtIO c M m) q }
callState env (machine turn halt j) M q = machineCall env (turn j) M q >>= λ { (r , (j′ , M′)) → return (r , _ , machine turn halt j′ , M′) }

machineCall env (ask k) M q = machineAnswer env (k q) M
machineCall env (run p k) M q = evalIO env p M >>= λ { (M′ , a) → machineCall env (k a) M′ q }
machineCall env (stopP c e k) M q = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → machineCall env (k i) (putAtIO c M m) q }
machineAnswer env (tell r k) M = stopOnce env k M >>= λ next → return (r , next)
machineAnswer env (run p k) M = evalIO env p M >>= λ { (M′ , a) → machineAnswer env (k a) M′ }
machineAnswer env (stopP c e k) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → machineAnswer env (k i) (putAtIO c M m) }

stopState : ∀ {Ψ Γ Q R I F} → EnvIO Ψ → Proc Ψ Γ (SrvI Q R I F) → ModelsIO Γ → Prim.IO (Σ I (λ i → ModelIO (F i)))
stopState env (daemon srv) M = stopOnce env (ServerI.stop srv) M
stopState env (machine turn halt j) M = stopOnce env (halt j) M
stopState env (run p k) M = evalIO env p M >>= λ { (M′ , a) → stopState env (k a) M′ }
stopState env (stopP c e k) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → stopState env (k i) (putAtIO c M m) }

mkService : ∀ {Ψ Γ Q R I F} → EnvIO Ψ → ServerI Ψ Q R I Γ F → ModelsIO Γ
          → Prim.IO (RunningIO Q R (Σ I (λ i → ModelIO (F i))))
mkService {Ψ} {Γ} {Q} {R} {I} {F} env srv M =
  newIORef {A = SrvState Ψ Q R I F} (Γ , daemon srv , M) >>= λ ref →
  return (record
    { onCall = λ q → readIORef ref >>= λ { (_ , proc , M₀) →
                     callState env proc M₀ q >>= λ { (r , st) → writeIORef ref st >> return r } }
    ; onStop = readIORef ref >>= λ { (_ , proc , M₀) → stopState env proc M₀ } })

mkMachine : ∀ {Ψ Q R I F} {J : Set} {G : J → Ctx} → EnvIO Ψ
          → ((j : J) → Proc Ψ (G j) (Dat Q ⊸ Dat R ⊗ ∃Res J (λ j′ → Dir (G j′)) ⊗ End))
          → ((j : J) → Proc Ψ (G j) (∃Res I F ⊗ End))
          → (j : J) → ModelsIO (G j) → Prim.IO (RunningIO Q R (Σ I (λ i → ModelIO (F i))))

provideIO : ∀ {Ψ Γ S} → EnvIO Ψ → Proc Ψ Γ S → ModelsIO Γ → Prim.IO (OfferIO S)
provideIO env (run p k)      M = evalIO env p M >>= λ { (M′ , a) → provideIO env (k a) M′ }
provideIO env end            _ = return tt
provideIO env (giveAt x k)   M = return (provideIO env k (delAtIO x M) >>= λ o → return (getAtIO x M , o))
provideIO env (tell a k)     M = return (provideIO env k M >>= λ o → return (a , o))
provideIO env (takeAt n _ k) M = return (λ m → provideIO env k (m , M))
provideIO env (ask k)        M = return (λ a → provideIO env (k a) M)
provideIO env (daemon srv)   M = mkService env srv M
provideIO env (machine turn halt j) M = mkMachine env turn halt j M
provideIO env (give∃Dir i e) M = return (return ((i , subst ModelIO e M) , tt))
provideIO env (give∃At i x e k) M = return (provideIO env k (delAtIO x M) >>= λ o → return ((i , subst ModelIO e (getAtIO x M)) , o))
provideIO env (stopP c e k) M = onStop (subst ModelIO e (getAtIO c M)) >>= λ { (i , m) → provideIO env (k i) (putAtIO c M m) }

mkMachine {J = J} {G = G} env turn halt j M =
  newIORef {A = Σ J (λ j → ModelsIO (G j))} (j , M) >>= λ ref →
  return (record
    { onCall = λ q → readIORef ref >>= λ { (j , M) →
        provideIO env (turn j) M >>= λ request → request q >>= λ answer → answer >>= λ { (r , resource) →
        resource >>= λ { (next , _) → writeIORef ref next >> return r } } }
    ; onStop = readIORef ref >>= λ { (j , M) → stopOnce env (halt j) M } })

------------------------------------------------------------------------
-- §5  纯 → IO：没有信道的子树，纯模型和 IO 模型是同一个东西；纯的 Offer 可以包成 IO 的句柄。
--   于是 root.test 里的模拟接口（provide [] worker 之类）一个字不改就能在 IO 里跑。
------------------------------------------------------------------------

NoChan    : St → Set
NoChanAll : Ctx → Set
NoChan (File _)   = ⊤
NoChan (Dir Γ)    = NoChanAll Γ
NoChan (Chan _)   = ⊥
NoChanAll []            = ⊤
NoChanAll ((_ , s) ∷ Γ) = NoChan s × NoChanAll Γ

-- 会话里传的子树都没有信道
NoChanS : Session → Set
NoChanS End            = ⊤
NoChanS (Res r ⊗ S)    = NoChan r × NoChanS S
NoChanS (Dat _ ⊗ S)    = NoChanS S
NoChanS (Res r ⊸ S)    = NoChan r × NoChanS S
NoChanS (Dat _ ⊸ S)    = NoChanS S
NoChanS (SrvI _ _ I F) = (i : I) → NoChan (F i)
NoChanS (∃Res I F ⊗ S) = ((i : I) → NoChan (F i)) × NoChanS S
NoChanS (∃Res I F ⊸ S) = ((i : I) → NoChan (F i)) × NoChanS S

NoChanSpec : Spec → Set
NoChanSpec (specI _ I Γ S) = (i : I) → NoChanAll (Γ i) × NoChanS (S i)

NoChanΨ : List Spec → Set
NoChanΨ []       = ⊤
NoChanΨ (ψ ∷ Ψ)  = NoChanSpec ψ × NoChanΨ Ψ

liftModel  : ∀ {s} → NoChan s → Model s → ModelIO s
liftModels : ∀ {Γ} → NoChanAll Γ → Models Γ → ModelsIO Γ
liftModel {File _} _  a  = a
liftModel {Dir Γ}  nc ms = liftModels {Γ} nc ms
liftModel {Chan _} () _
liftModels {[]}          _          _        = tt
liftModels {(_ , s) ∷ Γ} (nc , ncs) (m , ms) = liftModel {s} nc m , liftModels {Γ} ncs ms

dropModel  : ∀ {s} → NoChan s → ModelIO s → Model s
dropModels : ∀ {Γ} → NoChanAll Γ → ModelsIO Γ → Models Γ
dropModel {File _} _  a  = a
dropModel {Dir Γ}  nc ms = dropModels {Γ} nc ms
dropModel {Chan _} () _
dropModels {[]}          _          _        = tt
dropModels {(_ , s) ∷ Γ} (nc , ncs) (m , ms) = dropModel {s} nc m , dropModels {Γ} ncs ms

-- 纯的 Offer 包成 IO 的：⊗ 的值现成就在，⊸ 就是函数，Srv 的 Running 放进 IORef 变句柄
liftOffer : ∀ {S} → NoChanS S → Offer S → Prim.IO (OfferIO S)
liftOffer {End}          _          tt      = return tt
liftOffer {Res r ⊗ S}    (nr , ns)  (m , o) = return (liftOffer {S} ns o >>= λ o′ → return (liftModel {r} nr m , o′))
liftOffer {Dat _ ⊗ S}    ns         (a , o) = return (liftOffer {S} ns o >>= λ o′ → return (a , o′))
liftOffer {Res r ⊸ S}    (nr , ns)  f       = return (λ m → liftOffer {S} ns (f (dropModel {r} nr m)))
liftOffer {Dat _ ⊸ S}    ns         f       = return (λ a → liftOffer {S} ns (f a))
liftOffer {SrvI Q R I F} ns rn      =
  newIORef rn >>= λ ref →
  return (record
    { onCall = λ q → readIORef ref >>= λ r → let x = Running.onCall r q in writeIORef ref (proj₂ x) >> return (proj₁ x)
    ; onStop = readIORef ref >>= λ r → return (let (i , m) = Running.onStop r in i , liftModel {F i} (ns i) m) })

liftOffer {∃Res I F ⊗ S} (nf , ns) ((i , m) , o) =
  return (liftOffer {S} ns o >>= λ o′ → return ((i , liftModel {F i} (nf i) m) , o′))
liftOffer {∃Res I F ⊸ S} (nf , ns) f =
  return (λ { (i , m) → liftOffer {S} ns (f (i , dropModel {F i} (nf i) m)) })

-- 一条假设的纯兑现者 → IO 兑现者
liftSpec : ∀ {ψ} {{nc : NoChanSpec ψ}} → ⟦ ψ ⟧ → ⟦ ψ ⟧IO
liftSpec {specI _ I Γ S} {{nc}} f = λ i M → liftOffer {S i} (proj₂ (nc i)) (f i (dropModels {Γ i} (proj₁ (nc i)) M))

liftEnv : ∀ {Ψ} {{nc : NoChanΨ Ψ}} → Env Ψ → EnvIO Ψ
liftEnv {[]}    {{_}}        []       = []
liftEnv {ψ ∷ Ψ} {{nc , ncs}} (f ∷ fs) = liftSpec {ψ} {{nc}} f ∷ liftEnv {Ψ} {{ncs}} fs

------------------------------------------------------------------------
-- §6  真目录、真文件
--   File 怎么变成字节，是每种文件类型自己的事（Codec）。这里只管树的形状：Dir = 目录，File = 文件。
--   树上不能有没走完的会话（Codecs (Chan _) = ⊥）：存盘前先把话说完。
------------------------------------------------------------------------

record Codec (A : Set) : Set where
  field
    ext    : String                          -- 主文件的后缀（存的东西）
    encode : A → String
    decode : String → Maybe A
    views  : List (String × (A → String))    -- 顺带写出来给人看的（比如 .agda），load 不读它们
open Codec public

Codecs    : St → Set
CodecsAll : Ctx → Set
Codecs (File A) = Codec A
Codecs (Dir Γ)  = CodecsAll Γ
Codecs (Chan _) = ⊥
CodecsAll []            = ⊤
CodecsAll ((_ , s) ∷ Γ) = Codecs s × CodecsAll Γ

private
  writeViews : ∀ {A : Set} → String → List (String × (A → String)) → A → Prim.IO ⊤
  writeViews path []             a = return tt
  writeViews path ((e , f) ∷ vs) a = PF.writeFile (path ++ˢ e) (f a) >>= λ _ → writeViews path vs a

store    : String → ∀ {s} → Codecs s → ModelIO s → Prim.IO ⊤
storeAll : String → ∀ {Γ} → CodecsAll Γ → ModelsIO Γ → Prim.IO ⊤
store path {File A} cd a   = PF.writeFile (path ++ˢ ext cd) (encode cd a) >> writeViews path (views cd) a
store path {Dir Γ}  cds ms = mkdirP path >> storeAll path {Γ} cds ms
store path {Chan _} () _
storeAll path {[]}          _          _        = return tt
storeAll path {(n , s) ∷ Γ} (cd , cds) (m , ms) = store (path ++ˢ "/" ++ˢ n) {s} cd m >> storeAll path {Γ} cds ms

load    : String → ∀ {s} → Codecs s → Prim.IO (Maybe (ModelIO s))
loadAll : String → ∀ {Γ} → CodecsAll Γ → Prim.IO (Maybe (ModelsIO Γ))
load path {File A} cd  = fileExists (path ++ˢ ext cd) >>= λ where
  false → return nothing
  true  → PF.readFile (path ++ˢ ext cd) >>= λ txt → return (decode cd txt)
load path {Dir Γ}  cds = dirExists path >>= λ where
  false → return nothing
  true  → loadAll path {Γ} cds
load path {Chan _} ()
loadAll path {[]}          _          = return (just tt)
loadAll path {(n , s) ∷ Γ} (cd , cds) = load (path ++ˢ "/" ++ˢ n) {s} cd >>= λ where
  nothing  → return nothing
  (just m) → loadAll path {Γ} cds >>= λ where
    nothing   → return nothing
    (just ms) → return (just (m , ms))
