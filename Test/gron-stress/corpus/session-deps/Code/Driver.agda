{-# OPTIONS --guardedness #-}
module Code.Driver where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; concatMap; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; lines; words; wordsBy; intersperse; toList) renaming (_++_ to _++ˢ_)
open import Data.Char as Char using (isAlpha; isDigit)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import IO.Primitive as Prim
import IO.Primitive.Finite as PF
open import Ownership hiding (_>>=_; _>>_; Home; Agent; wake; mockAgent)
open import OwnershipIO
open import OwnershipIO.FFI
open import OwnershipIO.AsyncChildFFI using (spawnAsyncChild; pollAsyncChild; stopAsyncChild)
open import Code using (Code; _==ˢ_; allᵇ)
open import Code.Parse using (parse)
open import Code.Harness using (NodeΨ; nodeAgent; HomeShape; Home; HomeCtx; AgentS)
open import Code.Transport using (CheckResult)
open import Code.Protocol
open import Code.AgdaTool using (agdaTool; writeCodes; parentPath)
open import Code.AI using (Backend; aiService; isConcurrentBackend)
import Meta.Sandbox as Sandbox

private
  infixl 1 _>>=_ _>>_
  _>>=_ = Prim._>>=_
  _>>_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → Prim.IO B → Prim.IO B
  m >> n = m >>= λ _ → n
  return = Prim.return

------------------------------------------------------------------------
-- §1  根登记表，和从表里挑子表
------------------------------------------------------------------------

Registry : List Spec → Set₁
Registry Ψall = EnvIO Ψall

private
  pickIf : Bool → Spec → Maybe Spec → Maybe Spec
  pickIf true  ψ _ = just ψ
  pickIf false _ r = r

-- 按名字查表
findₛ : Name → List Spec → Maybe Spec
findₛ n []      = nothing
findₛ n (ψ ∷ Ψ) = pickIf (n ==ˢ sname ψ) ψ (findₛ n Ψ)

-- 会话要的一条 ψ 在表里：按名字查到的那条和 ψ 一模一样（名字、子树形状、协议）。
-- 实例 ≡-inst 算这个等式；对不上就是编译期错误——会话向根要了一个根没有（或形状不同）的工具。
Pick : Spec → List Spec → Set₁
Pick ψ Ψall = findₛ (sname ψ) Ψall ≡ just ψ

-- 子表：会话要的每一条都在根里（Spec 住在 Set₁，所以用 All 而不是 ×；两个实例让 Agda 自己把 All 拼出来）
SubT : List Spec → List Spec → Set₁
SubT Ψ Ψall = All (λ ψ → Pick ψ Ψall) Ψ

instance
  all-nil  : ∀ {a p} {A : Set a} {P : A → Set p} → All P []
  all-nil = []
  all-cons : ∀ {a p} {A : Set a} {P : A → Set p} {x : A} {xs : List A} {{px : P x}} {{pxs : All P xs}} → All P (x ∷ xs)
  all-cons {{px}} {{pxs}} = px ∷ pxs

-- 顺着查表的脚印，把兑现者从 All 里取出来
pickIO : (n : Name) {Ψall : List Spec} → EnvIO Ψall → ∀ {ψ} → findₛ n Ψall ≡ just ψ → ⟦ ψ ⟧IO
pickIO n {[]}     []       ()
pickIO n {ψ′ ∷ Ψ} (e ∷ es) eq = go (n ==ˢ sname ψ′) eq
  where
    go : (b : Bool) → ∀ {ψ} → pickIf b ψ′ (findₛ n Ψ) ≡ just ψ → ⟦ ψ ⟧IO
    go true  refl = e
    go false eq′  = pickIO n es eq′

-- 开会话：挑子表。Ψ 是这个会话的封闭世界
select : {Ψall : List Spec} (Ψ : List Spec) {{sub : SubT Ψ Ψall}} → Registry Ψall → EnvIO Ψ
select []      {{_}}      reg = []
select (ψ ∷ Ψ) {{p ∷ ps}} reg = pickIO (sname ψ) reg p ∷ select Ψ {{ps}} reg


record ProcReq : Set where
  constructor procReq
  field
    command : String
    arguments : List String
    stdin : String
open ProcReq public

ProcOut : Set
ProcOut = ProcResult

outText : ProcOut → String
outText (procResult _ out _) = out

procExec : String → ℕ → RunningIO ProcReq ProcOut (⊤ × ⊤)
procExec cwd timeout = record
  { onCall = λ q → readProcessAt cwd timeout (command q) (arguments q) (stdin q)
  ; onStop = return (tt , tt) }

ProcSpec : Spec
ProcSpec = mkSpec "procExec" [] (Srv ProcReq ProcOut (Dir []))

moduleNameOf : String → Maybe String
moduleNameOf src = go (lines src)
  where
    go : List String → Maybe String
    go [] = nothing
    go (l ∷ ls) with words l
    ... | "module" ∷ n ∷ _ = just n
    ... | _ = go ls

safeModule : String → Bool
safeModule n = allᵇ validPart (wordsBy ('.' Char.≟_) n)
  where
    validPart : String → Bool
    validPart s = if s ==ˢ "" then false else allᵇ (λ c → isAlpha c ∨ isDigit c) (toList s)

writeSource : String → String → Prim.IO (Maybe String)
writeSource dir src with moduleNameOf src
... | nothing = return nothing
... | just n = if safeModule n then
  (let parts = wordsBy ('.' Char.≟_) n
       file = intersperse "/" parts ++ˢ ".agda"
   in mkdirP (dir ++ˢ "/" ++ˢ parentPath parts) >> PF.writeFile (dir ++ˢ "/" ++ˢ file) src >> return (just file))
  else return nothing

writeSources : String → List (String × String) → Prim.IO ⊤
writeSources dir [] = return tt
writeSources dir ((_ , src) ∷ ss) = writeSource dir src >>= λ _ → writeSources dir ss

dumpTool : String → String → List String → RunningIO DumpReq DumpResult (⊤ × ⊤)
dumpTool bin scratch incs = record
  { onCall = λ req → freshDirectory scratch >>= λ dir →
      writeCodes dir (codeDeps req) >> writeSources dir (sourceDeps req) >> writeSource dir (source req) >>= λ file →
      dumpAt dir file >>= λ result → removeAll dir >> return result
  ; onStop = return (tt , tt) }
  where
    decoded : Maybe Code → DumpResult
    decoded nothing = dumpFailed "dump: unsupported S-expression output"
    decoded (just c) = dumped c
    dumpAt : String → Maybe String → Prim.IO DumpResult
    dumpAt dir nothing = return (dumpFailed "source: missing or unsafe module name")
    dumpAt dir (just f) = readProcessAt dir 120000 bin
      (concatMap (λ i → "-i" ∷ i ∷ []) ("." ∷ incs) ++ (f ∷ [])) "" >>= λ where
        (procResult zero out _) → return (decoded (parse out))
        (procResult (suc _) out err) → return (dumpFailed (out ++ˢ err))

-- The recursive registry is tied only at the IO boundary. Opening each ai slot
-- allocates its own service; a child never receives its parent's tool handles.
nodeEnvironmentWith : Prim.IO (RunningIO AIReq AIReply (⊤ × ⊤)) →
                      (DumpReq → Prim.IO DumpResult) → (AgdaCheckReq → Prim.IO CheckResult) → Prim.IO (EnvIO NodeΨ)
nodeEnvironmentWith ai dump check = fixIO λ env → return
  ((λ _ _ → ai)
   ∷ (λ _ _ → return (record { onCall = dump ; onStop = return (tt , tt) }))
   ∷ (λ _ _ → return (record { onCall = check ; onStop = return (tt , tt) }))
   ∷ (λ sh home → provideIO env (nodeAgent sh) home) ∷ [])

-- Concurrent IO realization of `NodeΨ`: waking a child spawns a background worker
-- thread immediately (`onCall` is non-blocking; `onStop` cancels & harvests cleanly).
asyncNodeEnvironmentWith : Prim.IO (RunningIO AIReq AIReply (⊤ × ⊤)) →
                           (DumpReq → Prim.IO DumpResult) → (AgdaCheckReq → Prim.IO CheckResult) → Prim.IO (EnvIO NodeΨ)
asyncNodeEnvironmentWith ai dump check = fixIO λ env → return
  ((λ _ _ → ai)
   ∷ (λ _ _ → return (record { onCall = dump ; onStop = return (tt , tt) }))
   ∷ (λ _ _ → return (record { onCall = check ; onStop = return (tt , tt) }))
   ∷ (λ sh home → provideIO env (nodeAgent sh) home >>= λ receive →
        return (λ task → receive task >>= λ innerSrv →
          spawnAsyncChild (onCall innerSrv tt) (onStop innerSrv) >>= λ h →
          return (record { onCall = pollAsyncChild h ; onStop = stopAsyncChild h }))) ∷ [])

nodeEnvironmentForBackend : Bool → Prim.IO (RunningIO AIReq AIReply (⊤ × ⊤)) →
                            (DumpReq → Prim.IO DumpResult) → (AgdaCheckReq → Prim.IO CheckResult) → Prim.IO (EnvIO NodeΨ)
nodeEnvironmentForBackend true  = asyncNodeEnvironmentWith
nodeEnvironmentForBackend false = nodeEnvironmentWith

nodeEnvironmentUsing : Prim.IO (RunningIO AIReq AIReply (⊤ × ⊤)) → String → String → List String → Prim.IO (EnvIO NodeΨ)
nodeEnvironmentUsing ai dumpBin scratch includes = nodeEnvironmentWith ai
  (onCall (dumpTool dumpBin (scratch ++ˢ "/dump") includes)) (onCall (agdaTool includes (scratch ++ˢ "/agda")))

nodeEnvironment : Backend → String → String → List String → Prim.IO (EnvIO NodeΨ)
nodeEnvironment backend dumpBin scratch includes =
  nodeEnvironmentForBackend (isConcurrentBackend backend) (aiService backend)
    (onCall (dumpTool dumpBin (scratch ++ˢ "/dump") includes))
    (onCall (agdaTool includes (scratch ++ˢ "/agda")))

sandboxDumpTool : (dumpBin repo scratch : String) → List String → RunningIO DumpReq DumpResult (⊤ × ⊤)
sandboxDumpTool dumpBin repo scratch ancestorDirs = record
  { onCall = Sandbox.sandboxDump dumpBin repo scratch ancestorDirs
  ; onStop = return (tt , tt) }

sandboxAgdaTool : (repo scratch : String) → List String → RunningIO AgdaCheckReq CheckResult (⊤ × ⊤)
sandboxAgdaTool repo scratch ancestorDirs = record
  { onCall = Sandbox.sandboxAgdaCheck repo scratch ancestorDirs
  ; onStop = return (tt , tt) }

sandboxNodeEnvironmentUsing : Prim.IO (RunningIO AIReq AIReply (⊤ × ⊤)) →
  (repo dumpBin scratch : String) → List String → Prim.IO (EnvIO NodeΨ)
sandboxNodeEnvironmentUsing ai repo dumpBin scratch ancestorDirs = nodeEnvironmentWith ai
  (onCall (sandboxDumpTool dumpBin repo (scratch ++ˢ "/dump") ancestorDirs))
  (onCall (sandboxAgdaTool repo (scratch ++ˢ "/agda") ancestorDirs))

sandboxNodeEnvironment : Backend → (repo dumpBin scratch : String) → List String → Prim.IO (EnvIO NodeΨ)
sandboxNodeEnvironment backend repo dumpBin scratch ancestorDirs =
  nodeEnvironmentForBackend (isConcurrentBackend backend) (aiService backend)
    (onCall (sandboxDumpTool dumpBin repo (scratch ++ˢ "/dump") ancestorDirs))
    (onCall (sandboxAgdaTool repo (scratch ++ˢ "/agda") ancestorDirs))

SessionΨ : List Spec
SessionΨ = ProcSpec ∷ NodeΨ

-- The open session selects its tools from this total registry. A closed child
-- still receives exactly NodeΨ and therefore has no procExec capability.
sessionRegistry : Backend → String → String → List String → String → ℕ → Prim.IO (Registry SessionΨ)
sessionRegistry backend dumpBin scratch includes cwd timeout =
  nodeEnvironment backend dumpBin scratch includes >>= λ env →
  return ((λ _ _ → return (procExec cwd timeout)) ∷ env)

record Workspace (Ψ : List Spec) (s : St) : Set₁ where
  field
    env : EnvIO Ψ
    root : String
    codecs : Codecs s
open Workspace public

runStep : ∀ {Ψ s A} → Workspace Ψ s → Prog Ψ s s A → Prim.IO (Maybe A)
runStep {s = s} ws p = load (root ws) {s} (codecs ws) >>= λ where
  nothing → return nothing
  (just m) → evalIO (env ws) p m >>= λ { (m′ , a) → store (root ws) {s} (codecs ws) m′ >> return (just a) }

plant : ∀ {Ψ s} → Workspace Ψ s → ModelIO s → Prim.IO ⊤
plant {s = s} ws = store (root ws) {s} (codecs ws)
