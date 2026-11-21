{-# OPTIONS --safe #-}
module Test.WorldFuzzTarget where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.Fin using () renaming (toℕ to octet)
open import Data.List using (List; []; _∷_; _++_; map; foldl; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList) renaming (_++_ to _++ˢ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Context.Terminal using (Byte; Bytes; byte; bytes)
open import Context.Tools.FuzzGen using
  ( Seed; mkSeed; Gen; runGen; genPure; genMap; genBind; genPair
  ; genBounded; genBool; genByte; genList; genBytes; genChoose )
open import Context.Tools.FsSandbox using
  ( FsNodeKind; regularNode; dirNode; symlinkNode )
open import Context.Tools.NetSandbox using (encodeHttpReq)
open import Context.World

------------------------------------------------------------------------
-- §1 Deterministic Serialization Helpers (Pure `--safe`, Fast-Path Lean 4)
------------------------------------------------------------------------

parseDecNat : String → ℕ
parseDecNat s = foldl (λ acc c → acc * 10 + (toℕ c ∸ 48)) 0 (toList s)

showBoolTag : Bool → String
showBoolTag true  = "true"
showBoolTag false = "false"

showByteList : Bytes → String
showByteList []       = "."
showByteList (b ∷ bs) = show (octet b) ++ˢ "," ++ˢ showByteList bs

showMaybeBytes : Maybe Bytes → String
showMaybeBytes nothing   = "EOF"
showMaybeBytes (just bs) = "LINE(" ++ˢ show (length bs) ++ˢ ":" ++ˢ showByteList bs ++ˢ ")"

showMaybeStr : Maybe String → String
showMaybeStr nothing  = "NONE"
showMaybeStr (just s) = "SOME(" ++ˢ s ++ˢ ")"

tagFsErr : FsError → String
tagFsErr fsNotFound         = "ENOENT"
tagFsErr fsIsDirectory      = "EISDIR"
tagFsErr fsNotDirectory     = "ENOTDIR"
tagFsErr fsAlreadyExists    = "EEXIST"
tagFsErr fsPermissionDenied = "EACCES"
tagFsErr fsSymlinkLoop      = "ELOOP"
tagFsErr fsInvalidPath      = "EINVAL"
tagFsErr fsIoError          = "EIO"

tagNodeKind : FsNodeKind → String
tagNodeKind regularNode = "REG"
tagNodeKind dirNode     = "DIR"
tagNodeKind symlinkNode = "SYM"

tagNetErr : NetError → String
tagNetErr netConnRefused     = "ECONNREFUSED"
tagNetErr netTimedOut        = "ETIMEDOUT"
tagNetErr netInvalidEndpoint = "EINVALIDEP"
tagNetErr netTlsError        = "ETLS"
tagNetErr netIoError         = "ENETIO"

------------------------------------------------------------------------
-- §2 `FuzzGen` Multi-Capability Instruction Vocabulary & Generator
------------------------------------------------------------------------

data FuzzFsStep : Set where
  fzWrite   : String → Bytes → FuzzFsStep
  fzRead    : String → FuzzFsStep
  fzMkdir   : String → ℕ → FuzzFsStep
  fzSymlink : String → String → FuzzFsStep
  fzUnlink  : String → FuzzFsStep
  fzStat    : String → FuzzFsStep

record FuzzPlan : Set where
  constructor fuzzPlan
  field
    sleepDelta : ℕ
    httpTarget : String
    fsOps      : List FuzzFsStep
open FuzzPlan public

pathPool : List String
pathPool =
    "work/alpha.bin"
  ∷ "./work/beta.bin"
  ∷ "work/nested/deep.bin"
  ∷ "./flat.dat"
  ∷ "work/link1"
  ∷ "work/link2"
  ∷ "work"
  ∷ "."
  ∷ "../escape"
  ∷ "work//bad"
  ∷ "/abs/path"
  ∷ "work/alpha.bin/child"
  ∷ []

linkTargetPool : List String
linkTargetPool =
    "work/alpha.bin"
  ∷ "./work/beta.bin"
  ∷ "work/link1"
  ∷ "work/link2"
  ∷ "../outside"
  ∷ ""
  ∷ []

modePool : List ℕ
modePool = 493 ∷ 448 ∷ 511 ∷ []

httpTargetPool : List String
httpTargetPool = "/alpha" ∷ "/beta" ∷ "/missing" ∷ []

mkFsStepFromTag : ℕ → String → Bytes → ℕ → String → FuzzFsStep
mkFsStepFromTag 0 p bs _  _   = fzWrite p bs
mkFsStepFromTag 1 p _  _  _   = fzRead p
mkFsStepFromTag 2 p _  md _   = fzMkdir p md
mkFsStepFromTag 3 p _  _  dst = fzSymlink p dst
mkFsStepFromTag 4 p _  _  _   = fzUnlink p
mkFsStepFromTag _ p _  _  _   = fzStat p

genFsStep : Gen FuzzFsStep
genFsStep =
  genBind (genBounded 5) λ tag →
  genBind (genChoose "work/alpha.bin" pathPool) λ p →
  genBind (genBounded 4) λ bLen →
  genBind (genBytes bLen) λ bs →
  genBind (genChoose 493 modePool) λ md →
  genBind (genChoose "work/alpha.bin" linkTargetPool) λ dst →
  genPure (mkFsStepFromTag tag p bs md dst)

seedCornerOps : ℕ → List FuzzFsStep
seedCornerOps n =
  if (n % 3) ≡ᵇ 0 then
    ( fzWrite "./work/alpha.bin" (byte 0 ∷ byte 255 ∷ bytes "‿\n")
    ∷ fzSymlink "work/link1" "work/alpha.bin"
    ∷ fzSymlink "work/link2" "./work/link1"
    ∷ fzRead "work/link2"
    ∷ [] )
  else if (n % 3) ≡ᵇ 1 then
    ( fzSymlink "loopA" "loopB"
    ∷ fzSymlink "loopB" "loopA"
    ∷ fzRead "loopA"
    ∷ fzUnlink "loopA"
    ∷ fzUnlink "loopB"
    ∷ [] )
  else
    ( fzMkdir "emptydir" 493
    ∷ fzStat "emptydir"
    ∷ fzUnlink "emptydir"
    ∷ fzStat "emptydir"
    ∷ [] )

genPlanForSeed : ℕ → FuzzPlan
genPlanForSeed idx =
  proj₁ (runGen
    (genBind (genBounded 8) λ dt →
     genBind (genChoose "/alpha" httpTargetPool) λ tgt →
     genBind (genList 10 genFsStep) λ ops →
     genPure (fuzzPlan dt tgt (seedCornerOps idx ++ ops)))
    (mkSeed (1000 + idx * 131)))

------------------------------------------------------------------------
-- §3 Closed-World Multi-Capability `CliApp` Executed identically in Pure & IO
------------------------------------------------------------------------

logWriteOutcome : String → ℕ → FsError ⊎ ⊤ → WorldProg CliCaps ℕ
logWriteOutcome p _   (inj₁ e) =
  writeStderrStrW tty∈Cli ("FS_WRITE_ERR:" ++ˢ p ++ˢ ":" ++ˢ tagFsErr e ++ˢ "\n") >>w pure 1
logWriteOutcome p len (inj₂ _) =
  writeStdoutStrW tty∈Cli ("FS_WRITE_OK:" ++ˢ p ++ˢ ":" ++ˢ show len ++ˢ "\n") >>w pure 0

logReadOutcome : String → FsError ⊎ Bytes → WorldProg CliCaps ℕ
logReadOutcome p (inj₁ e) =
  writeStderrStrW tty∈Cli ("FS_READ_ERR:" ++ˢ p ++ˢ ":" ++ˢ tagFsErr e ++ˢ "\n") >>w pure 1
logReadOutcome p (inj₂ bs) =
  writeStdoutStrW tty∈Cli ("FS_READ_OK:" ++ˢ p ++ˢ ":" ++ˢ showByteList bs ++ˢ "\n") >>w pure 0

logMkdirOutcome : String → FsError ⊎ ⊤ → WorldProg CliCaps ℕ
logMkdirOutcome p (inj₁ e) =
  writeStderrStrW tty∈Cli ("FS_MKDIR_ERR:" ++ˢ p ++ˢ ":" ++ˢ tagFsErr e ++ˢ "\n") >>w pure 1
logMkdirOutcome p (inj₂ _) =
  writeStdoutStrW tty∈Cli ("FS_MKDIR_OK:" ++ˢ p ++ˢ "\n") >>w pure 0

logSymlinkOutcome : String → String → FsError ⊎ ⊤ → WorldProg CliCaps ℕ
logSymlinkOutcome p _   (inj₁ e) =
  writeStderrStrW tty∈Cli ("FS_SYM_ERR:" ++ˢ p ++ˢ ":" ++ˢ tagFsErr e ++ˢ "\n") >>w pure 1
logSymlinkOutcome p dst (inj₂ _) =
  writeStdoutStrW tty∈Cli ("FS_SYM_OK:" ++ˢ p ++ˢ "->" ++ˢ dst ++ˢ "\n") >>w pure 0

logUnlinkOutcome : String → FsError ⊎ ⊤ → WorldProg CliCaps ℕ
logUnlinkOutcome p (inj₁ e) =
  writeStderrStrW tty∈Cli ("FS_UNLINK_ERR:" ++ˢ p ++ˢ ":" ++ˢ tagFsErr e ++ˢ "\n") >>w pure 1
logUnlinkOutcome p (inj₂ _) =
  writeStdoutStrW tty∈Cli ("FS_UNLINK_OK:" ++ˢ p ++ˢ "\n") >>w pure 0

logStatOutcome : String → FsError ⊎ FsNodeKind → WorldProg CliCaps ℕ
logStatOutcome p (inj₁ e) =
  writeStderrStrW tty∈Cli ("FS_STAT_ERR:" ++ˢ p ++ˢ ":" ++ˢ tagFsErr e ++ˢ "\n") >>w pure 1
logStatOutcome p (inj₂ k) =
  writeStdoutStrW tty∈Cli ("FS_STAT_OK:" ++ˢ p ++ˢ ":" ++ˢ tagNodeKind k ++ˢ "\n") >>w pure 0

runOneFsStep : FuzzFsStep → WorldProg CliCaps ℕ
runOneFsStep (fzWrite p bs)   = writeFileW fs∈Cli p bs >>=w logWriteOutcome p (length bs)
runOneFsStep (fzRead p)       = readFileW fs∈Cli p >>=w logReadOutcome p
runOneFsStep (fzMkdir p md)   = mkdirW fs∈Cli p md >>=w logMkdirOutcome p
runOneFsStep (fzSymlink p dst) = symlinkW fs∈Cli p dst >>=w logSymlinkOutcome p dst
runOneFsStep (fzUnlink p)     = unlinkW fs∈Cli p >>=w logUnlinkOutcome p
runOneFsStep (fzStat p)       = statW fs∈Cli p >>=w logStatOutcome p

runFsStepList : List FuzzFsStep → WorldProg CliCaps ℕ
runFsStepList []       = pure 0
runFsStepList (s ∷ ss) =
  runOneFsStep s >>=w λ c₁ →
  runFsStepList ss >>=w λ c₂ →
  pure (c₁ + c₂)

logNetResult : String → NetError ⊎ Bytes → WorldProg CliCaps ℕ
logNetResult lbl (inj₁ e) =
  writeStderrStrW tty∈Cli ("NET_ERR:" ++ˢ lbl ++ˢ ":" ++ˢ tagNetErr e ++ˢ "\n") >>w pure 1
logNetResult lbl (inj₂ bs) =
  writeStdoutStrW tty∈Cli ("NET_OK:" ++ˢ lbl ++ˢ ":" ++ˢ show (length bs) ++ˢ "\n") >>w
  writeStdoutW tty∈Cli bs >>w
  writeStdoutStrW tty∈Cli "\n" >>w
  pure 0

maybeTcpProbe : String → ℕ → ℕ → Bytes → WorldProg CliCaps ℕ
maybeTcpProbe lbl port tms reqBytes =
  if port ≡ᵇ 0 then pure 0
  else (tcpExchangeW net∈Cli "127.0.0.1" port reqBytes true tms >>=w logNetResult lbl)

defaultHttpHeaders : List (String × String)
defaultHttpHeaders = ("Host" , "127.0.0.1") ∷ ("Connection" , "close") ∷ []

runNetProbes : String → ℕ → ℕ → ℕ → WorldProg CliCaps ℕ
runNetProbes target fastPort slowPort closedPort =
  let reqBytes = encodeHttpReq "GET" target defaultHttpHeaders [] in
  if (fastPort ≡ᵇ 0) ∧ (slowPort ≡ᵇ 0) ∧ (closedPort ≡ᵇ 0) then pure 0
  else
    (maybeTcpProbe "fast" fastPort 3000 reqBytes >>=w λ e₁ →
     maybeTcpProbe "slow" slowPort 120 reqBytes >>=w λ e₂ →
     maybeTcpProbe "closed" closedPort 500 reqBytes >>=w λ e₃ →
     tcpExchangeW net∈Cli "" 0 reqBytes true 100 >>=w λ rInv →
     logNetResult "invalid" rInv >>=w λ e₄ →
     pure (e₁ + e₂ + e₃ + e₄))

decodeCliArgs : List String → ℕ × ℕ × ℕ × ℕ
decodeCliArgs (sIdx ∷ fP ∷ sP ∷ cP ∷ _) =
  parseDecNat sIdx , parseDecNat fP , parseDecNat sP , parseDecNat cP
decodeCliArgs (sIdx ∷ _) =
  parseDecNat sIdx , 0 , 0 , 0
decodeCliArgs [] =
  0 , 0 , 0 , 0

readStdinByMode : Bool → WorldProg CliCaps (Maybe Bytes × Maybe Bytes × Bytes)
readStdinByMode true =
  readStdinLineW env∈Cli >>=w λ l₁ →
  pure (l₁ , nothing , [])
readStdinByMode false =
  readStdinLineW env∈Cli >>=w λ l₁ →
  readStdinLineW env∈Cli >>=w λ l₂ →
  readStdinAllW env∈Cli >>=w λ rest →
  pure (l₁ , l₂ , rest)

fuzzCliApp : CliApp CliCaps
fuzzCliApp =
  getProgNameW env∈Cli >>=w λ prog →
  getArgsW env∈Cli >>=w λ rawArgs →
  let parsed     = decodeCliArgs rawArgs
      seedIdx    = proj₁ parsed
      fastPort   = proj₁ (proj₂ parsed)
      slowPort   = proj₁ (proj₂ (proj₂ parsed))
      closedPort = proj₂ (proj₂ (proj₂ parsed))
      plan       = genPlanForSeed seedIdx
  in
  nowMonoW clock∈Cli >>=w λ t₀ →
  nowWallW clock∈Cli >>=w λ _ →
  sleepW clock∈Cli (sleepDelta plan) >>w
  nowMonoW clock∈Cli >>=w λ t₁ →
  lookupEnvW env∈Cli "FUZZ_KEY" >>=w λ envPresent →
  lookupEnvW env∈Cli "EMPTY_KEY" >>=w λ envEmpty →
  lookupEnvW env∈Cli "MISSING_KEY" >>=w λ envMissing →
  isTTYStdinW tty∈Cli >>=w λ ttyIn →
  readStdinByMode ttyIn >>=w λ stdinTriple →
  let line₁     = proj₁ stdinTriple
      line₂     = proj₁ (proj₂ stdinTriple)
      restStdin = proj₂ (proj₂ stdinTriple)
  in
  isTTYStdoutW tty∈Cli >>=w λ ttyOut →
  let banner = if ttyOut then "\x1b[32mTTY=1\x1b[0m" else "TTY=0" in
  writeStdoutStrW tty∈Cli
    ("PROG=" ++ˢ prog
     ++ˢ "|SEED=" ++ˢ show seedIdx
     ++ˢ "|MONO_LE=" ++ˢ showBoolTag (t₀ ≤ᵇ t₁)
     ++ˢ "|ENV1=" ++ˢ showMaybeStr envPresent
     ++ˢ "|ENV2=" ++ˢ showMaybeStr envEmpty
     ++ˢ "|ENV3=" ++ˢ showMaybeStr envMissing
     ++ˢ "|L1=" ++ˢ showMaybeBytes line₁
     ++ˢ "|L2=" ++ˢ showMaybeBytes line₂
     ++ˢ "|REST=" ++ˢ showByteList restStdin
     ++ˢ "|" ++ˢ banner ++ˢ "\n") >>w
  runFsStepList (fsOps plan) >>=w λ fsErrs →
  runNetProbes (httpTarget plan) fastPort slowPort closedPort >>=w λ netErrs →
  pure ((seedIdx * 7 + fsErrs + netErrs) % 17)
