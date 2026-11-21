{-# OPTIONS --guardedness #-}
module SessionEnv where
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Code.SessionProtocol using (RefSpec; refSpec; local; docker; parseRefSpec)
open import Code.SessionTools using (sessionTools)
open import Code.SessionTools public using (SessionΨ)
open import Code.Driver public using (ProcReq; ProcOut; procReq; outText; ProcSpec; Registry; Pick; SubT; select; all-nil; all-cons)
open import Code.TermTool public using (ptySpec; TermFiles)
open import Code.Tools.FsTool public using (fsSpec; FsOwnedCtx)
open import Code.Tools.NetTool public using (netSpec; NetOwnedCtx)
open import Code.Tools.GitTool public using (gitSpec; GitOwnedCtx)
open import Context.Terminal public using (Byte; Bytes; bytes; Key; textKey; enter; escape; backspace; tab; up; down; right; left; ctrl; encodeKey; TermTopology; allTTY; pipeStdioWithTTY; SandboxTarget; localSandbox; dockerSandbox; TermConfig; termConfig; Signal; sigINT; sigTERM; sigHUP; sigQUIT; sigKILL; TermStep; writeStdin; writeTTY; closeStdin; sleepMs; resizeTTY; sendSignal; drainRaw; RawTermObs; rawObs; ttyOut; stdoutOut; stderrOut; exitStatus; emptyObs; appendObs; Screen; blankScreen; stepANSI; screenLines)
open import Context.Tools.FsSandbox public using (FsNodeKind; regularNode; dirNode; symlinkNode; FsFixture; fixDir; fixFile; fixSymlink; FsConfig; fsConfig; FsStep; runCmd; writeFileStep; mkdirStep; symlinkStep; chmodStep; unlinkStep; snapshotStep; FsEntryObs; fsEntry; RawFsObs; rawFsObs; emptyFsObs; VirtualFs; virtualFs; initVirtualFs; stepVirtualFs; traceVirtualFs; FsDiff; added; modified; removed; diffSnapshot)
open import Context.Tools.NetSandbox public using (HttpRoute; httpRoute; RawStubRule; rawStubRule; NetTopology; httpStubMode; tcpStubMode; udpStubMode; daemonProbeMode; httpDelayedStubMode; tcpDelayedStubMode; NetConfig; netConfig; encodeHttpReq; encodeHttpResp; HttpReqView; httpReqView; HttpRespView; httpRespView; parseHttpReq; parseHttpResp; NetStep; runClient; waitPortReady; tcpProbe; httpProbe; udpProbe; sleepNetMs; drainNet; RawNetObs; rawNetObs; emptyNetObs; wireReply; capturedReqs; timedOut; evalStubExchange)
open import Context.Tools.GitSandbox public using (GitConfig; gitConfig; GitStep; gitWriteFile; gitRemoveFile; gitStageAll; gitStagePaths; gitCommit; gitSwitchBranch; gitCreateTag; gitStatus; gitRunTarget; GitRepoSummary; gitSummary; RawGitObs; rawGitObs; commitHash; summary; PureGitRepo; initPureGit)
open import Context.Tools.FuzzGen public using (Seed; mkSeed; nextNat; Gen; runGen; genPure; genMap; genBind; genPair; genBounded; genBool; genByte; genList; genBytes; genChoose; sampleMany; Shrinker; shrinkNat; shrinkByte; shrinkList; shrinkBytes; firstFailure; minimize; fuzzCheck)
open import Ownership public using (≡-inst; withEphemeral)
open import OwnershipIO public using (EnvIO; RunningIO; OfferIO; evalIO; provideIO)
reference : RefSpec
reference = decode (parseRefSpec "(ref-target (local \"/bin/false\") (args) (timeoutMs 30000))")
  where
    decode : Data.Maybe.Maybe RefSpec → RefSpec
    decode (just r) = r
    decode nothing = refSpec (local "/bin/false") [] 30000
sessionEnv : EnvIO SessionΨ
sessionEnv = sessionTools reference "/bin/false" "/bin/false" "."
