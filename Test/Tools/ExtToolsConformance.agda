{-# OPTIONS --safe #-}
module Test.Tools.ExtToolsConformance where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; map; reverse)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal using (Bytes; byte; localSandbox)
open import Context.Tools.FuzzGen
open import Context.Tools.FsSandbox
open import Context.Tools.NetSandbox
open import Context.Tools.GitSandbox

-- One seed generates both files; the second draw uses the first draw's state.
generatedTree : List (String × Bytes)
generatedTree = proj₁ (runGen (genMap makeTree
  (genPair (genList 4 genByte) (genList 4 genByte))) (mkSeed 42))
  where
    makeTree : Bytes × Bytes → List (String × Bytes)
    makeTree (a , b) = ("candidates/alpha.bin" , a) ∷ ("candidates/beta.bin" , b) ∷ []

firstPayload secondPayload : Bytes
firstPayload = byte 129 ∷ byte 236 ∷ byte 91 ∷ byte 254 ∷ []
secondPayload = byte 69 ∷ byte 224 ∷ byte 191 ∷ byte 18 ∷ []

generated-tree-exact : generatedTree ≡
  (("candidates/alpha.bin" , firstPayload) ∷ ("candidates/beta.bin" , secondPayload) ∷ [])
generated-tree-exact = refl

generated-state-exact : proj₂ (runGen (genList 8 genByte) (mkSeed 42)) ≡ mkSeed 508781842
generated-state-exact = refl

fileConfig : FsConfig
fileConfig = fsConfig localSandbox [] (map proj₁ generatedTree) []

generatedFs : VirtualFs
generatedFs = initVirtualFs fileConfig (map proj₂ generatedTree)

transformedFs : VirtualFs
transformedFs = proj₁ (stepVirtualFs noopCmd
  (writeFileStep "candidates/alpha.bin" (reverse firstPayload)) generatedFs)

beforeSnapshot afterSnapshot : List FsEntryObs
beforeSnapshot = fsEntry "candidates" dirNode 493 []
  ∷ fsEntry "candidates/alpha.bin" regularNode 420 firstPayload
  ∷ fsEntry "candidates/beta.bin" regularNode 420 secondPayload ∷ []
afterSnapshot = fsEntry "candidates" dirNode 493 []
  ∷ fsEntry "candidates/alpha.bin" regularNode 420 (reverse firstPayload)
  ∷ fsEntry "candidates/beta.bin" regularNode 420 secondPayload ∷ []

generated-fs-tree : fsEntries generatedFs ≡ beforeSnapshot
generated-fs-tree = refl

binary-transform-snapshot : proj₂ (stepVirtualFs noopCmd snapshotStep transformedFs) ≡
  rawFsObs [] [] nothing false afterSnapshot
binary-transform-snapshot = refl

binary-transform-diff : diffSnapshot (fsEntries generatedFs) (fsEntries transformedFs) ≡
  (modified "candidates/alpha.bin" ∷ [])
binary-transform-diff = refl

entryBody : Maybe FsEntryObs → Bytes
entryBody nothing = []
entryBody (just e) = entryBytes e

-- Serve the bytes extracted from the transformed snapshot, not a new fixture.
artifact : Bytes
artifact = entryBody (lookupEntry "candidates/alpha.bin" (fsEntries transformedFs))

artifactRequest artifactResponse : Bytes
artifactRequest = encodeHttpReq "POST" "/artifact" [] firstPayload
artifactResponse = encodeHttpResp 200 "OK" [] artifact

artifactTopology : NetTopology
artifactTopology = httpStubMode (httpRoute "POST" "/artifact" 200 "OK" [] artifact ∷ [])

request-framing : parseHttpReq artifactRequest ≡ just (httpReqView "POST" "/artifact" firstPayload)
request-framing = refl

snapshot-response-framing : parseHttpResp artifactResponse ≡
  just (httpRespView 200 (byte 254 ∷ byte 91 ∷ byte 236 ∷ byte 129 ∷ []))
snapshot-response-framing = refl

snapshot-stub-capture : evalStubExchange artifactTopology (artifactRequest ∷ []) ≡
  (artifactRequest ∷ [] , artifactResponse ∷ [])
snapshot-stub-capture = refl

responseBody : Maybe HttpRespView → Bytes
responseBody nothing = []
responseBody (just response) = respBody response

repoConfig : GitConfig
repoConfig = gitConfig localSandbox "main" "Ext Probe" "ext@example.invalid"
  1700000000 [] (map proj₁ generatedTree)

generatedRepo committedRepo stagedRepo finalRepo : PureGitRepo
generatedRepo = initPureGit repoConfig (map proj₂ generatedTree)
committedRepo = runPureGit (gitStageAll ∷ gitCommit "generated candidates" 0 ∷ []) generatedRepo
stagedRepo = runPureGit
  (gitWriteFile "candidates/alpha.bin" (responseBody (parseHttpResp artifactResponse))
  ∷ gitStagePaths ("candidates/alpha.bin" ∷ []) ∷ []) committedRepo
finalRepo = runPureGit (gitCommit "served artifact" 1 ∷ []) stagedRepo

generated-git-tree : worktree generatedRepo ≡ generatedTree
generated-git-tree = refl

generated-git-commit : nthCommit 0 (commits committedRepo) ≡
  just (pureCommit nothing generatedTree "generated candidates" 1700000000)
generated-git-commit = refl

served-artifact-staged : projectSummary stagedRepo ≡
  gitSummary "main" 1 ("main" ∷ []) [] ("candidates/alpha.bin" ∷ []) [] []
served-artifact-staged = refl

-- End-to-end: seeded files, filesystem transformation, HTTP decoding and Git.
served-artifact-commit : nthCommit 1 (commits finalRepo) ≡ just
  (pureCommit (just 0)
    (("candidates/beta.bin" , secondPayload) ∷ ("candidates/alpha.bin" , reverse firstPayload) ∷ [])
    "served artifact" 1700000001)
served-artifact-commit = refl

final-clean-summary : projectSummary finalRepo ≡
  gitSummary "main" 2 ("main" ∷ []) [] [] [] []
final-clean-summary = refl

-- Staging snapshots content: a later working-tree edit cannot change the commit.
staging-is-a-snapshot : nthCommit 1 (commits (runPureGit
  (gitWriteFile "candidates/alpha.bin" firstPayload ∷ gitCommit "staged artifact" 2 ∷ []) stagedRepo)) ≡
  just (pureCommit (just 0)
    (("candidates/beta.bin" , secondPayload) ∷ ("candidates/alpha.bin" , reverse firstPayload) ∷ [])
    "staged artifact" 1700000002)
staging-is-a-snapshot = refl
