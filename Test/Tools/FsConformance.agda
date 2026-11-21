{-# OPTIONS --safe #-}
module Test.Tools.FsConformance where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Fin using () renaming (toℕ to octet)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _+_; _<ᵇ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox)
open import Context.Tools.FuzzGen
open import Context.Tools.FsSandbox

same-seed : runGen (genPair genBool (genBytes 4)) (mkSeed 42) ≡
  runGen (genPair genBool (genBytes 4)) (mkSeed 42)
same-seed = refl

first-draw : nextNat (mkSeed 42) ≡ (1083814273 , mkSeed 1083814273)
first-draw = refl

highByte : Gen Byte
highByte = genMap (λ n → byte (200 + n)) (genBounded 55)

below200 : Bytes → Bool
below200 [] = true
below200 (b ∷ bs) = (octet b <ᵇ 200) ∧ below200 bs

-- Generation really consumes the seed; three randomized high bytes shrink
-- through element deletion and scalar shrinking to the unique boundary 200.
minimal-counterexample : fuzzCheck 5 100 (genList 3 highByte) shrinkBytes below200 (mkSeed 42)
  ≡ just (byte 200 ∷ [])
minimal-counterexample = refl

minimal-still-fails : below200 (byte 200 ∷ []) ≡ false
minimal-still-fails = refl

minimal-candidates-pass : all below200 (shrinkBytes (byte 200 ∷ [])) ≡ true
minimal-candidates-pass = refl

passing-samples : fuzzCheck 8 10 (genMap (λ n → byte n ∷ []) (genBounded 199))
  shrinkBytes below200 (mkSeed 42) ≡ nothing
passing-samples = refl

reject-empty : validRelPath "" ≡ false
reject-empty = refl
reject-absolute : validRelPath "/abs" ≡ false
reject-absolute = refl
reject-escape : validRelPath "../esc" ≡ false
reject-escape = refl
reject-inner-escape : validRelPath "a/../b" ≡ false
reject-inner-escape = refl
reject-dot : validRelPath "a/./b" ≡ false
reject-dot = refl
reject-double-slash : validRelPath "a//b" ≡ false
reject-double-slash = refl
reject-final-slash : validRelPath "a/" ≡ false
reject-final-slash = refl
reject-nul : validRelPath "a\NULb" ≡ false
reject-nul = refl
reject-duplicates : noPathCollisions ("a" ∷ "a" ∷ []) ≡ false
reject-duplicates = refl
reject-prefix : noPathCollisions ("a" ∷ "a/b" ∷ []) ≡ false
reject-prefix = refl
reject-reverse-prefix : noPathCollisions ("a/b" ∷ "a" ∷ []) ≡ false
reject-reverse-prefix = refl
accept-nested : validRelPath "nested/data.bin" ≡ true
accept-nested = refl
accept-siblings : noPathCollisions ("a/b" ∷ "a/c" ∷ "ab" ∷ []) ≡ true
accept-siblings = refl
mask-permissions : maskMode 4095 ≡ 511
mask-permissions = refl
utf8-order : ltBytes (bytes "z") (bytes "é") ≡ true
utf8-order = refl

initialBytes finalOwnedBytes : Bytes
initialBytes = byte 0 ∷ byte 255 ∷ byte 128 ∷ byte 10 ∷ []
finalOwnedBytes = byte 255 ∷ byte 0 ∷ byte 1 ∷ byte 128 ∷ []

fsConfigFor : SandboxTarget → FsConfig
fsConfigFor t = fsConfig t [] ("data/owned.bin" ∷ [])
  (fixDir "fixture" 448 ∷ fixFile "fixture/seed.bin" 384 (byte 65 ∷ byte 0 ∷ byte 255 ∷ [])
  ∷ fixSymlink "links/esc" "../../../etc/passwd" ∷ fixFile "é.bin" 420 (bytes "λ") ∷ [])

conformanceSteps : List FsStep
conformanceSteps = writeFileStep "data/owned.bin" finalOwnedBytes
  ∷ mkdirStep "new/deep" 448 ∷ chmodStep "data/owned.bin" 384
  ∷ symlinkStep "links/current" "../data/owned.bin" ∷ snapshotStep
  ∷ unlinkStep "fixture/seed.bin" ∷ snapshotStep ∷ []

snapshotBefore : List FsEntryObs
snapshotBefore = fsEntry "data" dirNode 493 []
  ∷ fsEntry "data/owned.bin" regularNode 384 finalOwnedBytes
  ∷ fsEntry "fixture" dirNode 448 []
  ∷ fsEntry "fixture/seed.bin" regularNode 384 (byte 65 ∷ byte 0 ∷ byte 255 ∷ [])
  ∷ fsEntry "links" dirNode 493 []
  ∷ fsEntry "links/current" symlinkNode 511 (bytes "../data/owned.bin")
  ∷ fsEntry "links/esc" symlinkNode 511 (bytes "../../../etc/passwd")
  ∷ fsEntry "new" dirNode 493 [] ∷ fsEntry "new/deep" dirNode 448 []
  ∷ fsEntry "é.bin" regularNode 420 (bytes "λ") ∷ []

snapshotAfter : List FsEntryObs
snapshotAfter = fsEntry "data" dirNode 493 []
  ∷ fsEntry "data/owned.bin" regularNode 384 finalOwnedBytes
  ∷ fsEntry "fixture" dirNode 448 []
  ∷ fsEntry "links" dirNode 493 []
  ∷ fsEntry "links/current" symlinkNode 511 (bytes "../data/owned.bin")
  ∷ fsEntry "links/esc" symlinkNode 511 (bytes "../../../etc/passwd")
  ∷ fsEntry "new" dirNode 493 [] ∷ fsEntry "new/deep" dirNode 448 []
  ∷ fsEntry "é.bin" regularNode 420 (bytes "λ") ∷ []

expectedTrace : List RawFsObs
expectedTrace = emptyFsObs ∷ emptyFsObs ∷ emptyFsObs ∷ emptyFsObs
  ∷ rawFsObs [] [] nothing false snapshotBefore ∷ emptyFsObs
  ∷ rawFsObs [] [] nothing false snapshotAfter ∷ []

model-trace : traceVirtualFs noopCmd conformanceSteps
  (initVirtualFs (fsConfigFor localSandbox) (initialBytes ∷ [])) ≡ expectedTrace
model-trace = refl

snapshot-diff : diffSnapshot snapshotBefore snapshotAfter ≡ (removed "fixture/seed.bin" ∷ [])
snapshot-diff = refl

all-diff-kinds : diffSnapshot
  (fsEntry "a" regularNode 420 [] ∷ fsEntry "c" dirNode 493 [] ∷ [])
  (fsEntry "a" regularNode 384 [] ∷ fsEntry "b" symlinkNode 511 (bytes "a") ∷ [])
  ≡ (modified "a" ∷ added "b" ∷ removed "c" ∷ [])
all-diff-kinds = refl

write-preserves-mode : stepVirtualFs noopCmd (writeFileStep "file" finalOwnedBytes)
  (virtualFs (fsEntry "file" regularNode 384 initialBytes ∷ []))
  ≡ (virtualFs (fsEntry "file" regularNode 384 finalOwnedBytes ∷ []) , emptyFsObs)
write-preserves-mode = refl

symlink-ancestor-rejected : stepVirtualFs noopCmd (writeFileStep "sub/pwn" initialBytes)
  (virtualFs (fsEntry "sub" symlinkNode 511 (bytes "/tmp") ∷ []))
  ≡ (virtualFs (fsEntry "sub" symlinkNode 511 (bytes "/tmp") ∷ []) , rejectedFsObs)
symlink-ancestor-rejected = refl

symlink-leaf-rejected : stepVirtualFs noopCmd (writeFileStep "sub" initialBytes)
  (virtualFs (fsEntry "sub" symlinkNode 511 (bytes "/tmp") ∷ []))
  ≡ (virtualFs (fsEntry "sub" symlinkNode 511 (bytes "/tmp") ∷ []) , rejectedFsObs)
symlink-leaf-rejected = refl
