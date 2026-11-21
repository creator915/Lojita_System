{-# OPTIONS --safe #-}
module Context.Tools.FsSandbox where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char; toℕ)
open import Data.Fin using () renaming (toℕ to octet)
open import Data.List using (List; []; _∷_; _++_; map; reverse; foldl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList; fromList) renaming (_++_ to _++ˢ_)
open import Context.Terminal using (Byte; Bytes; byte; bytes; SandboxTarget; localSandbox; dockerSandbox)

eqChars : List Char → List Char → Bool
eqChars []       []       = true
eqChars (c ∷ cs) (d ∷ ds) = (toℕ c ≡ᵇ toℕ d) ∧ eqChars cs ds
eqChars _        _        = false

eqStr : String → String → Bool
eqStr a b = eqChars (toList a) (toList b)

splitSegmentChars : List Char → List Char → List (List Char)
splitSegmentChars acc [] = reverse acc ∷ []
splitSegmentChars acc (c ∷ cs) = if toℕ c ≡ᵇ 47
  then reverse acc ∷ splitSegmentChars [] cs
  else splitSegmentChars (c ∷ acc) cs

segments : String → List String
segments p = map fromList (splitSegmentChars [] (toList p))

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all f [] = true
all f (x ∷ xs) = f x ∧ all f xs

validSegChars : List Char → Bool
validSegChars cs = not (eqChars cs []) ∧ not (eqChars cs ('.' ∷ []))
  ∧ not (eqChars cs ('.' ∷ '.' ∷ []))

validSegment : String → Bool
validSegment s = validSegChars (toList s)

validRelPath : String → Bool
validRelPath p = all validSegChars (splitSegmentChars [] (toList p))
  ∧ all (λ c → not (toℕ c ≡ᵇ 0)) (toList p)

eqBytes : Bytes → Bytes → Bool
eqBytes [] [] = true
eqBytes (a ∷ as) (b ∷ bs) = (octet a ≡ᵇ octet b) ∧ eqBytes as bs
eqBytes _ _ = false

ltBytes : Bytes → Bytes → Bool
ltBytes [] [] = false
ltBytes [] (_ ∷ _) = true
ltBytes (_ ∷ _) [] = false
ltBytes (a ∷ as) (b ∷ bs) = if octet a ≡ᵇ octet b then ltBytes as bs else octet a <ᵇ octet b

prefixBytes : Bytes → Bytes → Bool
prefixBytes [] _ = true
prefixBytes (_ ∷ _) [] = false
prefixBytes (a ∷ as) (b ∷ bs) = (octet a ≡ᵇ octet b) ∧ prefixBytes as bs

isParent : String → String → Bool
isParent p q = prefixBytes (bytes (p ++ˢ "/")) (bytes q)

collide : String → String → Bool
collide p q = eqStr p q ∨ isParent p q ∨ isParent q p

noPathCollisions : List String → Bool
noPathCollisions [] = true
noPathCollisions (p ∷ ps) = validRelPath p ∧ all (λ q → not (collide p q)) ps ∧ noPathCollisions ps

maskMode : ℕ → ℕ
maskMode n = n % 512

data FsNodeKind : Set where
  regularNode dirNode symlinkNode : FsNodeKind

data FsFixture : Set where
  fixDir : String → ℕ → FsFixture
  fixFile : String → ℕ → Bytes → FsFixture
  fixSymlink : String → String → FsFixture

record FsConfig : Set where
  constructor fsConfig
  field
    target : SandboxTarget
    envVars : List (String × String)
    ownedFiles : List String
    fixtures : List FsFixture
open FsConfig public

data FsStep : Set where
  runCmd : String → List String → Bytes → ℕ → FsStep
  writeFileStep : String → Bytes → FsStep
  mkdirStep : String → ℕ → FsStep
  symlinkStep : String → String → FsStep
  chmodStep : String → ℕ → FsStep
  unlinkStep : String → FsStep
  snapshotStep : FsStep

record FsEntryObs : Set where
  constructor fsEntry
  field
    entryPath : String
    entryKind : FsNodeKind
    entryMode : ℕ
    entryBytes : Bytes
open FsEntryObs public

record RawFsObs : Set where
  constructor rawFsObs
  field
    stdoutOut stderrOut : Bytes
    exitStatus : Maybe ℕ
    timedOut : Bool
    entries : List FsEntryObs
open RawFsObs public

emptyFsObs : RawFsObs
emptyFsObs = rawFsObs [] [] nothing false []

rejectedFsObs : RawFsObs
rejectedFsObs = rawFsObs [] (bytes "filesystem operation rejected") (just 1) false []

eqKind : FsNodeKind → FsNodeKind → Bool
eqKind regularNode regularNode = true
eqKind dirNode dirNode = true
eqKind symlinkNode symlinkNode = true
eqKind _ _ = false

eqEntry : FsEntryObs → FsEntryObs → Bool
eqEntry a b = eqStr (entryPath a) (entryPath b)
  ∧ eqKind (entryKind a) (entryKind b) ∧ (entryMode a ≡ᵇ entryMode b) ∧ eqBytes (entryBytes a) (entryBytes b)

eqEntries : List FsEntryObs → List FsEntryObs → Bool
eqEntries [] [] = true
eqEntries (a ∷ as) (b ∷ bs) = eqEntry a b ∧ eqEntries as bs
eqEntries _ _ = false

eqExit : Maybe ℕ → Maybe ℕ → Bool
eqExit nothing nothing = true
eqExit (just a) (just b) = a ≡ᵇ b
eqExit _ _ = false

eqBool : Bool → Bool → Bool
eqBool true true = true
eqBool false false = true
eqBool _ _ = false

eqObs : RawFsObs → RawFsObs → Bool
eqObs a b = eqBytes (stdoutOut a) (stdoutOut b) ∧ eqBytes (stderrOut a) (stderrOut b)
  ∧ eqExit (exitStatus a) (exitStatus b) ∧ eqBool (timedOut a) (timedOut b) ∧ eqEntries (entries a) (entries b)

eqTrace : List RawFsObs → List RawFsObs → Bool
eqTrace [] [] = true
eqTrace (a ∷ as) (b ∷ bs) = eqObs a b ∧ eqTrace as bs
eqTrace _ _ = false

-- Invariant: one entry per path, ordered by UTF-8 octets, implicit parents
-- represented explicitly. The model abstracts permissions as metadata; syscall
-- permission failures in a real sandbox remain observable errors.
record VirtualFs : Set where
  constructor virtualFs
  field fsEntries : List FsEntryObs
open VirtualFs public

lookupEntry : String → List FsEntryObs → Maybe FsEntryObs
lookupEntry p [] = nothing
lookupEntry p (e ∷ es) = if eqStr p (entryPath e) then just e else lookupEntry p es

insertEntry : FsEntryObs → List FsEntryObs → List FsEntryObs
insertEntry e [] = e ∷ []
insertEntry e (x ∷ xs) = if eqStr (entryPath e) (entryPath x) then e ∷ xs else
  if ltBytes (bytes (entryPath e)) (bytes (entryPath x)) then e ∷ x ∷ xs else x ∷ insertEntry e xs

removeEntry : String → List FsEntryObs → List FsEntryObs
removeEntry p [] = []
removeEntry p (x ∷ xs) = if eqStr p (entryPath x) then xs else x ∷ removeEntry p xs

putEntry : FsEntryObs → VirtualFs → VirtualFs
putEntry e v = virtualFs (insertEntry e (fsEntries v))

joinPart : String → String → String
joinPart "" q = q
joinPart p q = p ++ˢ "/" ++ˢ q

parentsFrom : String → List String → List String
parentsFrom p [] = []
parentsFrom p (x ∷ []) = []
parentsFrom p (x ∷ y ∷ xs) = joinPart p x ∷ parentsFrom (joinPart p x) (y ∷ xs)

parentPaths : String → List String
parentPaths p = parentsFrom "" (segments p)

ensureParents : Bool → List String → VirtualFs → Maybe VirtualFs
ensureParents create [] v = just v
ensureParents create (p ∷ ps) v with lookupEntry p (fsEntries v)
... | just e = if eqKind (entryKind e) dirNode then ensureParents create ps v else nothing
... | nothing = if create then ensureParents create ps (putEntry (fsEntry p dirNode 493 []) v) else nothing

prepare : Bool → String → VirtualFs → Maybe VirtualFs
prepare create p v = if validRelPath p then ensureParents create (parentPaths p) v else nothing

writeLeaf : String → Bytes → VirtualFs → Maybe VirtualFs
writeLeaf p bs v with lookupEntry p (fsEntries v)
... | nothing = just (putEntry (fsEntry p regularNode 420 bs) v)
... | just e = if eqKind (entryKind e) regularNode then
  just (putEntry (fsEntry p regularNode (entryMode e) bs) v) else nothing

mkdirLeaf : String → ℕ → VirtualFs → Maybe VirtualFs
mkdirLeaf p mode v with lookupEntry p (fsEntries v)
... | nothing = just (putEntry (fsEntry p dirNode (maskMode mode) []) v)
... | just e = if eqKind (entryKind e) dirNode then
  just (putEntry (fsEntry p dirNode (maskMode mode) []) v) else nothing

linkLeaf : String → String → VirtualFs → Maybe VirtualFs
linkLeaf p dest v with lookupEntry p (fsEntries v)
... | nothing = just (putEntry (fsEntry p symlinkNode 511 (bytes dest)) v)
... | just e = if eqKind (entryKind e) dirNode then nothing
  else just (putEntry (fsEntry p symlinkNode 511 (bytes dest)) v)

chmodLeaf : String → ℕ → VirtualFs → Maybe VirtualFs
chmodLeaf p mode v with lookupEntry p (fsEntries v)
... | nothing = nothing
... | just e = if eqKind (entryKind e) symlinkNode then nothing
  else just (putEntry (fsEntry p (entryKind e) (maskMode mode) (entryBytes e)) v)

unlinkLeaf : String → VirtualFs → Maybe VirtualFs
unlinkLeaf p v with lookupEntry p (fsEntries v)
... | nothing = nothing
... | just e = if all (λ x → not (isParent p (entryPath x))) (fsEntries v)
  then just (virtualFs (removeEntry p (fsEntries v))) else nothing

bindMaybe : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindMaybe nothing f = nothing
bindMaybe (just x) f = f x

applyFs : FsStep → VirtualFs → Maybe VirtualFs
applyFs (writeFileStep p bs) v = bindMaybe (prepare true p v) (writeLeaf p bs)
applyFs (mkdirStep p mode) v = bindMaybe (prepare true p v) (mkdirLeaf p mode)
applyFs (symlinkStep p dest) v = if all (λ c → not (toℕ c ≡ᵇ 0)) (toList dest)
  ∧ not (eqStr dest "") then bindMaybe (prepare true p v) (linkLeaf p dest) else nothing
applyFs (chmodStep p mode) v = bindMaybe (prepare false p v) (chmodLeaf p mode)
applyFs (unlinkStep p) v = bindMaybe (prepare false p v) (unlinkLeaf p)
applyFs _ v = just v

CmdSemantics : Set
CmdSemantics = String → List String → Bytes → ℕ → VirtualFs → VirtualFs × Bytes × Bytes × ℕ × Bool

noopCmd : CmdSemantics
noopCmd cmd args input ms v = v , [] , [] , 0 , false

finishFs : VirtualFs → Maybe VirtualFs → VirtualFs × RawFsObs
finishFs old nothing = old , rejectedFsObs
finishFs old (just next) = next , emptyFsObs

stepVirtualFs : CmdSemantics → FsStep → VirtualFs → VirtualFs × RawFsObs
stepVirtualFs cmd (runCmd exe args input ms) v with cmd exe args input ms v
... | next , out , err , status , timeout = next , rawFsObs out err (just status) timeout []
stepVirtualFs cmd snapshotStep v = v , rawFsObs [] [] nothing false (fsEntries v)
stepVirtualFs cmd q v = finishFs v (applyFs q v)

traceVirtualFs : CmdSemantics → List FsStep → VirtualFs → List RawFsObs
traceVirtualFs cmd [] v = []
traceVirtualFs cmd (q ∷ qs) v with stepVirtualFs cmd q v
... | next , o = o ∷ traceVirtualFs cmd qs next

retain : VirtualFs → Maybe VirtualFs → VirtualFs
retain old nothing = old
retain old (just v) = v

initOwned : List String → List Bytes → VirtualFs → VirtualFs
initOwned [] bs v = v
initOwned (p ∷ ps) [] v = initOwned ps [] (retain v (applyFs (writeFileStep p []) v))
initOwned (p ∷ ps) (b ∷ bs) v = initOwned ps bs (retain v (applyFs (writeFileStep p b) v))

initDirs : List FsFixture → VirtualFs → VirtualFs
initDirs [] v = v
initDirs (fixDir p mode ∷ fs) v = initDirs fs (retain v (applyFs (mkdirStep p mode) v))
initDirs (_ ∷ fs) v = initDirs fs v

initFixtures : List FsFixture → VirtualFs → VirtualFs
initFixtures [] v = v
initFixtures (fixFile p mode bs ∷ fs) v = initFixtures fs
  (retain v (bindMaybe (applyFs (writeFileStep p bs) v) (chmodLeaf p mode)))
initFixtures (fixSymlink p dest ∷ fs) v = initFixtures fs (retain v (applyFs (symlinkStep p dest) v))
initFixtures (_ ∷ fs) v = initFixtures fs v

initVirtualFs : FsConfig → List Bytes → VirtualFs
initVirtualFs cfg contents = initFixtures (fixtures cfg)
  (initOwned (ownedFiles cfg) contents (initDirs (fixtures cfg) (virtualFs [])))

data FsDiff : Set where
  added modified removed : String → FsDiff

-- Inputs are snapshots in UTF-8 path order; output uses that same order.
diffSnapshot : List FsEntryObs → List FsEntryObs → List FsDiff
diffSnapshot [] ys = map (λ y → added (entryPath y)) ys
diffSnapshot xs [] = map (λ x → removed (entryPath x)) xs
diffSnapshot (x ∷ xs) (y ∷ ys) = if eqStr (entryPath x) (entryPath y)
  then (if eqEntry x y then [] else modified (entryPath x) ∷ []) ++ diffSnapshot xs ys
  else if ltBytes (bytes (entryPath x)) (bytes (entryPath y))
    then removed (entryPath x) ∷ diffSnapshot xs (y ∷ ys)
    else added (entryPath y) ∷ diffSnapshot (x ∷ xs) ys
