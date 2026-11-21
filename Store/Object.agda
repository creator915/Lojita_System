{-# OPTIONS --safe #-}
module Store.Object where

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Char.Base using (Char; toℕ)
open import Data.List.Base using (List; []; _∷_; all; foldr; length; map)
open import Data.Maybe.Base using (Maybe; nothing; just; _>>=_; when)
open import Data.Nat.Base using (_≡ᵇ_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String.Base using (String; toList)
open import Data.String.Properties using (_<?_)
open import Relation.Nullary using (does)

Hash : Set
Hash = String

validHash : Hash → Bool
validHash h = (length (toList h) ≡ᵇ 64) ∧ all hex (toList h)
  where
  hex : Char → Bool
  hex c = let n = toℕ c in ((48 ≤ᵇ n) ∧ (n ≤ᵇ 57)) ∨ ((97 ≤ᵇ n) ∧ (n ≤ᵇ 102))

Kid : Set
Kid = String × Hash

record HomeNodeObj : Set where
  constructor homeNode
  field
    codeHash specHash memHash : Hash
    kids : List Kid
open HomeNodeObj public

record CommitObj : Set where
  constructor commitWithView
  field
    parents : List Hash
    rootHome : Hash
    epoch why : String
    presentation : Maybe Hash
open CommitObj public

pattern commit ps h e w = commitWithView ps h e w nothing

sortKids : List Kid → List Kid
sortKids = foldr insert []
  where
  insert : Kid → List Kid → List Kid
  insert k [] = k ∷ []
  insert k (j ∷ js) = if does (proj₁ j <? proj₁ k)
    then j ∷ insert k js else k ∷ j ∷ js

-- The metadata grammar uses only quoted strings and tagged S-expressions.
-- Its text reader/printer and the existing AST codecs are supplied by CAS,
-- so this module can be checked independently under --safe.
data Form : Set where
  quoted : String → Form
  tagged : String → List Form → Form

private
  traverse : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
  traverse f [] = just []
  traverse f (x ∷ xs) = f x >>= λ y → traverse f xs >>= λ ys → just (y ∷ ys)

  hashField : Form → Maybe Hash
  hashField (quoted h) = when (validHash h) h
  hashField _ = nothing

  kidField : Kid → Form
  kidField (n , h) = tagged "kid" (quoted n ∷ quoted h ∷ [])

  readKid : Form → Maybe Kid
  readKid (tagged "kid" (quoted n ∷ h ∷ [])) = hashField h >>= λ key → just (n , key)
  readKid _ = nothing

  -- Strict ordering also rules out two children claiming the same slot.
  ordered : List Kid → Bool
  ordered ((a , _) ∷ k ∷ ks) = does (a <? proj₁ k) ∧ ordered (k ∷ ks)
  ordered _ = true

homeForm : HomeNodeObj → Form
homeForm (homeNode c s m ks) =
  tagged "home" (quoted c ∷ quoted s ∷ quoted m ∷ map kidField (sortKids ks))

readHomeForm : Form → Maybe HomeNodeObj
readHomeForm (tagged "home" (c ∷ s ∷ m ∷ ks)) = do
  ch ← hashField c
  sh ← hashField s
  mh ← hashField m
  children ← traverse readKid ks
  when (ordered children) (homeNode ch sh mh children)
readHomeForm _ = nothing

commitForm : CommitObj → Form
commitForm (commitWithView ps root e w view) =
  tagged "commit" (tagged "parents" (map quoted ps) ∷ quoted root ∷ quoted e ∷ quoted w ∷ extra view)
  where
    extra : Maybe Hash → List Form
    extra nothing = []
    extra (just h) = tagged "presentation" (quoted h ∷ []) ∷ []

readCommitForm : Form → Maybe CommitObj
readCommitForm (tagged "commit" (tagged "parents" ps ∷ r ∷ quoted e ∷ quoted w ∷ rest)) = do
  root ← hashField r
  hs ← traverse hashField ps
  view ← extra rest
  just (commitWithView hs root e w view)
  where
    extra : List Form → Maybe (Maybe Hash)
    extra [] = just nothing
    extra (tagged "presentation" (h ∷ []) ∷ []) = Data.Maybe.Base.map just (hashField h)
    extra _ = nothing
readCommitForm _ = nothing

data Kind : Set where
  codeK ifaceK memK homeK commitK : Kind

kindName : Kind → String
kindName codeK = "code"
kindName ifaceK = "iface"
kindName memK = "mem"
kindName homeK = "home"
kindName commitK = "commit"

record Format (A : Set) : Set where
  constructor format
  field
    encode : A → String
    parseValue : String → Maybe A
open Format public

-- The repository parsers also accept presentation syntax. Only canonical
-- bytes are objects, even when an alternative spelling has its own valid hash.
decode : ∀ {A} → Format A → String → Maybe A
decode f bytes = parseValue f bytes >>= λ a → when (primStringEquality (encode f a) bytes) a

module Objects {Code Interface Memory : Set}
               (codeFormat : Format Code) (ifaceFormat : Format Interface)
               (memFormat : Format Memory) (wire : Format Form) where
  CodeBlob IfaceBlob MemBlob : Set
  CodeBlob = Code
  IfaceBlob = Interface
  MemBlob = Memory

  Payload : Kind → Set
  Payload codeK = CodeBlob
  Payload ifaceK = IfaceBlob
  Payload memK = MemBlob
  Payload homeK = HomeNodeObj
  Payload commitK = CommitObj

  objectFormat : (k : Kind) → Format (Payload k)
  objectFormat codeK = codeFormat
  objectFormat ifaceK = ifaceFormat
  objectFormat memK = memFormat
  objectFormat homeK = format (λ h → encode wire (homeForm h))
                              (λ s → parseValue wire s >>= readHomeForm)
  objectFormat commitK = format (λ c → encode wire (commitForm c))
                                (λ s → parseValue wire s >>= readCommitForm)

  encodeCodeBlob = encode codeFormat
  decodeCodeBlob = decode codeFormat
  encodeIfaceBlob = encode ifaceFormat
  decodeIfaceBlob = decode ifaceFormat
  encodeMemBlob = encode memFormat
  decodeMemBlob = decode memFormat
  encodeHomeNode = encode (objectFormat homeK)
  decodeHomeNode = decode (objectFormat homeK)
  encodeCommit = encode (objectFormat commitK)
  decodeCommit = decode (objectFormat commitK)
