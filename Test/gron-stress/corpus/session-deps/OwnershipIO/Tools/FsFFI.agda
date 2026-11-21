-- All filesystem host bindings live at this explicit trusted boundary.
module OwnershipIO.Tools.FsFFI where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.String using (String)
import IO.Primitive as IO

data Fixture : Set where
  wireDir : String → ℕ → Fixture
  wireFile : String → ℕ → List ℕ → Fixture
  wireSymlink : String → String → Fixture

data Entry : Set where
  wireEntry : String → ℕ → ℕ → List ℕ → Entry

data Wire : Set where
  wire : List ℕ → List ℕ → Maybe ℕ → Bool → List Entry → Wire

postulate
  FsHandle : Set
  openFs : String → String → Bool → String → List String → List String
    → List (List ℕ) → List Fixture → IO.IO FsHandle
  openFsWithCand : String → String → String → Bool → String → List String → List String
    → List (List ℕ) → List Fixture → IO.IO FsHandle
  callFs : FsHandle → String → IO.IO Wire
  stopFs : FsHandle → IO.IO (List (List ℕ))
  localOnly : IO.IO Bool
  clockMs : IO.IO ℕ
  transportError : ∀ {a} {A : Set a} → String → IO.IO A

{-# FOREIGN GHC import qualified FsTransport as FS #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified GHC.Clock as Clock #-}
{-# COMPILE GHC Fixture = data FS.Fixture (FS.FixDir | FS.FixFile | FS.FixSymlink) #-}
{-# COMPILE GHC Entry = data FS.Entry (FS.Entry) #-}
{-# COMPILE GHC Wire = data FS.Wire (FS.Wire) #-}
{-# COMPILE GHC FsHandle = type FS.FsHandle #-}
{-# COMPILE GHC openFs = FS.openFs #-}
{-# COMPILE GHC openFsWithCand = FS.openFsWithCand #-}
{-# COMPILE GHC callFs = FS.callFs #-}
{-# COMPILE GHC stopFs = FS.stopFs #-}
{-# COMPILE GHC localOnly = FS.localOnly #-}
{-# COMPILE GHC clockMs = fmap (\ n -> toInteger n `div` 1000000) Clock.getMonotonicTimeNSec #-}
{-# COMPILE GHC transportError = \ _ _ s -> ioError (userError (T.unpack s)) #-}
