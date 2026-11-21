-- Terminal-only trusted boundary; ordinary IO does not import this module.
module OwnershipIO.TermFFI where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.String using (String)
import IO.Primitive as IO

-- The FFI sees only primitive configuration, a resource handle, hex-framed raw
-- bytes and text files. No Key, Screen, Parser or TimedMachine crosses it.
data Wire : Set where
  wire : List ℕ → List ℕ → List ℕ → Maybe ℕ → Wire

postulate
  TermHandle : Set
  openTerm : String → String → Bool → String → Bool → String → List String → List String
    → ℕ → ℕ → List String → List String → IO.IO TermHandle
  openTermWithCand : String → String → String → Bool → String → Bool → String → List String → List String
    → ℕ → ℕ → List String → List String → IO.IO TermHandle
  callTerm : TermHandle → String → IO.IO Wire
  stopTerm : TermHandle → IO.IO (List String)
  transportError : ∀ {a} {A : Set a} → String → IO.IO A

{-# FOREIGN GHC import qualified TermTransport as TT #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC Wire = data TT.Wire (TT.Wire) #-}
{-# COMPILE GHC TermHandle = type TT.TermHandle #-}
{-# COMPILE GHC openTerm = TT.openTerm #-}
{-# COMPILE GHC openTermWithCand = TT.openTermWithCand #-}
{-# COMPILE GHC callTerm = TT.callTerm #-}
{-# COMPILE GHC stopTerm = TT.stopTerm #-}
{-# COMPILE GHC transportError = \ _ _ s -> ioError (userError (T.unpack s)) #-}
