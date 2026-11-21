module OwnershipIO.Tools.WebFFI where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.String using (String)
import IO.Primitive as IO

data RawWebObs : Set where
  ack : RawWebObs
  frame : ℕ → ℕ → RawWebObs
  pixelObs : Bool → ℕ → ℕ → ℕ → RawWebObs

postulate
  WebHandle : Set
  openWeb : String → String → Bool → String → ℕ → ℕ →
            List String → List (List ℕ) → IO.IO WebHandle
  callWeb flushWeb : WebHandle → String → IO.IO RawWebObs
  stopWeb : WebHandle → IO.IO (List (List ℕ))

{-# FOREIGN GHC import qualified WebTransport as W #-}
{-# COMPILE GHC RawWebObs = data W.Wire (W.Ack | W.Frame | W.Pixel) #-}
{-# COMPILE GHC WebHandle = type W.WebHandle #-}
{-# COMPILE GHC openWeb = W.openWeb #-}
{-# COMPILE GHC callWeb = W.callWeb #-}
{-# COMPILE GHC flushWeb = W.flushWeb #-}
{-# COMPILE GHC stopWeb = W.stopWeb #-}
