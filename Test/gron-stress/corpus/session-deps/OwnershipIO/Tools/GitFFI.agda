-- The only trusted Git host boundary. Wire octets are checked by the transport.
module OwnershipIO.Tools.GitFFI where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.String using (String)
import IO.Primitive as IO

data Summary : Set where
  wireSummary : String → ℕ → List String → List String → List String
    → List String → List String → Summary

data Wire : Set where
  wire : List ℕ → List ℕ → String → Maybe ℕ → Bool → Maybe Summary → Wire

postulate
  GitHandle : Set
  openGit : String → String → Bool → String → String → String → String → ℕ
    → List String → List String → List (List ℕ) → IO.IO GitHandle
  openGitWithCand : String → String → String → Bool → String → String → String → String → ℕ
    → List String → List String → List (List ℕ) → IO.IO GitHandle
  callGit : GitHandle → String → IO.IO Wire
  stopGit : GitHandle → IO.IO (List (List ℕ))
  localOnly : IO.IO Bool
  transportError : ∀ {a} {A : Set a} → String → IO.IO A

{-# FOREIGN GHC import qualified GitTransport as Git #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC Summary = data Git.Summary (Git.Summary) #-}
{-# COMPILE GHC Wire = data Git.Wire (Git.Wire) #-}
{-# COMPILE GHC GitHandle = type Git.GitHandle #-}
{-# COMPILE GHC openGit = Git.openGit #-}
{-# COMPILE GHC openGitWithCand = Git.openGitWithCand #-}
{-# COMPILE GHC callGit = Git.callGit #-}
{-# COMPILE GHC stopGit = Git.stopGit #-}
{-# COMPILE GHC localOnly = Git.localOnly #-}
{-# COMPILE GHC transportError = \ _ _ s -> ioError (userError (T.unpack s)) #-}
