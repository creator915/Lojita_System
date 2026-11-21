-- The only trusted host boundary of the network tool.
module OwnershipIO.Tools.NetFFI where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.String using (String)
import IO.Primitive as IO

data Route : Set where
  wireRoute : String → String → List ℕ → Route

data Rule : Set where
  wireRule : List ℕ → List ℕ → Rule

data Topology : Set where
  wireHttp : List ℕ → List Route → Topology
  wireTcp : List Rule → Topology
  wireUdp : List Rule → Topology
  wireDaemon : String → List String → Topology
  wireHttpDelayed : ℕ → List ℕ → List Route → Topology
  wireTcpDelayed : ℕ → List Rule → Topology

data Wire : Set where
  wire : List ℕ → List ℕ → List ℕ → List (List ℕ) → Maybe ℕ → Bool → Wire

postulate
  NetHandle : Set
  openNet : String → String → Bool → String → List String → List String
    → List (List ℕ) → Topology → IO.IO NetHandle
  openNetWithCand : String → String → String → Bool → String → List String → List String
    → List (List ℕ) → Topology → IO.IO NetHandle
  callNet : NetHandle → String → IO.IO Wire
  stopNet : NetHandle → IO.IO (List (List ℕ))
  localOnly : IO.IO Bool
  clockMs : IO.IO ℕ
  transportError : ∀ {a} {A : Set a} → String → IO.IO A

{-# FOREIGN GHC import qualified NetTransport as NET #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified GHC.Clock as Clock #-}
{-# COMPILE GHC Route = data NET.Route (NET.Route) #-}
{-# COMPILE GHC Rule = data NET.Rule (NET.Rule) #-}
{-# COMPILE GHC Topology = data NET.Topology (NET.HttpStub | NET.TcpStub | NET.UdpStub | NET.Daemon | NET.HttpDelayedStub | NET.TcpDelayedStub) #-}
{-# COMPILE GHC Wire = data NET.Wire (NET.Wire) #-}
{-# COMPILE GHC NetHandle = type NET.NetHandle #-}
{-# COMPILE GHC openNet = NET.openNet #-}
{-# COMPILE GHC openNetWithCand = NET.openNetWithCand #-}
{-# COMPILE GHC callNet = NET.callNet #-}
{-# COMPILE GHC stopNet = NET.stopNet #-}
{-# COMPILE GHC localOnly = NET.localOnly #-}
{-# COMPILE GHC clockMs = fmap (\ n -> toInteger n `div` 1000000) Clock.getMonotonicTimeNSec #-}
{-# COMPILE GHC transportError = \ _ _ s -> ioError (userError (T.unpack s)) #-}
