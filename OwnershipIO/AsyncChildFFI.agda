------------------------------------------------------------------------
-- OwnershipIO/AsyncChildFFI.agda —— Non-blocking background `OfferIO` for sibling subpackages
--
-- Implements Dialectica §2.4 ("并发在 IO 层：onCall 不阻塞（圈在后台跑，催到就答）；
-- 封闭世界只看见催和答") without altering a single character of `Ownership.agda`.
--
-- Lifecycle & safety invariants:
-- 1. Upon child activation (`wakeChild` / `sendD task`), a dedicated background
--    thread drives `innerCall` turns until `just v` (`ok` or `contradiction c`).
-- 2. `onCall` is non-blocking: returns `just v` immediately when ready, or yields
--    briefly (5ms) and returns `nothing` while in flight so `pollKids` polls all
--    sibling channels concurrently with ~0% idle CPU.
-- 3. `onStop` (cancellation or harvest) atomically signals stop without holding
--    `stateVar`, sends `ThreadKilled` to interrupt any in-flight subprocess
--    (`withCreateProcess` reaps child OS processes on async exception), waits on
--    `workerDone` so zero concurrent state access can occur, and then runs the
--    child's own `innerStop` to cascade-stop grandchildren and return its `Home`.
------------------------------------------------------------------------
module OwnershipIO.AsyncChildFFI where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Unit using (⊤)

{-# FOREIGN GHC
import Control.Concurrent (ThreadId, forkIO, killThread, threadDelay)
import Control.Concurrent.MVar (MVar, newEmptyMVar, newMVar, putMVar, readMVar, swapMVar, takeMVar, modifyMVar_)
import qualified Control.Exception as E

data ChildState v
  = ChildWorking
  | ChildFinished v
  | ChildFailed E.SomeException

data AsyncChildHandle v m = AsyncChildHandle
  { acState      :: MVar (ChildState v)
  , acTid        :: MVar (Maybe ThreadId)
  , acWorkerDone :: MVar ()
  , acStopped    :: MVar Bool
  , acInnerStop  :: IO m
  }

spawnAsyncChildHS :: IO (Maybe v) -> IO m -> IO (AsyncChildHandle v m)
spawnAsyncChildHS stepCall innerStop = do
  stateVar   <- newMVar ChildWorking
  tidVar     <- newEmptyMVar
  workerDone <- newEmptyMVar
  stoppedVar <- newMVar False
  let loop = do
        res <- E.try stepCall
        case res of
          Left ex -> case E.fromException ex of
            Just E.ThreadKilled -> pure ()
            _ -> modifyMVar_ stateVar (\_ -> pure (ChildFailed ex))
          Right Nothing  -> loop
          Right (Just v) -> modifyMVar_ stateVar (\_ -> pure (ChildFinished v))
  tid <- forkIO (E.finally (readMVar tidVar >> loop) (putMVar workerDone ()))
  putMVar tidVar (Just tid)
  pure (AsyncChildHandle stateVar tidVar workerDone stoppedVar innerStop)

pollAsyncChildHS :: AsyncChildHandle v m -> () -> IO (Maybe v)
pollAsyncChildHS h _ = do
  stopped <- readMVar (acStopped h)
  if stopped then ioError (userError "asyncChild: called after stop") else do
    st <- readMVar (acState h)
    case st of
      ChildFinished v -> pure (Just v)
      ChildFailed ex  -> E.throwIO ex
      ChildWorking    -> do
        threadDelay 5000
        st2 <- readMVar (acState h)
        case st2 of
          ChildFinished v -> pure (Just v)
          ChildFailed ex  -> E.throwIO ex
          ChildWorking    -> pure Nothing

stopAsyncChildHS :: AsyncChildHandle v m -> IO m
stopAsyncChildHS h = do
  already <- swapMVar (acStopped h) True
  if already then ioError (userError "asyncChild: stopped twice") else do
    st <- readMVar (acState h)
    case st of
      ChildWorking -> do
        mtid <- readMVar (acTid h)
        case mtid of
          Just tid -> killThread tid
          Nothing  -> pure ()
      _ -> pure ()
    takeMVar (acWorkerDone h)
    stFinal <- readMVar (acState h)
    case stFinal of
      ChildFailed ex -> do
        E.catch (acInnerStop h >> pure ()) (\e -> let _ = e :: E.SomeException in pure ())
        E.throwIO ex
      _ -> acInnerStop h
#-}

postulate
  AsyncChildHandle : Set → Set → Set
  spawnAsyncChild  : ∀ {V M : Set} → IO (Maybe V) → IO M → IO (AsyncChildHandle V M)
  pollAsyncChild   : ∀ {V M : Set} → AsyncChildHandle V M → ⊤ → IO (Maybe V)
  stopAsyncChild   : ∀ {V M : Set} → AsyncChildHandle V M → IO M

{-# COMPILE GHC AsyncChildHandle = type AsyncChildHandle #-}
{-# COMPILE GHC spawnAsyncChild  = \ _ _ -> spawnAsyncChildHS #-}
{-# COMPILE GHC pollAsyncChild   = \ _ _ -> pollAsyncChildHS #-}
{-# COMPILE GHC stopAsyncChild   = \ _ _ -> stopAsyncChildHS #-}
