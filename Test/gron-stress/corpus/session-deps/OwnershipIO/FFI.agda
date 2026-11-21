------------------------------------------------------------------------
-- OwnershipIO/FFI.agda —— IO 层对 Haskell 的几条绑定
--
-- 内核（Ownership.agda、Code*.agda）一条公理也没有。IO 层得碰真世界，真世界在 Haskell 那边：
-- 可变引用（服务句柄的隐藏状态）、目录、起进程。这里与 TermFFI 是受信任的 FFI 边界，
-- 性质和 stdlib 的 IO.Primitive 一样：说的是"Haskell 里有这么个东西"，不是数学公理。
-- 都是 GHC 自带的包（base、directory、process），agda --compile 直接能用。
------------------------------------------------------------------------
module OwnershipIO.FFI where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Unit using (⊤)



{-# FOREIGN GHC
import qualified Data.IORef as R
import qualified System.Directory as D
import qualified Data.List as L
import qualified System.Process as P
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Exit (ExitCode(..))
import qualified System.Exit
import qualified Control.Exception as E
import qualified System.Timeout as Timeout
import qualified System.IO as H
import System.IO.Error (isDoesNotExistError)
import qualified System.FilePath as FP
import qualified Data.ByteString as BS
import qualified Data.Text.Encoding as TE
import qualified Data.Aeson as J
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import qualified Data.Vector as V
import qualified Control.Monad.Fix as MF
import GHC.IO.Encoding (setLocaleEncoding, utf8)

-- 第一个参数吃掉 Agda 的 Level
type IORefL l a = R.IORef a

data ProcResult = ProcResult Integer T.Text T.Text

runProc :: T.Text -> [T.Text] -> T.Text -> IO ProcResult
runProc cmd args inp = do
  (c, o, e) <- P.readProcessWithExitCode (T.unpack cmd) (map T.unpack args) (T.unpack inp)
  return (ProcResult (code c) (T.pack o) (T.pack e))
  where code ExitSuccess     = 0
        code (ExitFailure n) = fromIntegral n

runProcAt :: T.Text -> Integer -> T.Text -> [T.Text] -> T.Text -> IO ProcResult
runProcAt dir ms cmd args inp = E.catch action handler
  where
    action = do
      let cp = (P.proc (T.unpack cmd) (map T.unpack args))
                 { P.cwd = if T.null dir then Nothing else Just (T.unpack dir) }
          wait = P.readCreateProcessWithExitCode cp (T.unpack inp)
      result <- if ms == 0 then fmap Just wait else Timeout.timeout (fromInteger (ms * 1000)) wait
      return $ case result of
        Nothing -> ProcResult 124 T.empty (T.pack "process timeout")
        Just (c,o,e) -> ProcResult (case c of ExitSuccess -> 0; ExitFailure n -> fromIntegral n) (T.pack o) (T.pack e)
    handler :: E.IOException -> IO ProcResult
    handler e = return (ProcResult 127 T.empty (T.pack (show e)))

shaText :: T.Text -> IO T.Text
shaText txt = do
  -- sha256sum is used on bytes, avoiding locale-dependent text encoding.
  root <- D.getTemporaryDirectory
  E.bracket (H.openBinaryTempFile root "codetransport-sha")
    (\(p,h) -> E.catch (H.hClose h) (\e -> let _ = e :: E.IOException in return ()) >> D.removeFile p)
    (\(p,h) -> do
      BS.hPut h (TE.encodeUtf8 txt)
      H.hClose h
      (c,o,e) <- P.readProcessWithExitCode "sha256sum" [p] ""
      case c of
        ExitSuccess -> return (T.pack (take 64 o))
        _ -> ioError (userError e))

freshDir :: T.Text -> IO T.Text
freshDir parent = do
  D.createDirectoryIfMissing True (T.unpack parent)
  (p,h) <- H.openTempFile (T.unpack parent) "codetransport-"
  H.hClose h
  D.removeFile p
  D.createDirectory p
  return (T.pack p)

-- removePathForcibly chmods symbolic-link targets on some directory versions.
-- Temporary include views must unlink links without touching their targets.
removeTree :: FilePath -> IO ()
removeTree path = E.catch action handler
  where
    action = do
      linked <- D.pathIsSymbolicLink path
      if linked then D.removeFile path else do
        directory <- D.doesDirectoryExist path
        if directory then do
          D.listDirectory path >>= mapM_ (removeTree . (path FP.</>))
          D.removeDirectory path
        else D.removeFile path
    handler :: E.IOException -> IO ()
    handler e = if isDoesNotExistError e then return () else E.throwIO e

findString :: T.Text -> J.Value -> Maybe T.Text
findString key (J.Object o) = case KM.lookup (K.fromText key) o of
  Just (J.String s) -> Just s
  _ -> firstJust (map (findString key) (KM.elems o))
findString key (J.Array a) = firstJust (map (findString key) (V.toList a))
findString _ _ = Nothing
firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just a:_) = Just a
firstJust (_:xs) = firstJust xs
jsonField :: T.Text -> T.Text -> T.Text
jsonField key txt = maybe T.empty id (firstJust [J.decodeStrict (TE.encodeUtf8 line) >>= findString key | line <- txt : T.lines txt])

enableLineBuf :: IO ()
enableLineBuf = do
  setLocaleEncoding utf8
  H.hSetEncoding H.stdin utf8
  H.hSetEncoding H.stdout utf8
  H.hSetEncoding H.stderr utf8
  H.hSetBuffering H.stdout H.LineBuffering
  H.hSetBuffering H.stderr H.LineBuffering

-- Strip benign Cubical Agda warnings serialized inside /usr/share/agda-stdlib
-- .agdai files, while preserving every user diagnostic and non-stdlib line.
cleanAgdaOutput :: T.Text -> T.Text
cleanAgdaOutput = T.unlines . go . T.lines
  where
    stdlibPrefix = T.pack "/usr/share/agda-stdlib/"
    cubicalHeader = T.pack "This clause uses pattern-matching features that are not yet"
    whenDef = T.pack "when checking the definition of"
    whenDefSpace = T.pack "when checking the definition of "

    go [] = []
    go (l : rest@(l2 : _))
      | T.isPrefixOf stdlibPrefix l && T.isPrefixOf cubicalHeader l2 = skipBlock rest
    go (l : ls) = l : go ls

    skipBlock [] = []
    skipBlock (l : ls)
      | l == whenDef = case ls of
          (_ : rest) -> go rest
          []         -> []
      | T.isPrefixOf whenDefSpace l = go ls
      | otherwise = skipBlock ls
#-}

------------------------------------------------------------------------
-- 可变引用：服务句柄的隐藏状态住在这里（层级多态：状态可以是 Set₁ 的东西，比如 Server × 模型）
------------------------------------------------------------------------

postulate
  IORef      : ∀ {a} → Set a → Set a
  newIORef   : ∀ {a} {A : Set a} → A → IO (IORef A)
  readIORef  : ∀ {a} {A : Set a} → IORef A → IO A
  writeIORef : ∀ {a} {A : Set a} → IORef A → A → IO ⊤
{-# COMPILE GHC IORef      = type IORefL #-}
{-# COMPILE GHC newIORef   = \ _ _ -> R.newIORef #-}
{-# COMPILE GHC readIORef  = \ _ _ -> R.readIORef #-}
{-# COMPILE GHC writeIORef = \ _ _ -> R.writeIORef #-}

------------------------------------------------------------------------
-- 目录与文件
------------------------------------------------------------------------

postulate
  mkdirP     : String → IO ⊤           -- mkdir -p
  fileExists : String → IO Bool
  dirExists  : String → IO Bool
  removeAll  : String → IO ⊤           -- rm -rf（存在才删）
{-# COMPILE GHC mkdirP     = D.createDirectoryIfMissing True . T.unpack #-}
{-# COMPILE GHC fileExists = D.doesFileExist . T.unpack #-}
{-# COMPILE GHC dirExists  = D.doesDirectoryExist . T.unpack #-}
{-# COMPILE GHC removeAll  = removeTree . T.unpack #-}

------------------------------------------------------------------------
-- 起一个进程，等它跑完：退出码、stdout、stderr。编译器就是这样接进来的
------------------------------------------------------------------------

data ProcResult : Set where
  procResult : Nat → String → String → ProcResult
{-# COMPILE GHC ProcResult = data ProcResult (ProcResult) #-}

postulate
  readProcess : String → List String → String → IO ProcResult     -- 命令、参数、stdin
{-# COMPILE GHC readProcess = runProc #-}

-- Process execution never uses a shell. Timeout kills/reaps the process through
-- process's exception cleanup; OS errors are returned as ordinary tool failures.


postulate
  readProcessAt : String → Nat → String → List String → String → IO ProcResult
  sha256 : String → IO String
  freshDirectory : String → IO String
  atomicRename : String → String → IO ⊤
  currentDirectory : IO String
  exitFailure : IO ⊤
  readStdin : IO String
{-# COMPILE GHC readProcessAt = runProcAt #-}
{-# COMPILE GHC sha256 = shaText #-}
{-# COMPILE GHC freshDirectory = freshDir #-}
{-# COMPILE GHC atomicRename = \ a b -> D.renamePath (T.unpack a) (T.unpack b) #-}
{-# COMPILE GHC currentDirectory = fmap T.pack D.getCurrentDirectory #-}
{-# COMPILE GHC exitFailure = System.Exit.exitFailure #-}
{-# COMPILE GHC readStdin = TIO.getContents #-}



postulate
  jsonString : String → String → String
  fixIO : ∀ {a} {A : Set a} → (A → IO A) → IO A
{-# COMPILE GHC jsonString = jsonField #-}
{-# COMPILE GHC fixIO = \ _ _ -> MF.mfix #-}

-- Filesystem plumbing shared by session persistence and exception-safe probes.
postulate
  listDirectory : String → IO (List String)
  absolutePath : String → IO String
  linkPath : String → String → IO ⊤
  withTempDirectory : ∀ {a} {A : Set a} → String → (String → IO A) → IO A
{-# COMPILE GHC listDirectory = \ p -> fmap (map T.pack . L.sort) (D.listDirectory (T.unpack p)) #-}
{-# COMPILE GHC absolutePath = fmap T.pack . D.makeAbsolute . T.unpack #-}
{-# COMPILE GHC linkPath = \ a b -> D.doesDirectoryExist (T.unpack a) >>= \ d -> (if d then D.createDirectoryLink else D.createFileLink) (T.unpack a) (T.unpack b) #-}
{-# COMPILE GHC withTempDirectory = \ _ _ p f -> E.bracket (freshDir p) (removeTree . T.unpack) f #-}

postulate
  failIO : ∀ {a} {A : Set a} → String → IO A
  enableLineBuffering : IO ⊤
  stripStdlibWarnings : String → String
{-# COMPILE GHC failIO = \ _ _ s -> ioError (userError (T.unpack s)) #-}
{-# COMPILE GHC enableLineBuffering = enableLineBuf #-}
{-# COMPILE GHC stripStdlibWarnings = cleanAgdaOutput #-}
