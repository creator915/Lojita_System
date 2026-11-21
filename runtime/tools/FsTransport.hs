-- Binary framing and resource ownership; filesystem semantics live in Agda/C.
module FsTransport where

import qualified Control.Exception as E
import Control.Concurrent.MVar
import Control.Monad (forM_, unless, when, replicateM)
import qualified Data.ByteString as B
import Data.Char (isAlpha, isAlphaNum, isAscii)
import Data.List (nub, isPrefixOf, sortOn)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Numeric (readHex, showHex)
import qualified System.Directory as D
import System.Environment (getArgs)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), splitDirectories)
import qualified System.IO as H
import System.IO.Error (isDoesNotExistError)
import qualified System.Posix.Files as F
import qualified System.Posix.Temp as Temp
import qualified System.Process as P
import qualified System.Timeout as Timeout

data Fixture = FixDir T.Text Integer | FixFile T.Text Integer [Integer]
             | FixSymlink T.Text T.Text deriving (Eq, Show)
data Entry = Entry T.Text Integer Integer [Integer] deriving (Eq, Show)
data Wire = Wire [Integer] [Integer] (Maybe Integer) Bool [Entry] deriving (Eq, Show)
data FsHandle = FsHandle H.Handle H.Handle P.ProcessHandle FilePath [FilePath]
                         (Maybe String) (MVar Bool)

require :: Bool -> String -> IO ()
require b message = unless b (ioError (userError message))

ignore :: IO a -> IO ()
ignore action = E.catch (action >> pure ()) handler
  where handler :: E.IOException -> IO ()
        handler _ = pure ()

-- Call only after the relay/container has stopped. lstat identifies links before
-- any chmod or traversal; even dangling links are unlinked without following.
removeTree :: FilePath -> IO ()
removeTree path = E.catch action handler
  where
    action = do
      st <- F.getSymbolicLinkStatus path
      if F.isDirectory st then do
        F.setFileMode path (F.ownerModes `F.unionFileModes` F.fileMode st)
        D.listDirectory path >>= mapM_ (removeTree . (path </>))
        D.removeDirectory path
      else D.removeFile path
    handler :: E.IOException -> IO ()
    handler e = if isDoesNotExistError e then pure () else E.throwIO e

validPath :: FilePath -> Bool
validPath p = not (null p) && head p /= '/' && last p /= '/'
  && '\0' `notElem` p && not (T.pack "//" `T.isInfixOf` T.pack p)
  && all (\s -> not (null s) && s /= "." && s /= "..") (splitDirectories p)

validEnv :: String -> Bool
validEnv value = case break (== '=') value of
  (name, '=':body) -> not (null name) && (isAlpha (head name) || head name == '_')
    && all (\c -> isAscii c && (isAlphaNum c || c == '_')) name && '\0' `notElem` body
  _ -> False

fixturePath :: Fixture -> T.Text
fixturePath (FixDir p _) = p
fixturePath (FixFile p _ _) = p
fixturePath (FixSymlink p _) = p

fixtureDir :: Fixture -> Bool
fixtureDir (FixDir _ _) = True
fixtureDir _ = False

validOctets :: [Integer] -> Bool
validOctets = all (\n -> n >= 0 && n < 256)

validFixture :: Fixture -> Bool
validFixture (FixDir _ n) = n >= 0
validFixture (FixFile _ n bs) = n >= 0 && validOctets bs
validFixture (FixSymlink _ target) = not (T.null target) && not (T.any (== '\0') target)

checkLeaf :: FilePath -> FilePath -> IO ()
checkLeaf base name = go base (splitDirectories name)
  where
    go _ [] = pure ()
    go dir (part:parts) = do
      let path = dir </> part
      st <- F.getSymbolicLinkStatus path
      require (if null parts then F.isRegularFile st else F.isDirectory st)
              ("non-regular owned path: " ++ name)
      go path parts

-- Readback owns the tree after all child processes have been reaped. Check
-- each object with lstat before temporarily granting access; in particular a
-- symlink leaf is rejected before any chmod can affect its external target.
-- Brackets restore exact stored modes even when a deeper check/read fails.
readOwned :: FilePath -> FilePath -> IO [Integer]
readOwned base name = directory base (walk base (splitDirectories name))
  where
    permissions path st needed action =
      let old = F.fileMode st
          granted = old `F.unionFileModes` needed
      in if old == granted then action else
        E.bracket_ (F.setFileMode path granted) (F.setFileMode path old) action
    directory path action = do
      st <- F.getSymbolicLinkStatus path
      require (F.isDirectory st) ("non-directory owned ancestor: " ++ name)
      permissions path st (F.ownerReadMode `F.unionFileModes` F.ownerExecuteMode) action
    walk _ [] = ioError (userError "empty owned path")
    walk dir (part:parts) = do
      let path = dir </> part
      if null parts then do
        st <- F.getSymbolicLinkStatus path
        require (F.isRegularFile st) ("non-regular owned path: " ++ name)
        permissions path st F.ownerReadMode (map fromIntegral . B.unpack <$> B.readFile path)
      else directory path (walk path parts)

makeRoot :: FilePath -> IO FilePath
makeRoot parent = do
  D.createDirectoryIfMissing True parent
  root <- Temp.mkdtemp (parent </> "fs-")
  F.setFileMode root 0o700
  pure root

dockerRemove :: Maybe String -> IO ()
dockerRemove Nothing = pure ()
dockerRemove (Just name) = ignore (P.readProcessWithExitCode "docker" ["rm", "-f", name] "")

dispose :: FsHandle -> IO ()
dispose (FsHandle hin hout ph root _ container _) = do
  ignore (H.hClose hin)
  ended <- Timeout.timeout 3000000 (P.waitForProcess ph)
  case ended of
    Nothing -> ignore (P.terminateProcess ph)
    Just _ -> pure ()
  dockerRemove container
  ignore (P.waitForProcess ph)
  ignore (H.hClose hout)
  removeTree root

hex :: [Integer] -> String
hex [] = "-"
hex bs = concatMap digit bs
  where digit n = let s = showHex n "" in if length s == 1 then '0':s else s

hexText :: T.Text -> String
hexText = hex . map fromIntegral . B.unpack . TE.encodeUtf8

unhex :: String -> IO [Integer]
unhex "-" = pure []
unhex input = go input
  where
    go [] = pure []
    go (a:b:rest) = case readHex [a,b] of
      [(n, "")] | n >= 0 && n < 256 -> (n:) <$> go rest
      _ -> ioError (userError "invalid relay hex")
    go _ = ioError (userError "odd relay hex")

natural :: String -> IO Integer
natural input = case reads input of
  [(n, "")] | n >= 0 -> pure n
  _ -> ioError (userError "invalid relay natural")

readEntry :: H.Handle -> IO Entry
readEntry hout = do
  line <- H.hGetLine hout
  case words line of
    ["F", p, k, m, b] -> do
      path <- unhex p >>= either E.throwIO pure . TE.decodeUtf8' . B.pack . map fromInteger
      kind <- natural k
      mode <- natural m
      require (kind <= 2 && mode <= 511) "invalid relay entry kind/mode"
      contents <- unhex b
      pure (Entry path kind mode contents)
    _ -> ioError (userError "invalid relay entry")

exchange :: FsHandle -> T.Text -> IO Wire
exchange (FsHandle hin hout _ _ _ _ _) command = do
  require (not (T.any (\c -> c == '\n' || c == '\r' || c == '\0') command)) "invalid control command"
  H.hPutStrLn hin (T.unpack command)
  H.hFlush hin
  let receive = do
        line <- H.hGetLine hout
        case words line of
          ["O", o, e, s, t, c] -> do
            out <- unhex o
            err <- unhex e
            status <- if s == "-1" then pure Nothing else Just <$> natural s
            require (t == "0" || t == "1") "invalid timeout flag"
            count <- natural c
            require (count <= toInteger (maxBound :: Int)) "snapshot too large"
            entries <- replicateM (fromInteger count) (readEntry hout)
            pure (Wire out err status (t == "1") entries)
          _ -> ioError (userError ("filesystem relay protocol failure: " ++ take 200 line))
      deadline = case words (T.unpack command) of
        "R":ms:_ -> case reads ms of
          [(0, "")] -> Nothing
          [(n, "")] | n > (0 :: Integer) -> Just (min (toInteger (maxBound :: Int)) (n * 1000 + 35000000))
          _ -> Just 35000000
        _ -> Just 35000000
  case deadline of
    Nothing -> receive
    Just micros -> Timeout.timeout (fromInteger micros) receive >>= maybe
      (ioError (userError "filesystem relay transport timeout")) pure

-- E catches failures inside modifyMVar so a failed call remains permanently
-- closed; modifyMVar's exception rollback cannot resurrect a disposed handle.
liveAction :: FsHandle -> Bool -> IO a -> IO a
liveAction h@(FsHandle _ _ _ _ _ _ lock) stopping action = E.mask $ \restore -> do
  result <- modifyMVar lock $ \closed -> if closed then
    pure (True, Left (E.toException (userError "filesystem already stopped")))
    else do
      outcome <- E.try (restore action)
      case outcome of
        Right value -> pure (stopping, Right value)
        Left err -> do
          ignore (dispose h)
          pure (True, Left (err :: E.SomeException))
  either E.throwIO pure result

callFs :: FsHandle -> T.Text -> IO Wire
callFs h command = liveAction h False $ do
  response@(Wire _ _ status _ _) <- exchange h command
  let op = takeWhile (/= ' ') (T.unpack command)
  require (op == "R" || status == Nothing) "filesystem operation rejected"
  pure response

stopFs :: FsHandle -> IO [[Integer]]
stopFs h@(FsHandle _ _ ph root paths _ _) = liveAction h True $ E.finally (do
  _ <- exchange h (T.pack "Q")
  code <- P.waitForProcess ph
  require (code == ExitSuccess) "filesystem relay failed at stop"
  mapM (readOwned (root </> "work")) paths) (dispose h)

openFs :: T.Text -> T.Text -> Bool -> T.Text -> [T.Text] -> [T.Text]
       -> [[Integer]] -> [Fixture] -> IO FsHandle
openFs relay = openFsWithCand relay T.empty

openFsWithCand :: T.Text -> T.Text -> T.Text -> Bool -> T.Text -> [T.Text] -> [T.Text]
               -> [[Integer]] -> [Fixture] -> IO FsHandle
openFsWithCand relay cand scratch docker image env names contents fixtures = E.mask $ \restore -> do
  let paths = map T.unpack names
      nodes = zip paths (repeat False) ++ map (\f -> (T.unpack (fixturePath f), fixtureDir f)) fixtures
      allPaths = map fst nodes
      vars = map T.unpack env
      varNames = map (takeWhile (/= '=')) vars
      collision (p, directory) (q, _) = not directory && (p ++ "/") `isPrefixOf` q
  require (all validPath allPaths && length allPaths == length (nub allPaths)) "invalid/duplicate filesystem path"
  require (not (or [collision p q | p <- nodes, q <- nodes])) "filesystem parent/leaf collision"
  require (length names == length contents && all validOctets contents) "invalid owned file contents/arity"
  require (all validFixture fixtures) "invalid fixture"
  require (all validEnv vars && length varNames == length (nub varNames)) "invalid/duplicate environment name"
  when docker $ require (not (T.null image) && T.head image /= '-' && not (T.any (== '\0') image)) "invalid image"
  relayPath <- D.canonicalizePath (T.unpack relay)
  scratchPath <- D.makeAbsolute (T.unpack scratch)
  hasCand <- if docker && not (T.null cand) then D.doesFileExist (T.unpack cand) else pure False
  E.bracketOnError (makeRoot scratchPath) removeTree $ \root -> do
    let work = root </> "work"
        candCopy = root </> "cand-bin"
    D.createDirectory work
    F.setFileMode work (if docker then 0o777 else 0o755)
    when hasCand $ do
      F.setFileMode root 0o755
      D.copyFile (T.unpack cand) candCopy
      F.setFileMode candCopy 0o755
    when docker $ require (',' `notElem` relayPath && ',' `notElem` work && (not hasCand || ',' `notElem` candCopy)) "commas in Docker bind paths are unsupported"
    let name = "fsrelay-" ++ reverse (takeWhile (/= '/') (reverse root))
        container = if docker then Just name else Nothing
        candMount = if hasCand then ["--mount", "type=bind,src=" ++ candCopy ++ ",dst=/codetransport-cand,readonly"] else []
        process = if docker then P.proc "docker"
          (["run", "--rm", "-i", "--pull=never", "--network=none", "--cap-drop=ALL",
            "--security-opt=no-new-privileges", "--user", "65534:65534", "--read-only",
            "--pids-limit=128", "--tmpfs", "/tmp:rw,nosuid,noexec,size=64m", "--name", name,
            "--mount", "type=bind,src=" ++ relayPath ++ ",dst=/fs-relay,readonly"]
           ++ candMount ++
           ["--mount", "type=bind,src=" ++ work ++ ",dst=/work", "--workdir", "/work",
            "--entrypoint", "/fs-relay", T.unpack image])
          else (P.proc relayPath []) { P.env = Just [] }
        cp = process { P.cwd = Just work, P.std_in = P.CreatePipe, P.std_out = P.CreatePipe,
                       P.std_err = P.Inherit, P.close_fds = True }
    E.onException (do
      (Just hin, Just hout, _, ph) <- P.createProcess cp
      lock <- newMVar False
      let h = FsHandle hin hout ph root paths container lock
          send = callFs h . T.pack
      E.onException (restore (do
        H.hSetBuffering hin H.LineBuffering
        H.hSetBuffering hout H.LineBuffering
        ready <- Timeout.timeout 15000000 (H.hGetLine hout)
        require (ready == Just "READY") "filesystem relay did not start"
        forM_ env $ \v -> send ("E " ++ hexText v)
        -- Defer restrictive explicit directory modes until all descendants exist.
        let dirs = sortOn (T.length . fixturePath) [f | f@(FixDir _ _) <- fixtures]
        forM_ dirs $ \f -> send ("D " ++ hexText (fixturePath f) ++ " 493")
        forM_ (zip names contents) $ \(p, bs) -> send ("W " ++ hexText p ++ " " ++ hex bs)
        forM_ fixtures $ \f -> case f of
          FixDir _ _ -> pure ()
          FixFile p mode bs -> do
            _ <- send ("W " ++ hexText p ++ " " ++ hex bs)
            _ <- send ("M " ++ hexText p ++ " " ++ show (mode `mod` 512))
            pure ()
          FixSymlink p target -> do
            _ <- send ("L " ++ hexText p ++ " " ++ hexText target)
            pure ()
        forM_ (reverse dirs) $ \f -> case f of
          FixDir p mode -> send ("M " ++ hexText p ++ " " ++ show (mode `mod` 512)) >> pure ()
          _ -> pure ()
        pure h)) (dispose h)) (dockerRemove container)

localOnly :: IO Bool
localOnly = elem "--local-only" <$> getArgs
