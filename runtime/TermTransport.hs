-- Resource lifecycle and hex framing only. Terminal semantics are in Agda.
module TermTransport where

import qualified Control.Exception as E
import Control.Concurrent.MVar
import Control.Monad (forM_, unless, when)
import qualified Data.ByteString as B
import Data.Char (isAlphaNum, isAscii, isAlpha)
import Data.List (nub)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified System.Directory as D
import System.Exit (ExitCode(..))
import System.FilePath ((</>), isAbsolute, splitDirectories, takeDirectory)
import qualified System.IO as H
import System.IO.Error (isDoesNotExistError)
import qualified System.Posix.Files as F
import qualified System.Process as P
import qualified System.Posix.Temp as Temp
import qualified System.Timeout as Timeout
import Numeric (readHex)

data Wire = Wire [Integer] [Integer] [Integer] (Maybe Integer)
data TermHandle = TermHandle H.Handle H.Handle P.ProcessHandle FilePath [FilePath]
                             (Maybe String) (MVar Bool)

ignore :: IO a -> IO ()
ignore io = E.catch (io >> pure ()) (\e -> let _ = e :: E.IOException in pure ())
require :: Bool -> String -> IO ()
require b msg = unless b (ioError (userError msg))

-- Unlink symbolic links without chmodding or traversing their targets.
removeTree :: FilePath -> IO ()
removeTree path = E.catch action handler
  where
    action = do
      linked <- D.pathIsSymbolicLink path
      if linked then D.removeFile path else do
        directory <- D.doesDirectoryExist path
        if directory then do
          D.listDirectory path >>= mapM_ (removeTree . (path </>))
          D.removeDirectory path
        else D.removeFile path
    handler :: E.IOException -> IO ()
    handler e = if isDoesNotExistError e then pure () else E.throwIO e

-- Reject aliases, traversal and duplicate leaves before materialization.
-- Parent/leaf collisions fail materialization and remove the partial workspace.
-- Returned files must be regular, with no symlink in any path component.
validPath :: FilePath -> Bool
validPath p = not (null p) && not (isAbsolute p) && all valid (splitDirectories p)
  && all (/= '\0') p && last p /= '/' && not (T.pack "//" `T.isInfixOf` T.pack p)
  where valid x = not (null x) && x /= "." && x /= ".."

checkLeaf :: FilePath -> FilePath -> IO ()
checkLeaf root p = go root (splitDirectories p)
  where
    go _ [] = pure ()
    go base (x:xs) = do
      let path = base </> x
      st <- F.getSymbolicLinkStatus path
      require (if null xs then F.isRegularFile st else F.isDirectory st)
              ("non-regular owned path: " ++ p)
      go path xs

makeRoot :: FilePath -> IO FilePath
makeRoot parent = do
  D.createDirectoryIfMissing True parent
  -- mkdir is atomic, unlike removing a temp file and recreating its pathname.
  -- mkdtemp is exposed by unix through System.Posix.Temp (below via import).
  Temp.mkdtemp (parent </> "term-")

validEnv :: String -> Bool
validEnv v = case break (== '=') v of
  (n, '=':value) -> not (null n) && (isAlpha (head n) || head n == '_')
    && all (\c -> isAscii c && (isAlphaNum c || c == '_')) n && '\0' `notElem` value
  _ -> False

dockerRemove :: Maybe String -> IO ()
dockerRemove Nothing = pure ()
dockerRemove (Just name) = ignore (P.readProcessWithExitCode "docker" ["rm", "-f", name] "")

dispose :: TermHandle -> IO ()
dispose (TermHandle hin hout ph root _ container _) = do
  -- EOF asks the relay to kill/reap its process group even after an exception.
  ignore (H.hClose hin)
  ended <- Timeout.timeout 3000000 (P.waitForProcess ph)
  case ended of
    Nothing -> ignore (P.terminateProcess ph)
    Just _ -> pure ()
  dockerRemove container
  ignore (P.waitForProcess ph)
  ignore (H.hClose hout)
  removeTree root

openTerm :: T.Text -> T.Text -> Bool -> T.Text -> Bool -> T.Text -> [T.Text]
         -> [T.Text] -> Integer -> Integer -> [T.Text] -> [T.Text] -> IO TermHandle
openTerm relay = openTermWithCand relay T.empty

openTermWithCand :: T.Text -> T.Text -> T.Text -> Bool -> T.Text -> Bool -> T.Text -> [T.Text]
                 -> [T.Text] -> Integer -> Integer -> [T.Text] -> [T.Text] -> IO TermHandle
openTermWithCand relay cand scratch docker image pipe cmd args env rows cols names contents = do
  let paths = map T.unpack names
      vars = map T.unpack env
      envNames = map (takeWhile (/= '=')) vars
  require (all validPath paths && length paths == length (nub paths)) "invalid/duplicate owned file path"
  require (length names == length contents) "owned file arity"
  require (all validEnv vars && length envNames == length (nub envNames)) "invalid/duplicate environment name"
  require (rows > 0 && cols > 0 && rows <= 65535 && cols <= 65535) "invalid terminal dimensions"
  require (not (T.null cmd) && all (not . T.any (== '\0')) (cmd:args)) "invalid executable/argument"
  when docker $ require (not (T.null image) && T.head image /= '-' && not (T.any (== '\0') image)) "invalid image name"
  relayPath <- D.canonicalizePath (T.unpack relay)
  scratchPath <- D.makeAbsolute (T.unpack scratch)
  hasCand <- if docker && not (T.null cand) then D.doesFileExist (T.unpack cand) else pure False
  E.bracketOnError (makeRoot scratchPath) removeTree $ \root -> do
    let work = root </> "work"
        candCopy = root </> "cand-bin"
    D.createDirectory work
    when hasCand $ do
      F.setFileMode root 0o755
      D.copyFile (T.unpack cand) candCopy
      F.setFileMode candCopy 0o755
    when docker $ require (',' `notElem` relayPath && ',' `notElem` work && (not hasCand || ',' `notElem` candCopy)) "commas in Docker bind paths are unsupported"
    forM_ (zip paths contents) $ \(p, content) -> do
      D.createDirectoryIfMissing True (takeDirectory (work </> p))
      B.writeFile (work </> p) (TE.encodeUtf8 content)
    -- The mkdtemp root stays 0700 on the host unless candidate mount needs traversal.
    -- Inside its work bind mount, uid 65534 owns no host privilege.
    when docker $ do
      let grant path = do
            isDir <- D.doesDirectoryExist path
            F.setFileMode path (if isDir then 0o777 else 0o666)
            when isDir (D.listDirectory path >>= mapM_ (grant . (path </>)))
      grant work
    let relayArgs = [if pipe then "pipe" else "tty", show rows, show cols, show (length vars)]
                   ++ vars ++ map T.unpack (cmd:args)
        name = "codetransport-" ++ reverse (takeWhile (/= '/') (reverse root))
        container = if docker then Just name else Nothing
        candMount = if hasCand then ["--mount", "type=bind,src=" ++ candCopy ++ ",dst=/codetransport-cand,readonly"] else []
        process = if docker then
          P.proc "docker" (["run", "--rm", "-i", "--pull=never", "--network=none",
            "--cap-drop=ALL", "--security-opt=no-new-privileges", "--user", "65534:65534",
            "--read-only", "--pids-limit=128", "--tmpfs", "/tmp:rw,nosuid,noexec,size=64m",
            "--name", name, "--mount", "type=bind,src=" ++ relayPath ++ ",dst=/term-relay,readonly"]
            ++ candMount ++
            ["--mount", "type=bind,src=" ++ work ++ ",dst=/work", "--workdir", "/work",
             "--entrypoint", "/term-relay", T.unpack image] ++ relayArgs)
          else (P.proc "/usr/bin/env" (["-i", relayPath] ++ relayArgs)) { P.env = Just [] }
        cp = process { P.cwd = Just work, P.std_in = P.CreatePipe,
                       P.std_out = P.CreatePipe, P.std_err = P.Inherit, P.close_fds = True }
    E.onException (do
      (Just hin, Just hout, _, ph) <- P.createProcess cp
      lock <- newMVar False
      let h = TermHandle hin hout ph root paths container lock
      E.onException (do
        H.hSetBuffering hin H.LineBuffering
        H.hSetBuffering hout H.LineBuffering
        ready <- Timeout.timeout 15000000 (H.hGetLine hout)
        require (ready == Just "READY") "terminal relay did not start"
        pure h) (dispose h)) (dockerRemove container)

unhex :: String -> IO [Integer]
unhex "-" = pure []
unhex [] = pure []
unhex (a:b:rest) = case readHex [a,b] of
  [(n, "")] -> (n:) <$> unhex rest
  _ -> ioError (userError "invalid relay hex")
unhex _ = ioError (userError "odd relay hex")

exchange :: TermHandle -> T.Text -> IO Wire
exchange (TermHandle hin hout _ _ _ _ _) command = do
  H.hPutStrLn hin (T.unpack command)
  H.hFlush hin
  -- sleepMs has an explicit 24-hour transport limit, not a hidden short timeout.
  let limit = case words (T.unpack command) of
        ["S", n] -> case reads n of [(ms, "")] -> ms * 1000 + 35000000; _ -> 35000000
        _ -> 35000000
  result <- Timeout.timeout limit (H.hGetLine hout)
  case fmap words result of
    Just ["O", tty, out, err, status] -> do
      t <- unhex tty; o <- unhex out; e <- unhex err
      s <- case reads status of
        [(-1, "")] -> pure Nothing
        [(n, "")] | n >= 0 -> pure (Just n)
        _ -> ioError (userError "invalid relay exit status")
      pure (Wire t o e s)
    _ -> ioError (userError ("terminal relay protocol failure for " ++ takeWhile (/= ' ') (T.unpack command) ++ ": " ++ show result))

callTerm :: TermHandle -> T.Text -> IO Wire
callTerm h@(TermHandle _ _ _ _ _ _ lock) command = modifyMVar lock $ \closed -> do
  require (not closed) "terminal already stopped"
  E.onException ((\result -> (False, result)) <$> exchange h command) (dispose h)

stopTerm :: TermHandle -> IO [T.Text]
stopTerm h@(TermHandle _ _ ph root paths _ lock) = modifyMVar lock $ \closed -> do
  require (not closed) "terminal already stopped"
  result <- E.finally (do
    _ <- exchange h (T.pack "Q")
    code <- P.waitForProcess ph
    require (code == ExitSuccess) "terminal relay failed at stop"
    let work = root </> "work"
    mapM (\p -> checkLeaf work p >> (TE.decodeUtf8' <$> B.readFile (work </> p))
      >>= either E.throwIO pure) paths) (dispose h)
  pure (True, result)
