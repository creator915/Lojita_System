-- The relay owns Git/process semantics. This module owns protocol framing and
-- the lifetime of each private workspace, including every exceptional path.
module GitTransport
  ( Summary(..), Wire(..), GitHandle, openGit, openGitWithCand, callGit, stopGit, localOnly
  , hex, hexText
  ) where

import qualified Control.Exception as E
import Control.Concurrent.MVar
import Control.Monad (forM_, unless, when, replicateM)
import qualified Data.ByteString as B
import Data.Char (isAlpha, isAlphaNum, isAscii)
import Data.List (nub, isPrefixOf, isSuffixOf, isInfixOf)
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
import qualified System.Posix.User as U
import qualified System.Process as P
import qualified System.Timeout as Timeout

data Summary = Summary T.Text Integer [T.Text] [T.Text] [T.Text] [T.Text] [T.Text]
  deriving (Eq, Show)
data Wire = Wire [Integer] [Integer] T.Text (Maybe Integer) Bool (Maybe Summary)
  deriving (Eq, Show)
data GitHandle = GitHandle H.Handle H.Handle P.ProcessHandle FilePath [T.Text]
  (Maybe String) (MVar Bool)

require :: Bool -> String -> IO ()
require b message = unless b (ioError (userError message))

ignore :: IO a -> IO ()
ignore action = E.catch (action >> pure ()) handler
  where
    handler :: E.IOException -> IO ()
    handler _ = pure ()

-- Inspect with lstat before any permission adjustment or descent. A target may
-- plant a symlink to a read-only external file; cleanup only unlinks that link.
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
  && '\0' `notElem` p && not ("//" `isInfixOf` p)
  && all (\s -> not (null s) && s /= "." && s /= "..") (splitDirectories p)
  && takeWhile (/= '/') p /= ".git"

validBranch :: String -> Bool
validBranch s = not (null s) && s /= "@" && s /= "HEAD" && head s /= '-' && head s /= '.' && head s /= '/'
  && last s /= '/' && last s /= '.' && not (any (`isInfixOf` s) ["..", "@{", "//"])
  && all (\c -> isAscii c && (isAlphaNum c || c `elem` "_-./")) s
  && all (\p -> not (null p) && head p /= '.' && last p /= '.' && not (".lock" `isSuffixOf` p))
         (splitDirectories s)

validEnv :: String -> Bool
validEnv value = case break (== '=') value of
  (name, '=':body) -> not (null name) && (isAlpha (head name) || head name == '_')
    && all (\c -> isAscii c && (isAlphaNum c || c == '_')) name && '\0' `notElem` body
  _ -> False

validOctets :: [Integer] -> Bool
validOctets = all (\n -> n >= 0 && n < 256)

makeRoot :: FilePath -> IO FilePath
makeRoot parent = do
  D.createDirectoryIfMissing True parent
  root <- Temp.mkdtemp (parent </> "git-")
  F.setFileMode root 0o700
  pure root

dockerRemove :: Maybe String -> IO ()
dockerRemove Nothing = pure ()
dockerRemove (Just name) = ignore (P.readProcessWithExitCode "docker" ["rm", "-f", name] "")

dispose :: GitHandle -> IO ()
dispose (GitHandle hin hout ph root _ container _) = do
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
  where
    digit n = let s = showHex n "" in if length s == 1 then '0':s else s

hexText :: T.Text -> String
hexText = hex . map fromIntegral . B.unpack . TE.encodeUtf8

unhex :: String -> IO [Integer]
unhex "-" = pure []
unhex input = go input
  where
    go [] = pure []
    go (a:b:rest) = case readHex [a,b] of
      [(n, "")] | n >= 0 && n < 256 -> (n:) <$> go rest
      _ -> ioError (userError "invalid Git relay hex")
    go _ = ioError (userError "odd Git relay hex")

textHex :: String -> IO T.Text
textHex input = unhex input >>= either E.throwIO pure . TE.decodeUtf8' . B.pack . map fromInteger

natural :: String -> IO Integer
natural input = case reads input of
  [(n, "")] | n >= 0 -> pure n
  _ -> ioError (userError "invalid Git relay natural")

readNames :: H.Handle -> String -> IO [T.Text]
readNames hout size = do
  count <- natural size
  require (count <= toInteger (maxBound :: Int)) "Git summary too large"
  replicateM (fromInteger count) $ do
    line <- H.hGetLine hout
    case words line of
      ["N", name] -> textHex name
      _ -> ioError (userError "invalid Git summary name")

readSummary :: H.Handle -> IO Summary
readSummary hout = do
  line <- H.hGetLine hout
  case words line of
    ["S", branch, commits, branches, tags, staged, modified, untracked] -> do
      current <- textHex branch
      count <- natural commits
      bs <- readNames hout branches
      ts <- readNames hout tags
      ss <- readNames hout staged
      ms <- readNames hout modified
      us <- readNames hout untracked
      pure (Summary current count bs ts ss ms us)
    _ -> ioError (userError "invalid Git summary")

exchange :: GitHandle -> T.Text -> IO Wire
exchange (GitHandle hin hout _ _ _ _ _) command = do
  require (not (T.any (\c -> c == '\n' || c == '\r' || c == '\0') command)) "invalid Git control command"
  H.hPutStrLn hin (T.unpack command)
  H.hFlush hin
  let receive = do
        line <- H.hGetLine hout
        case words line of
          ["O", o, e, s, t, oid, present] -> do
            out <- unhex o
            err <- unhex e
            hash <- textHex oid
            require (T.null hash || (T.length hash == 40 && T.all (`elem` "0123456789abcdef") hash))
                    "invalid Git object identifier"
            status <- if s == "-1" then pure Nothing else Just <$> natural s
            require (t == "0" || t == "1") "invalid Git timeout flag"
            summary <- case present of
              "0" -> pure Nothing
              "1" -> Just <$> readSummary hout
              _ -> ioError (userError "invalid Git summary flag")
            pure (Wire out err hash status (t == "1") summary)
          _ -> ioError (userError ("Git relay protocol failure: " ++ take 200 line))
      deadline = case words (T.unpack command) of
        "R":ms:_ -> case reads ms of
          [(0, "")] -> Nothing
          [(n, "")] | n > (0 :: Integer) -> Just (min (toInteger (maxBound :: Int)) (n * 1000 + 35000000))
          _ -> Just 35000000
        _ -> Just 35000000
  case deadline of
    Nothing -> receive
    Just micros -> Timeout.timeout (fromInteger micros) receive >>= maybe
      (ioError (userError "Git relay transport timeout")) pure

-- Catch inside modifyMVar: an exception permanently closes the handle rather
-- than allowing modifyMVar's rollback to resurrect a disposed workspace.
liveAction :: GitHandle -> Bool -> IO a -> IO a
liveAction h@(GitHandle _ _ _ _ _ _ lock) stopping action = E.mask $ \restore -> do
  result <- modifyMVar lock $ \closed -> if closed then
    pure (True, Left (E.toException (userError "Git sandbox already stopped")))
    else do
      outcome <- E.try (restore action)
      case outcome of
        Right value -> pure (stopping, Right value)
        Left err -> do
          ignore (dispose h)
          pure (True, Left (err :: E.SomeException))
  either E.throwIO pure result

successful :: Maybe Integer -> Bool
successful Nothing = True
successful (Just n) = n == 0

callGit :: GitHandle -> T.Text -> IO Wire
callGit h command = liveAction h False $ do
  response@(Wire _ _ _ status _ _) <- exchange h command
  let op = takeWhile (/= ' ') (T.unpack command)
  require (op == "R" || successful status) "Git operation rejected"
  pure response

stopGit :: GitHandle -> IO [[Integer]]
stopGit h@(GitHandle _ _ ph _ paths _ _) = liveAction h True $ E.finally (do
  contents <- mapM readOwned paths
  Wire _ _ _ status _ _ <- exchange h (T.pack "Q")
  require (successful status) "Git relay rejected stop"
  code <- P.waitForProcess ph
  require (code == ExitSuccess) "Git relay failed at stop"
  pure contents) (dispose h)
  where
    readOwned path = do
      Wire out _ _ status timed summary <- exchange h (T.pack ("F " ++ hexText path))
      require (successful status && not timed && summary == Nothing) "non-regular or missing owned Git file"
      pure out

openGit :: T.Text -> T.Text -> Bool -> T.Text -> T.Text -> T.Text -> T.Text
        -> Integer -> [T.Text] -> [T.Text] -> [[Integer]] -> IO GitHandle
openGit relay = openGitWithCand relay T.empty

openGitWithCand :: T.Text -> T.Text -> T.Text -> Bool -> T.Text -> T.Text -> T.Text -> T.Text
                -> Integer -> [T.Text] -> [T.Text] -> [[Integer]] -> IO GitHandle
openGitWithCand relay cand scratch docker image branch author email epoch env names contents = E.mask $ \restore -> do
  let paths = map T.unpack names
      vars = map T.unpack env
      varNames = map (takeWhile (/= '=')) vars
      collision p q = (p ++ "/") `isPrefixOf` q
  require (validBranch (T.unpack branch)) "invalid default Git branch"
  require (epoch >= 0 && epoch <= 9223372036854775807) "invalid Git epoch"
  require (all (\s -> not (T.null s) && not (T.any (`elem` "\0\n\r<>") s)) [author, email]) "invalid Git author identity"
  require (all validPath paths && length paths == length (nub paths)) "invalid/duplicate owned Git path"
  require (not (or [collision p q | p <- paths, q <- paths])) "owned Git parent/leaf collision"
  require (length names == length contents && all validOctets contents) "invalid owned Git contents/arity"
  require (all validEnv vars && length varNames == length (nub varNames)) "invalid/duplicate Git environment name"
  when docker $ require (not (T.null image) && T.head image /= '-' && not (T.any (== '\0') image)) "invalid Git Docker image"
  relayPath <- D.canonicalizePath (T.unpack relay)
  scratchPath <- D.makeAbsolute (T.unpack scratch)
  hasCand <- if docker && not (T.null cand) then D.doesFileExist (T.unpack cand) else pure False
  E.bracketOnError (makeRoot scratchPath) removeTree $ \root -> do
    let work = root </> "work"
        candCopy = root </> "cand-bin"
    D.createDirectory work
    F.setFileMode work 0o755
    when hasCand $ do
      F.setFileMode root 0o755
      D.copyFile (T.unpack cand) candCopy
      F.setFileMode candCopy 0o755
    -- Git checks ownership of both the worktree and .git. Matching the bind
    -- directory's UID/GID also lets target Git commands use their exact env
    -- without safe.directory overrides or a world-writable worktree.
    workStatus <- F.getFileStatus work
    rootDocker <- if docker then (== 0) <$> U.getEffectiveUserID else pure False
    sandboxUser <- if rootDocker then do
      F.setOwnerAndGroup work 65534 65534
      pure "65534:65534"
      else pure (show (F.fileOwner workStatus) ++ ":" ++ show (F.fileGroup workStatus))
    when docker $ require (',' `notElem` relayPath && ',' `notElem` work && (not hasCand || ',' `notElem` candCopy)) "commas in Docker bind paths are unsupported"
    let name = "gitrelay-" ++ reverse (takeWhile (/= '/') (reverse root))
        container = if docker then Just name else Nothing
        candMount = if hasCand then ["--mount", "type=bind,src=" ++ candCopy ++ ",dst=/codetransport-cand,readonly"] else []
        process = if docker then P.proc "docker"
          (["run", "--rm", "-i", "--pull=never", "--network=none", "--cap-drop=ALL",
            "--security-opt=no-new-privileges", "--user", sandboxUser, "--read-only",
            "--pids-limit=128", "--tmpfs", "/tmp:rw,nosuid,noexec,size=64m", "--name", name,
            "--mount", "type=bind,src=" ++ relayPath ++ ",dst=/git-relay,readonly"]
           ++ candMount ++
           ["--mount", "type=bind,src=" ++ work ++ ",dst=/work", "--workdir", "/work",
            "--entrypoint", "/git-relay", T.unpack image])
          else (P.proc relayPath []) { P.env = Just [] }
        cp = process { P.cwd = Just work, P.std_in = P.CreatePipe, P.std_out = P.CreatePipe,
                       P.std_err = P.Inherit, P.close_fds = True }
    E.onException (do
      (Just hin, Just hout, _, ph) <- P.createProcess cp
      lock <- newMVar False
      let h = GitHandle hin hout ph root names container lock
          send = callGit h . T.pack
      E.onException (restore (do
        H.hSetBuffering hin H.LineBuffering
        H.hSetBuffering hout H.LineBuffering
        ready <- Timeout.timeout 15000000 (H.hGetLine hout)
        require (ready == Just "READY") "Git relay did not start"
        _ <- send (unwords ["I", hexText branch, hexText author, hexText email, show epoch])
        forM_ env $ \v -> send ("E " ++ hexText v)
        forM_ (zip names contents) $ \(p, bs) -> send ("W " ++ hexText p ++ " " ++ hex bs)
        pure h)) (dispose h)) (dockerRemove container)

localOnly :: IO Bool
localOnly = elem "--local-only" <$> getArgs
