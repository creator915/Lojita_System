-- The only host boundary: binary framing, process lifetime, and owned-file return.
-- HTTP bytes and routing policy are supplied by the pure Agda model.
module NetTransport where

import qualified Control.Exception as E
import Control.Concurrent.MVar (MVar, newMVar, modifyMVar)
import Control.Monad (forM_, unless, when, replicateM)
import qualified Data.ByteString as B
import Data.Char (isAlpha, isAlphaNum, isAscii)
import Data.List (nub, isPrefixOf)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Numeric (readHex, showHex)
import qualified System.Directory as D
import System.Environment (getArgs)
import System.Exit (ExitCode(..))
import System.FilePath ((</>), splitDirectories, takeFileName)
import qualified System.IO as H
import System.IO.Error (isDoesNotExistError)
import qualified System.Posix.Files as F
import qualified System.Posix.Signals as Signals
import qualified System.Posix.Temp as Temp
import qualified System.Process as P
import qualified System.Timeout as Timeout

data Route = Route T.Text T.Text [Integer] deriving (Eq, Show)
data Rule = Rule [Integer] [Integer] deriving (Eq, Show)
data Topology = HttpStub [Integer] [Route] | TcpStub [Rule] | UdpStub [Rule]
              | Daemon T.Text [T.Text]
              | HttpDelayedStub Integer [Integer] [Route]
              | TcpDelayedStub Integer [Rule]
              deriving (Eq, Show)
data Wire = Wire [Integer] [Integer] [Integer] [[Integer]] (Maybe Integer) Bool
  deriving (Eq, Show)
data NetHandle = NetHandle H.Handle H.Handle P.ProcessHandle FilePath [FilePath]
                           (Maybe String) (MVar Bool)

require :: Bool -> String -> IO ()
require condition message = unless condition (ioError (userError message))

ignore :: IO a -> IO ()
ignore action = E.catch (action >> pure ()) handler
  where handler :: E.IOException -> IO ()
        handler _ = pure ()

-- No chmod or traversal follows symlinks. Children have stopped before cleanup.
removeTree :: FilePath -> IO ()
removeTree path = E.catch action handler
  where
    action = do
      st <- F.getSymbolicLinkStatus path
      if F.isDirectory st then do
        let old = F.fileMode st
            accessible = F.ownerModes `F.unionFileModes` old
        when (accessible /= old) (F.setFileMode path accessible)
        D.listDirectory path >>= mapM_ (removeTree . (path </>))
        D.removeDirectory path
      else D.removeFile path
    handler :: E.IOException -> IO ()
    handler err = if isDoesNotExistError err then pure () else E.throwIO err

validPath :: FilePath -> Bool
validPath path = not (null path) && head path /= '/' && last path /= '/'
  && '\0' `notElem` path && not (T.pack "//" `T.isInfixOf` T.pack path)
  && all (\part -> not (null part) && part /= "." && part /= "..") (splitDirectories path)

validEnv :: String -> Bool
validEnv value = case break (== '=') value of
  (name, '=':body) -> not (null name) && (isAlpha (head name) || head name == '_')
    && all (\c -> isAscii c && (isAlphaNum c || c == '_')) name && '\0' `notElem` body
  _ -> False

validOctets :: [Integer] -> Bool
validOctets = all (\n -> n >= 0 && n < 256)

validText :: T.Text -> Bool
validText = not . T.any (== '\0')

validTopology :: Topology -> Bool
validTopology (HttpStub fallback routes) = validOctets fallback && all validRoute routes
  where validRoute (Route method target reply) = not (T.null method) && not (T.null target)
          && validText method && validText target && validOctets reply
validTopology (TcpStub rules) = all validRule rules
validTopology (UdpStub rules) = all validRule rules
validTopology (Daemon exe args) = not (T.null exe) && validText exe && all validText args
validTopology (HttpDelayedStub ms fallback routes) = ms >= 0 && validTopology (HttpStub fallback routes)
validTopology (TcpDelayedStub ms rules) = ms >= 0 && all validRule rules

validRule :: Rule -> Bool
validRule (Rule prefix payload) = validOctets prefix && validOctets payload

-- Ownership returns only regular leaves through real directory ancestors.
-- Temporary access is bracketed and restores the exact prior permission bits.
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
  root <- Temp.mkdtemp (parent </> "net-")
  F.setFileMode root 0o700
  pure root

dockerRemove :: Maybe String -> IO ()
dockerRemove Nothing = pure ()
dockerRemove (Just name) = ignore (P.readProcessWithExitCode "docker" ["rm", "-f", name] "")

-- Closing stdin asks the relay to perform the same process-group cleanup as Q.
-- A bounded fallback also handles failed startup or broken framing.
dispose :: NetHandle -> IO ()
dispose (NetHandle hin hout ph root _ container _) = do
  ignore (H.hClose hin)
  ended <- Timeout.timeout 3000000 (P.waitForProcess ph)
  case ended of
    Just _ -> pure ()
    Nothing -> do
      ignore (P.terminateProcess ph)
      stopped <- Timeout.timeout 2000000 (P.waitForProcess ph)
      case stopped of
        Just _ -> pure ()
        Nothing -> do
          pid <- P.getPid ph
          forM_ pid $ \p -> ignore (Signals.signalProcess Signals.sigKILL p)
  dockerRemove container
  ignore (P.waitForProcess ph)
  ignore (H.hClose hout)
  removeTree root

hex :: [Integer] -> String
hex [] = "-"
hex octets = concatMap digit octets
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

readCapture :: H.Handle -> IO [Integer]
readCapture hout = do
  line <- H.hGetLine hout
  case words line of
    ["C", payload] -> unhex payload
    _ -> ioError (userError "invalid captured request framing")

exchange :: NetHandle -> T.Text -> IO Wire
exchange (NetHandle hin hout _ _ _ _ _) command = do
  require (not (T.any (\c -> c == '\n' || c == '\r' || c == '\0') command)) "invalid control command"
  H.hPutStrLn hin (T.unpack command)
  H.hFlush hin
  let receive = do
        line <- H.hGetLine hout
        case words line of
          ["O", o, e, w, s, t, c] -> do
            out <- unhex o
            err <- unhex e
            wire <- unhex w
            status <- if s == "-1" then pure Nothing else Just <$> natural s
            require (t == "0" || t == "1") "invalid timeout flag"
            count <- natural c
            require (count <= toInteger (maxBound :: Int)) "capture count overflow"
            captures <- replicateM (fromInteger count) (readCapture hout)
            pure (Wire out err wire captures status (t == "1"))
          _ -> ioError (userError ("network relay protocol failure: " ++ take 200 line))
      deadline = case words (T.unpack command) of
        op:ms:_ | op `elem` ["R", "C", "J", "G", "P", "S"] -> case reads ms of
          [(n, "")] | n >= (0 :: Integer) -> min (toInteger (maxBound :: Int)) (n * 1000 + 35000000)
          _ -> 35000000
        _ -> 35000000
  Timeout.timeout (fromInteger deadline) receive >>= maybe
    (ioError (userError "network relay transport timeout")) pure

-- Catch inside modifyMVar: an exception cannot roll a disposed handle back to
-- live. Every subsequent call and repeated stop rejects without allocating.
liveAction :: NetHandle -> Bool -> IO a -> IO a
liveAction h@(NetHandle _ _ _ _ _ _ lock) stopping action = E.mask $ \restore -> do
  result <- modifyMVar lock $ \closed -> if closed then
    pure (True, Left (E.toException (userError "network already stopped")))
    else do
      outcome <- E.try (restore action)
      case outcome of
        Right value -> pure (stopping, Right value)
        Left err -> do
          ignore (dispose h)
          pure (True, Left (err :: E.SomeException))
  either E.throwIO pure result

callNet :: NetHandle -> T.Text -> IO Wire
callNet h command = liveAction h False (exchange h command)

stopNet :: NetHandle -> IO [[Integer]]
stopNet h@(NetHandle _ _ ph root paths _ _) = liveAction h True $ E.finally (do
  _ <- exchange h (T.pack "Q")
  code <- P.waitForProcess ph
  require (code == ExitSuccess) "network relay failed at stop"
  mapM (readOwned (root </> "work")) paths) (dispose h)

openNet :: T.Text -> T.Text -> Bool -> T.Text -> [T.Text] -> [T.Text]
        -> [[Integer]] -> Topology -> IO NetHandle
openNet relay = openNetWithCand relay T.empty

openNetWithCand :: T.Text -> T.Text -> T.Text -> Bool -> T.Text -> [T.Text] -> [T.Text]
                -> [[Integer]] -> Topology -> IO NetHandle
openNetWithCand relay cand scratch docker image env names contents topology = E.mask $ \restore -> do
  let paths = map T.unpack names
      vars = map T.unpack env
      varNames = map (takeWhile (/= '=')) vars
  require (all validPath paths && length paths == length (nub paths)) "invalid/duplicate owned path"
  require (not (or [(p ++ "/") `isPrefixOf` q | p <- paths, q <- paths])) "owned parent/leaf collision"
  require (length names == length contents && all validOctets contents) "invalid owned contents/arity"
  require (all validEnv vars && length varNames == length (nub varNames)) "invalid/duplicate environment"
  require (validTopology topology) "invalid topology"
  when docker $ require (not (T.null image) && T.head image /= '-' && validText image) "invalid image"
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
    let name = "netrelay-" ++ takeFileName root
        container = if docker then Just name else Nothing
        candMount = if hasCand then ["--mount", "type=bind,src=" ++ candCopy ++ ",dst=/codetransport-cand,readonly"] else []
        process = if docker then P.proc "docker"
          (["run", "--rm", "-i", "--pull=never", "--network=none", "--cap-drop=ALL",
            "--security-opt=no-new-privileges", "--user", "65534:65534", "--read-only",
            "--pids-limit=128", "--tmpfs", "/tmp:rw,nosuid,noexec,size=64m", "--name", name,
            "--mount", "type=bind,src=" ++ relayPath ++ ",dst=/net-relay,readonly"]
           ++ candMount ++
           ["--mount", "type=bind,src=" ++ work ++ ",dst=/work", "--workdir", "/work",
            "--entrypoint", "/net-relay", T.unpack image])
          else (P.proc relayPath []) { P.env = Just [] }
        cp = process { P.cwd = Just work, P.std_in = P.CreatePipe, P.std_out = P.CreatePipe,
                       P.std_err = P.Inherit, P.close_fds = True }
    E.onException (do
      (Just hin, Just hout, _, ph) <- P.createProcess cp
      lock <- newMVar False
      let h = NetHandle hin hout ph root paths container lock
          send text = do
            Wire _ _ _ _ status timed <- callNet h (T.pack text)
            require (status == Nothing && not timed) "network initialization rejected"
      E.onException (restore (do
        H.hSetBuffering hin H.LineBuffering
        H.hSetBuffering hout H.LineBuffering
        ready <- Timeout.timeout 15000000 (H.hGetLine hout)
        require (ready == Just "READY") "network relay did not start"
        forM_ env $ \value -> send ("E " ++ hexText value)
        forM_ (zip names contents) $ \(path, value) -> send ("W " ++ hexText path ++ " " ++ hex value)
        case topology of
          HttpStub fallback routes -> do
            send ("H " ++ hex fallback)
            forM_ routes $ \(Route method target reply) ->
              send (unwords ["A", hexText method, hexText target, hex reply])
          HttpDelayedStub ms fallback routes -> do
            send ("Z " ++ show ms)
            send ("H " ++ hex fallback)
            forM_ routes $ \(Route method target reply) ->
              send (unwords ["A", hexText method, hexText target, hex reply])
          TcpStub rules -> send "T" >> forM_ rules (send . ruleCommand)
          TcpDelayedStub ms rules -> send ("Z " ++ show ms) >> send "T" >> forM_ rules (send . ruleCommand)
          UdpStub rules -> send "U" >> forM_ rules (send . ruleCommand)
          Daemon exe args -> send (unwords (["D", hexText exe, show (length args)] ++ map hexText args))
        pure h)) (dispose h)) (dockerRemove container)
  where ruleCommand (Rule prefix payload) = unwords ["B", hex prefix, hex payload]

localOnly :: IO Bool
localOnly = elem "--local-only" <$> getArgs
