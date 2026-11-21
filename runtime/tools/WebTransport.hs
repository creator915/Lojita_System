-- The relay owns geometry. This module owns the process, pipes and byte files.
module WebTransport
  (WebHandle, Wire(..), openWeb, callWeb, flushWeb, stopWeb) where

import Control.Concurrent.MVar
import qualified Control.Exception as E
import Control.Monad (forM_, when)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.List (isPrefixOf, tails)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified System.Directory as D
import System.Exit (ExitCode(..))
import System.FilePath ((</>), splitDirectories, takeDirectory, takeFileName)
import qualified System.IO as H
import qualified System.Posix.Files as F
import qualified System.Posix.Signals as Sig
import qualified System.Posix.Temp as Temp
import System.Posix.Types (ProcessGroupID)
import qualified System.Process as P
import qualified System.Timeout as Timeout
import qualified TermTransport as Shared
import Text.Read (readMaybe)

data Wire = Ack | Frame Integer Integer | Pixel Bool Integer Integer Integer
  deriving (Eq, Show)

data Session = Session
  { input :: H.Handle, output :: H.Handle, process :: P.ProcessHandle
  , group :: Maybe ProcessGroupID, root :: FilePath, paths :: [FilePath]
  , container :: Maybe String }
newtype WebHandle = WebHandle (MVar (Maybe Session))

require :: Bool -> String -> IO ()
require = Shared.require

bounded :: Int -> String -> IO a -> IO a
bounded seconds label action = do
  result <- Timeout.timeout (seconds * 1000000) action
  maybe (ioError (userError (label ++ " timed out"))) pure result

validPaths :: [FilePath] -> Bool
validPaths ps = all valid ps && and [distinct a b | a:rest <- tails ps, b <- rest]
  where
    valid p = Shared.validPath p && all (`notElem` "\r\n") p
    distinct a b = let x = splitDirectories a; y = splitDirectories b
                   in not (x `isPrefixOf` y || y `isPrefixOf` x)

dispose :: Session -> IO ()
dispose s = E.finally stop (Shared.removeTree (root s))
  where
    stop = do
      forM_ (group s) $ \g -> Shared.ignore (Sig.signalProcessGroup Sig.sigKILL g)
      Shared.ignore (H.hClose (input s))
      Shared.ignore (H.hClose (output s))
      Shared.ignore (bounded 5 "wait for web relay" (P.waitForProcess (process s)))
      forM_ (container s) $ \name -> Shared.ignore
        (bounded 8 "remove web container" (P.readProcessWithExitCode "docker" ["rm", "-f", name] ""))

openWeb :: T.Text -> T.Text -> Bool -> T.Text -> Integer -> Integer ->
           [T.Text] -> [[Integer]] -> IO WebHandle
openWeb relay scratch docker image width height names contents = E.mask $ \restore -> do
  let ps = map T.unpack names
  require (validPaths ps) "invalid or overlapping web file paths"
  require (length ps == length contents) "wrong web file arity"
  require (all (all (\b -> b >= 0 && b <= 255)) contents) "invalid file byte"
  require (all (\n -> n > 0 && n <= 2048) [width,height]) "invalid web dimensions"
  when docker $ require (not (T.null image) && T.head image /= '-' && not (T.any (== '\0') image)) "invalid image"
  bin <- D.canonicalizePath (T.unpack relay)
  parent <- D.makeAbsolute (T.unpack scratch)
  D.createDirectoryIfMissing True parent
  E.bracketOnError (Temp.mkdtemp (parent </> "web-")) Shared.removeTree $ \dir -> do
    let work = dir </> "work"
        name = "codetransport-" ++ takeFileName dir
        args = [show width, show height] ++ ps
    D.createDirectory work
    when docker $ require (',' `notElem` bin && ',' `notElem` work) "invalid Docker mount path"
    restore $ forM_ (zip ps contents) $ \(p,bs) -> do
      D.createDirectoryIfMissing True (takeDirectory (work </> p))
      B.writeFile (work </> p) (B.pack (map fromInteger bs))
      -- Only predeclared regular leaves need write permission inside the bind.
      when docker (F.setFileMode (work </> p) 0o666)
    when docker $ do
      let traverseDirs path = do
            F.setFileMode path 0o755
            children <- D.listDirectory path
            forM_ children $ \p -> do
              let child = path </> p
              isDir <- D.doesDirectoryExist child
              when isDir (traverseDirs child)
      traverseDirs work
    let command = if docker then P.proc "docker"
          (["run","--rm","-i","--pull=never","--network=none","--cap-drop=ALL",
            "--security-opt=no-new-privileges","--read-only","--user","65534:65534",
            "--pids-limit=32","--name",name,"--mount","type=bind,src=" ++ bin ++ ",dst=/web-relay,readonly",
            "--mount","type=bind,src=" ++ work ++ ",dst=/work","--workdir","/work",
            "--entrypoint","/web-relay",T.unpack image] ++ args)
          else (P.proc "/usr/bin/env" (["-i",bin] ++ args)) { P.env = Just [] }
    (Just hin, Just hout, _, ph) <- P.createProcess command
      { P.cwd = Just work, P.std_in = P.CreatePipe, P.std_out = P.CreatePipe
      , P.std_err = P.Inherit, P.close_fds = True, P.create_group = True }
    pid <- P.getPid ph
    let s = Session hin hout ph pid dir ps (if docker then Just name else Nothing)
    flip E.onException (dispose s) $ do
      H.hSetBinaryMode hin True
      H.hSetBinaryMode hout True
      ready <- restore (bounded 15 "start web relay" (BC.hGetLine hout))
      require (ready == BC.pack "READY") "web relay handshake failed"
      WebHandle <$> newMVar (Just s)

-- The closed state is committed on every exception, including cancellation.
-- Concurrent calls and stop share a single request/reply and lifetime lock.
withSession :: Bool -> WebHandle -> (Session -> IO a) -> IO a
withSession closing (WebHandle cell) action = E.mask $ \restore -> do
  outcome <- modifyMVarMasked cell $ \live -> case live of
    Nothing -> ioError (userError "web relay already stopped")
    Just s -> do
      result <- E.try (restore (action s))
      case result of
        Right value | not closing -> pure (live, Right value)
        _ -> do
          cleaned <- E.try (dispose s)
          pure (Nothing, case cleaned of
            Left e -> Left (e :: E.SomeException)
            Right () -> result)
  either E.throwIO pure outcome

exchange :: Session -> B.ByteString -> IO Wire
exchange s request = bounded 30 "web command" $ do
  BC.hPutStrLn (input s) request
  H.hFlush (input s)
  reply <- BC.words <$> BC.hGetLine (output s)
  let decimal word = case readMaybe (BC.unpack word) of
        Just n | n >= (0 :: Integer) -> pure n
        _ -> ioError (userError "invalid web observation")
      channel word = do n <- decimal word; require (n <= 255) "invalid RGB"; pure n
  case map BC.unpack (take 1 reply) of
    ["OK"] | [_] <- reply -> pure Ack
    ["FRAME"] | [_,n,d] <- reply -> Frame <$> decimal n <*> decimal d
    ["PIXEL"] | [_,p,r,g,b] <- reply, BC.unpack p `elem` ["0","1"] ->
      Pixel (BC.unpack p == "1") <$> channel r <*> channel g <*> channel b
    _ -> ioError (userError ("web relay rejected " ++ BC.unpack (BC.takeWhile (/= ' ') request)))

flushWeb :: WebHandle -> T.Text -> IO Wire
flushWeb h wire = withSession False h $ \s ->
  let alphabet = BC.pack "0123456789abcdef"
      hex b = B.pack [B.index alphabet (fromIntegral b `div` 16), B.index alphabet (fromIntegral b `mod` 16)]
      payload = if T.null wire then BC.pack "-" else B.concatMap hex (TE.encodeUtf8 wire)
  in exchange s (BC.pack "FLUSH " <> payload)

callWeb :: WebHandle -> T.Text -> IO Wire
callWeb h cmd = withSession False h $ \s -> do
  require (not (T.any (`elem` "\r\n\0") cmd)) "invalid web command delimiter"
  case T.stripPrefix (T.pack "EXPORT_PPM ") cmd of
    Just path -> require (T.unpack path `elem` paths s) "export requires an owned file"
    Nothing -> require (take 1 (T.words cmd) `elem` map ((:[]) . T.pack) ["PIXEL","RESIZE","FLUSH"]) "invalid web command"
  exchange s (TE.encodeUtf8 cmd)

stopWeb :: WebHandle -> IO [[Integer]]
stopWeb h = withSession True h $ \s -> do
  reply <- exchange s (BC.pack "STOP")
  require (reply == Ack) "invalid stop reply"
  code <- bounded 5 "stop web relay" (P.waitForProcess (process s))
  require (code == ExitSuccess) "web relay failed at stop"
  let work = root s </> "work"
      recover p = do
        Shared.checkLeaf (root s) ("work" </> p)
        st <- F.getSymbolicLinkStatus (work </> p)
        require (F.linkCount st == 1) "aliased web file"
        map toInteger . B.unpack <$> B.readFile (work </> p)
  mapM recover (paths s)
