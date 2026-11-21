-- Negative and lifetime gates for the explicit network transport boundary.
module Main where

import qualified Control.Exception as E
import Control.Concurrent (threadDelay)
import Control.Monad (forM_, unless, void)
import qualified Data.ByteString as B
import Data.Char (isDigit)
import Data.List ((\\))
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import GHC.Clock (getMonotonicTimeNSec)
import qualified System.Directory as D
import System.Environment (getArgs)
import System.FilePath ((</>))
import qualified System.IO as H
import qualified System.Posix.Files as F
import qualified System.Process as P
import qualified NetTransport as N

scratch :: FilePath
scratch = "tmp/net-sandboxes"

relay :: T.Text
relay = T.pack "tmp/ext-tools-build/net-relay"

image :: T.Text
image = T.pack "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

start :: Bool -> [String] -> [[Integer]] -> N.Topology -> IO N.NetHandle
start docker paths contents = N.openNet relay (T.pack scratch) docker image
  [T.pack "DECLARED=visible", T.pack "LC_ALL=C.UTF-8"] (map T.pack paths) contents

stub :: N.Topology
stub = N.TcpStub [N.Rule [] [0, 255, 13, 10]]

clean :: String -> IO ()
clean label = do
  remaining <- D.listDirectory scratch
  unless (null remaining) (error ("workspace residue after " ++ label ++ ": " ++ show remaining))
  args <- getArgs
  if "--docker" `elem` args then do
    containers <- P.readProcess "docker" ["ps", "-a", "--filter", "name=netrelay-", "--format", "{{.ID}}"] ""
    unless (null (words containers)) (error ("container residue after " ++ label ++ ": " ++ containers))
  else pure ()

expectFailure :: String -> IO () -> IO ()
expectFailure label action = do
  result <- E.try action :: IO (Either E.SomeException ())
  case result of
    Left _ -> putStrLn ("PASS " ++ label)
    Right _ -> error ("expected failure: " ++ label)
  clean label

pythonCommand :: Integer -> String -> [Integer] -> T.Text
pythonCommand timeout source input = T.pack (unwords
  ["R", show timeout, N.hexText (T.pack "/usr/bin/python3"), "4",
   N.hexText (T.pack "-I"), N.hexText (T.pack "-S"), N.hexText (T.pack "-c"),
   N.hexText (T.pack source), N.hex input])

run :: N.NetHandle -> Integer -> String -> [Integer] -> IO N.Wire
run h timeout source input = N.callNet h (pythonCommand timeout source input)

assertRun :: N.Wire -> IO ()
assertRun (N.Wire _ err _ _ status timed) =
  unless (status == Just 0 && not timed) (error ("client failed: " ++ show (status, timed, err)))

decode :: [Integer] -> String
decode = T.unpack . TE.decodeUtf8 . B.pack . map fromInteger

assertGone :: [String] -> IO ()
assertGone pids = forM_ pids $ \pid -> do
  unless (not (null pid) && all isDigit pid) (error ("invalid child pid: " ++ pid))
  alive <- D.doesDirectoryExist ("/proc" </> pid)
  unless (not alive) (error ("orphan survived: " ++ pid))

relayPids :: IO [String]
relayPids = do
  absolute <- D.canonicalizePath (T.unpack relay)
  entries <- D.listDirectory "/proc"
  let check pid = E.catch (do
        target <- D.getSymbolicLinkTarget ("/proc" </> pid </> "exe")
        pure [pid | target == absolute]) missing
      missing :: E.IOException -> IO [String]
      missing _ = pure []
  concat <$> mapM check (filter (all isDigit) entries)

unchangedSentinel :: FilePath -> B.ByteString -> IO ()
unchangedSentinel path expected = do
  mode <- F.fileMode <$> F.getSymbolicLinkStatus path
  actual <- B.readFile path
  unless (actual == expected && mode `F.intersectFileModes` F.accessModes == 0o400)
    (error "external sentinel bytes or mode changed")

-- Gates are test-only files inside the disposable work tree. They make output
-- generation deterministic even if process startup is scheduled unusually late.
probeCoverage :: Bool -> IO ()
probeCoverage docker = do
  let source = unlines
        [ "import os,sys,time,socket,select"
        , "blob=bytes(range(256))*1024"
        , "def flood():"
        , " sys.stdout.buffer.write(blob); sys.stdout.buffer.flush()"
        , " sys.stderr.buffer.write(blob); sys.stderr.buffer.flush()"
        , "while open('gate','rb').read()!=b'start': time.sleep(.005)"
        , "flood()"
        , "p=int(sys.argv[1])"
        , "tcp=socket.socket(); tcp.bind(('127.0.0.1',p)); tcp.listen()"
        , "udp=socket.socket(socket.AF_INET,socket.SOCK_DGRAM); udp.bind(('127.0.0.1',p))"
        , "last=b'start'"
        , "while True:"
        , " gate=open('gate','rb').read()"
        , " if gate!=last:"
        , "  last=gate"
        , "  if gate in (b'sleep',b'drain'): flood()"
        , "  if gate==b'exit': break"
        , " for sock in select.select([tcp,udp],[],[],.005)[0]:"
        , "  if sock is udp:"
        , "   b,addr=udp.recvfrom(65535); flood(); udp.sendto(b[::-1],addr)"
        , "  else:"
        , "   c,addr=tcp.accept(); b=b''"
        , "   while True:"
        , "    x=c.recv(4096)"
        , "    if not x: break"
        , "    b+=x"
        , "   if b: flood()"
        , "   c.sendall(b[::-1]); c.close()"
        ]
      payload = concat (replicate 1024 [0 .. 255])
      request = [0, 255, 13, 10, 128, 1]
      verify label expectedWire (N.Wire out err wire captures status timed) = do
        unless (out == payload && err == payload && wire == expectedWire && null captures && status == Nothing && not timed)
          (error (label ++ " daemon drain/probe mismatch: " ++ show (length out, length err, wire, status, timed)))
        putStrLn ("PASS " ++ label ++ " drains both daemon pipes")
  h <- start docker ["gate"] [[]] (N.Daemon (T.pack "/usr/bin/python3")
    (map T.pack ["-I", "-S", "-c", source, "{{PORT}}"]))
  let N.NetHandle _ _ _ root _ _ _ = h
      gate = root </> "work" </> "gate"
      setGate value = do
        (temporary, output) <- H.openBinaryTempFile (root </> "work") "gate-signal-"
        B.hPut output (TE.encodeUtf8 (T.pack value))
        H.hClose output
        F.setFileMode temporary 0o644
        D.renameFile temporary gate
  N.Wire _ _ _ _ _ notReady <- N.callNet h (T.pack "P 30")
  unless notReady (error "unbound daemon port should time out")
  setGate "start"
  N.callNet h (T.pack "P 5000") >>= verify "waitPortReady" []
  N.callNet h (T.pack ("C 5000 " ++ N.hex request)) >>= verify "binary TCP probe and SHUT_WR" (reverse request)
  N.callNet h (T.pack ("G 5000 " ++ N.hex request)) >>= verify "binary UDP probe" (reverse request)
  setGate "sleep"
  N.callNet h (T.pack "S 200") >>= verify "sleepNetMs" []
  setGate "drain"
  threadDelay 100000
  N.callNet h (T.pack "N") >>= verify "drainNet and idle control wait" []
  setGate "exit"
  N.Wire _ _ _ _ daemonExit exitTimed <- N.callNet h (T.pack "S 100")
  unless (daemonExit == Just 0 && not exitTimed) (error "daemon exit status was not observed")
  returned <- N.stopNet h
  unless (returned == [map (fromIntegral . fromEnum) "exit"]) (error "daemon gate ownership return changed")
  clean "daemon probe/drain stress"
  putStrLn "PASS daemon exit status and owned-file return"

suite :: Bool -> IO ()
suite docker = do
  let mode = if docker then "Docker" else "local"
  putStrLn (mode ++ " network lifecycle")
  forM_ [[""], ["../escape"], ["/abs"], ["a/./b"], ["a/../b"], ["a//b"],
         ["a/"], ["a\0b"], ["a", "a"], ["a", "a/b"]] $ \paths ->
    expectFailure ("invalid owned paths " ++ show paths) $
      start docker paths (replicate (length paths) [0, 255]) stub >>= void . N.stopNet
  forM_ [["BAD-NAME=value"], ["A=1", "A=2"], ["A=x\0y"], ["=empty"], ["NO_EQUALS"]] $ \vars ->
    expectFailure ("invalid environment " ++ show vars) $
      N.openNet relay (T.pack scratch) docker image (map T.pack vars) [] [] stub >>= void . N.stopNet
  expectFailure "owned byte bounds" $ start docker ["a"] [[256]] stub >>= void . N.stopNet
  expectFailure "owned content arity" $ start docker ["a"] [] stub >>= void . N.stopNet
  expectFailure "invalid route bytes" $ start docker [] [] (N.HttpStub [] [N.Route (T.pack "GET") (T.pack "/") [-1]]) >>= void . N.stopNet
  expectFailure "invalid daemon argument" $ start docker [] [] (N.Daemon (T.pack "/usr/bin/python3") [T.pack "a\0b"]) >>= void . N.stopNet
  before <- relayPids
  expectFailure "failed daemon exec" $
    start docker ["owned"] [[1]] (N.Daemon (T.pack "/definitely/missing/net-daemon") []) >>= void . N.stopNet
  after <- relayPids
  unless (null (after \\ before)) (error "failed daemon exec left a relay process")
  putStrLn "PASS failed daemon exec leaves no relay process"
  (relativeSentinel, handle) <- H.openBinaryTempFile "tmp/ext-tools-build" "net-sentinel-"
  let sentinelBytes = B.pack [0, 255, 128, 13, 10, 1]
  B.hPut handle sentinelBytes
  H.hClose handle
  sentinel <- D.makeAbsolute relativeSentinel
  F.setFileMode sentinel 0o400
  E.finally (do
    forM_ [False, True] $ \replace -> do
      expectFailure (if replace then "symlink owned readback" else "missing owned readback") $ do
        h <- start docker ["note"] [[1, 2, 3]] stub
        run h 5000 ("import os; os.unlink('note'); " ++
          if replace then "os.symlink(" ++ show sentinel ++ ",'note')" else "pass") [] >>= assertRun
        void (N.stopNet h)
      unchangedSentinel sentinel sentinelBytes
    expectFailure "symlink ancestor readback" $ do
      h <- start docker ["sub/note"] [[7]] stub
      run h 5000 ("import os; os.unlink('sub/note'); os.rmdir('sub'); os.symlink(" ++ show sentinel ++ ",'sub')") [] >>= assertRun
      void (N.stopNet h)
    unchangedSentinel sentinel sentinelBytes
    putStrLn "PASS cleanup preserves external sentinel bytes and 0400 mode") (D.removeFile sentinel)
  h <- start docker ["nested/bytes"] [[0 .. 255]] stub
  roots <- D.listDirectory scratch
  unless (length roots == 1) (error "expected one active workspace")
  forM_ roots $ \root -> do
    modeBits <- F.fileMode <$> F.getSymbolicLinkStatus (scratch </> root)
    unless (modeBits `F.intersectFileModes` F.accessModes == 0o700) (error "workspace root is not 0700")
  returned <- N.stopNet h
  unless (returned == [[0 .. 255]]) (error "binary owned readback changed")
  clean "binary readback"
  putStrLn "PASS private workspace and all 256 owned octets"
  expectFailure "call after stop" (void (N.callNet h (T.pack "N")))
  expectFailure "double stop" (void (N.stopNet h))
  failed <- start docker [] [] stub
  expectFailure "invalid command closes handle" (void (N.callNet failed (T.pack "INVALID")))
  expectFailure "call after failure" (void (N.callNet failed (T.pack "N")))
  expectFailure "stop after failure" (void (N.stopNet failed))
  timedHandle <- start docker [] [] stub
  started <- getMonotonicTimeNSec
  N.Wire childBytes _ _ _ timeoutStatus timeoutFlag <- run timedHandle 200
    "import os,time; pid=os.fork(); print(os.getpid(),flush=True); time.sleep(60)" []
  ended <- getMonotonicTimeNSec
  let elapsed = (ended - started) `div` 1000000
  unless (timeoutStatus == Just 124 && timeoutFlag && elapsed >= 100 && elapsed < 2500)
    (error ("timeout deadline mismatch: " ++ show (timeoutStatus, timeoutFlag, elapsed)))
  unless docker (assertGone (words (decode childBytes)))
  run timedHandle 5000 "import os; assert set(os.environ)=={'DECLARED','LC_ALL'}; assert 'HOST_SECRET_LEAK' not in os.environ" [] >>= assertRun
  void (N.stopNet timedHandle)
  clean "timeout and reuse"
  putStrLn "PASS timeout kills/reaps process group and session remains usable with exact environment"
  orphan <- start docker [] [] stub
  N.Wire orphanBytes _ _ _ status timed <- run orphan 5000
    "import os,time; pid=os.fork(); print(pid,flush=True) if pid else None; time.sleep(60) if not pid else None" []
  unless (status == Just 0 && not timed) (error "successful parent did not finish")
  unless docker (assertGone (words (decode orphanBytes)))
  void (N.stopNet orphan)
  clean "orphan cleanup"
  putStrLn "PASS successful client exit reaps surviving descendants"
  daemon <- start docker ["pids"] [[]] (N.Daemon (T.pack "/usr/bin/python3")
    (map T.pack ["-I", "-S", "-c", "import os,time; pid=os.fork(); open('pids','w').write(str(os.getpid())+' '+str(pid)) if pid else None; time.sleep(60)"]))
  void (N.callNet daemon (T.pack "S 100"))
  daemonFiles <- N.stopNet daemon
  case daemonFiles of
    [pidBytes] -> do
      unless (length (words (decode pidBytes)) == 2) (error "daemon did not write both pids")
      unless docker (assertGone (words (decode pidBytes)))
    _ -> error "missing daemon owned file"
  clean "daemon group stop"
  putStrLn "PASS daemon stop terminates and reaps its whole process group"
  probeCoverage docker
  binary <- start docker [] [] stub
  let payload = concat (replicate 1024 [0 .. 255])
  N.Wire out err _ _ binStatus binTimed <- run binary 5000
    "import sys; b=bytes(range(256))*1024; sys.stdout.buffer.write(b); sys.stdout.buffer.flush(); sys.stderr.buffer.write(b); sys.stderr.buffer.flush(); x=sys.stdin.buffer.read(); sys.stdout.buffer.write(x[::-1])" payload
  unless (out == payload ++ reverse payload && err == payload && binStatus == Just 0 && not binTimed)
    (error "concurrent binary pipes deadlocked or changed bytes")
  void (N.stopNet binary)
  clean "large binary pipes"
  putStrLn "PASS concurrent large binary stdin/stdout/stderr"

main :: IO ()
main = do
  D.createDirectoryIfMissing True scratch
  suite False
  args <- getArgs
  if "--docker" `elem` args then suite True else pure ()
  clean "final suite"
  putStrLn "ALL NETWORK LIFECYCLE TESTS PASS"
