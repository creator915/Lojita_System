-- Negative gates exercise the transport boundary without Agda's typed wrapper.
module Main where

import qualified Control.Exception as E
import Control.Monad (forM_, unless, void)
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import GHC.Clock (getMonotonicTimeNSec)
import qualified System.Directory as D
import System.FilePath ((</>))
import qualified System.IO as H
import qualified System.Posix.Files as F
import qualified FsTransport as FS

scratch :: FilePath
scratch = "tmp/fs-sandboxes"

start :: [String] -> [[Integer]] -> [FS.Fixture] -> IO FS.FsHandle
start paths contents fixtures = FS.openFs
  (T.pack "tmp/ext-tools-build/fs-relay") (T.pack scratch) False T.empty
  [T.pack "DECLARED=visible"] (map T.pack paths) contents fixtures

clean :: String -> IO ()
clean label = do
  remaining <- D.listDirectory scratch
  unless (null remaining) (error ("workspace residue after " ++ label ++ ": " ++ show remaining))

expectFailure :: String -> IO () -> IO ()
expectFailure label action = do
  result <- E.try action :: IO (Either E.SomeException ())
  case result of
    Left _ -> putStrLn ("PASS " ++ label)
    Right _ -> error ("expected failure: " ++ label)
  clean label

command :: String -> String -> T.Text
command op path = T.pack (op ++ " " ++ FS.hexText (T.pack path))

python :: Integer -> String -> [Integer] -> T.Text
python timeout source input = T.pack (unwords
  ["R", show timeout, FS.hexText (T.pack "/usr/bin/python3"), "4",
   FS.hexText (T.pack "-I"), FS.hexText (T.pack "-S"), FS.hexText (T.pack "-c"),
   FS.hexText (T.pack source), FS.hex input])

run :: FS.FsHandle -> Integer -> String -> [Integer] -> IO FS.Wire
run h timeout source input = FS.callFs h (python timeout source input)

unchangedSentinel :: FilePath -> B.ByteString -> IO ()
unchangedSentinel path expected = do
  mode <- F.fileMode <$> F.getSymbolicLinkStatus path
  actual <- B.readFile path
  unless (actual == expected && mode `F.intersectFileModes` F.accessModes == 0o400)
    (error "external sentinel bytes or mode changed")

main :: IO ()
main = do
  D.createDirectoryIfMissing True scratch
  forM_ [[""], ["../escape"], ["/abs"], ["a/./b"], ["a/../b"], ["a//b"],
         ["a/"], ["a\0b"], ["a", "a"], ["a", "a/b"]] $ \paths ->
    expectFailure ("invalid owned paths " ++ show paths) $ do
      h <- start paths (replicate (length paths) [0, 255]) []
      void (FS.stopFs h)
  let dir p = FS.FixDir (T.pack p) 493
      file p = FS.FixFile (T.pack p) 420 [0, 255]
      link p = FS.FixSymlink (T.pack p) (T.pack "../outside")
  forM_ [[dir "../escape"], [file "/abs"], [link "a/./b"], [dir "a", file "a"],
         [file "a", file "a/b"], [link "a", file "a/b"], [link ""],
         [FS.FixSymlink (T.pack "a") (T.pack "bad\0target")]] $ \fixtures ->
    expectFailure ("invalid fixtures " ++ show fixtures) $ do
      h <- start [] [] fixtures
      void (FS.stopFs h)
  expectFailure "owned/fixture duplicate" $ start ["a"] [[1]] [dir "a"] >>= void . FS.stopFs
  expectFailure "owned/fixture parent collision" $ start ["a"] [[1]] [dir "a/b"] >>= void . FS.stopFs
  forM_ [["BAD-NAME=value"], ["A=1", "A=2"], ["A=x\0y"], ["=empty"]] $ \vars ->
    expectFailure ("invalid environment " ++ show vars) $ do
      h <- FS.openFs (T.pack "tmp/ext-tools-build/fs-relay") (T.pack scratch)
        False T.empty (map T.pack vars) [] [] []
      void (FS.stopFs h)
  expectFailure "owned byte bounds" $ start ["a"] [[256]] [] >>= void . FS.stopFs
  -- Each modifying operation rejects a symlink ancestor, including mkdir and
  -- chmod (which could otherwise reach arbitrary external objects).
  forM_ ["W 00", "D 493", "L 78", "M 420", "U"] $ \operation ->
    expectFailure ("symlink ancestor " ++ operation) $ do
      h <- start [] [] [FS.FixSymlink (T.pack "sub") (T.pack "/tmp")]
      let (op, rest) = break (== ' ') operation
      void (FS.callFs h (T.pack (op ++ " " ++ FS.hexText (T.pack "sub/fs-relay-pwn") ++ rest)))
      void (FS.stopFs h)
  -- The sentinel's permissions prohibit accidental writeback; cleanup must not
  -- chmod or follow the replacement link, including a linked ancestor.
  (sentinelRelative, handle) <- H.openBinaryTempFile "tmp/ext-tools-build" "fs-sentinel-"
  let sentinelBytes = B.pack [0, 255, 128, 13, 10, 1]
  B.hPut handle sentinelBytes
  H.hClose handle
  sentinel <- D.makeAbsolute sentinelRelative
  F.setFileMode sentinel 0o400
  E.finally (do
    forM_ [False, True] $ \replace -> do
      expectFailure (if replace then "symlink owned readback" else "missing owned readback") $ do
        h <- start ["note"] [[1, 2, 3]] []
        void (FS.callFs h (command "U" "note"))
        if replace then void (FS.callFs h (T.pack ("L " ++ FS.hexText (T.pack "note") ++ " " ++ FS.hexText (T.pack sentinel)))) else pure ()
        void (FS.stopFs h)
      unchangedSentinel sentinel sentinelBytes
    expectFailure "symlink ancestor readback" $ do
      h <- start ["sub/note"] [[7]] []
      void (FS.callFs h (command "U" "sub/note"))
      void (FS.callFs h (command "U" "sub"))
      void (FS.callFs h (T.pack ("L " ++ FS.hexText (T.pack "sub") ++ " " ++ FS.hexText (T.pack sentinel))))
      void (FS.stopFs h)
    unchangedSentinel sentinel sentinelBytes
    putStrLn "PASS cleanup preserves external sentinel bytes and 0400 mode") (D.removeFile sentinel)
  h <- start ["nested/bytes"] [[0 .. 255]] [dir "fixture", file "fixture/data"]
  roots <- D.listDirectory scratch
  unless (length roots == 1) (error "expected one active root")
  forM_ roots $ \root -> do
    mode <- F.fileMode <$> F.getSymbolicLinkStatus (scratch </> root)
    unless (mode `F.intersectFileModes` F.accessModes == 0o700) (error "active root is not 0700")
  restored <- FS.stopFs h
  unless (restored == [[0 .. 255]]) (error "raw binary owned readback changed")
  putStrLn "PASS active root 0700 and binary owned readback"
  expectFailure "call after stop" (void (FS.callFs h (T.pack "S")))
  expectFailure "double stop" (void (FS.stopFs h))
  restricted <- start ["locked/data"] [[0, 255, 128]] []
  void (FS.callFs restricted (command "M" "locked/data" <> T.pack " 0"))
  void (FS.callFs restricted (command "M" "locked" <> T.pack " 0"))
  let FS.FsHandle _ _ _ restrictedRoot _ _ _ = restricted
  restrictedBytes <- FS.readOwned (restrictedRoot </> "work") "locked/data"
  FS.Wire _ _ _ _ restrictedEntries <- FS.callFs restricted (T.pack "S")
  unless (restrictedBytes == [0, 255, 128] && restrictedEntries ==
    [FS.Entry (T.pack "locked") 1 0 [], FS.Entry (T.pack "locked/data") 0 0 [0, 255, 128]])
    (error "readback did not restore exact mode000 parent/file permissions")
  returnedRestricted <- FS.stopFs restricted
  unless (returnedRestricted == [[0, 255, 128]]) (error "mode000 owned readback failed")
  clean "mode000 readback"
  putStrLn "PASS mode000 owned parent/file readback restores exact permissions"
  failed <- start [] [] []
  expectFailure "failed command closes handle" (void (FS.callFs failed (command "W" "../bad" <> T.pack " 00")))
  expectFailure "call after failed call" (void (FS.callFs failed (T.pack "S")))
  expectFailure "stop after failed call" (void (FS.stopFs failed))
  -- Output fills both pipes before the child reads its much larger input.
  -- Concurrent relay polling must prevent the three-pipe deadlock.
  binary <- start [] [] []
  let payload = concat (replicate 1024 [0 .. 255])
  FS.Wire out err status timed entries <- run binary 5000
    "import sys; b=bytes(range(256))*1024; sys.stdout.buffer.write(b); sys.stdout.buffer.flush(); sys.stderr.buffer.write(b); sys.stderr.buffer.flush(); x=sys.stdin.buffer.read(); sys.stdout.buffer.write(x[::-1])" payload
  unless (out == payload ++ reverse payload && err == payload && status == Just 0 && not timed && null entries)
    (error "large concurrent binary transfer changed bytes")
  void (FS.stopFs binary)
  clean "large binary transfer"
  putStrLn "PASS large concurrent binary stdin/stdout/stderr"
  timedHandle <- start [] [] []
  before <- getMonotonicTimeNSec
  FS.Wire childBytes _ timeoutStatus timeoutFlag _ <- run timedHandle 200
    "import os,time; pid=os.fork(); print(os.getpid(),flush=True) if pid==0 else None; time.sleep(5)" []
  after <- getMonotonicTimeNSec
  let elapsed = (after - before) `div` 1000000
      pidText = T.unpack (TE.decodeUtf8 (B.pack (map fromInteger childBytes)))
  unless (timeoutStatus == Just 124 && timeoutFlag && elapsed >= 100 && elapsed < 2500)
    (error ("timeout deadline mismatch: " ++ show elapsed))
  forM_ (words pidText) $ \pid -> do
    alive <- D.doesDirectoryExist ("/proc" </> pid)
    unless (not alive) (error ("orphan survived timeout: " ++ pid))
  void (FS.stopFs timedHandle)
  clean "timeout"
  putStrLn "PASS monotonic timeout kills and reaps child/grandchild"
  orphan <- start [] [] []
  FS.Wire orphanBytes _ orphanStatus orphanTimed _ <- run orphan 2000
    "import os,time; pid=os.fork(); print(pid,flush=True) if pid else None; time.sleep(60) if not pid else None" []
  let orphanPid = words (T.unpack (TE.decodeUtf8 (B.pack (map fromInteger orphanBytes))))
  unless (orphanStatus == Just 0 && not orphanTimed) (error "parent exit did not finish command")
  forM_ orphanPid $ \pid -> do
    alive <- D.doesDirectoryExist ("/proc" </> pid)
    unless (not alive) (error ("orphan survived parent exit: " ++ pid))
  void (FS.stopFs orphan)
  clean "orphan cleanup"
  putStrLn "PASS successful parent exit reaps remaining process group"
  putStrLn "ALL FILESYSTEM LIFECYCLE TESTS PASS"
