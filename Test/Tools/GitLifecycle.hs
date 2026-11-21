-- Adversarial resource-lifetime tests for the trusted Git transport boundary.
module Main where

import qualified Control.Exception as E
import Control.Monad (forM_, unless, void)
import qualified Data.ByteString as B
import qualified Data.Text as T
import GHC.Clock (getMonotonicTimeNSec)
import qualified System.Directory as D
import System.FilePath ((</>))
import qualified System.IO as H
import qualified System.Posix.Files as F
import qualified GitTransport as G

scratch :: FilePath
scratch = "tmp/git-sandboxes"

startWith :: String -> [String] -> [String] -> [[Integer]] -> IO G.GitHandle
startWith branch env paths contents = G.openGit
  (T.pack "tmp/ext-tools-build/git-relay") (T.pack scratch) False T.empty
  (T.pack branch) (T.pack "Probe Author") (T.pack "probe@example.invalid")
  1700000000 (map T.pack env) (map T.pack paths) contents

start :: [String] -> [[Integer]] -> IO G.GitHandle
start = startWith "main" ["DECLARED=visible", "LC_ALL=C"]

clean :: String -> IO ()
clean label = do
  remaining <- D.listDirectory scratch
  unless (null remaining) (error ("Git workspace residue after " ++ label ++ ": " ++ show remaining))

expectFailure :: String -> IO () -> IO ()
expectFailure label action = do
  result <- E.try action :: IO (Either E.SomeException ())
  case result of
    Left _ -> putStrLn ("PASS " ++ label)
    Right _ -> error ("expected failure: " ++ label)
  clean label

write :: String -> [Integer] -> T.Text
write path contents = T.pack (unwords ["W", G.hexText (T.pack path), G.hex contents])

command :: String -> [String] -> T.Text
command op args = T.pack (unwords (op : map (G.hexText . T.pack) args))

target :: Integer -> String -> [String] -> [Integer] -> T.Text
target timeout exe args input = T.pack (unwords
  (["R", show timeout, G.hexText (T.pack exe), show (length args)]
   ++ map (G.hexText . T.pack) args ++ [G.hex input]))

python :: Integer -> String -> T.Text
python timeout source = target timeout "/usr/bin/python3" ["-I", "-S", "-c", source] []

runPython :: G.GitHandle -> Integer -> String -> IO G.Wire
runPython h timeout source = G.callGit h (python timeout source)

assertSuccess :: G.Wire -> IO ()
assertSuccess (G.Wire _ _ _ status timed _) =
  unless (status == Just 0 && not timed) (error "target command failed")

unchangedSentinel :: FilePath -> B.ByteString -> IO ()
unchangedSentinel path expected = do
  st <- F.getSymbolicLinkStatus path
  actual <- B.readFile path
  unless (F.isRegularFile st && actual == expected
    && F.fileMode st `F.intersectFileModes` F.accessModes == 0o400)
    (error "external sentinel bytes or 0400 mode changed")

main :: IO ()
main = do
  D.createDirectoryIfMissing True scratch
  clean "suite start"
  forM_ [[".git"], [".git/config"], [".git/objects/file"], [""], ["../escape"],
         ["/abs"], ["a/./b"], ["a/../b"], ["a//b"], ["a/"], ["a\0b"],
         ["a", "a"], ["a", "a/b"], ["a/b", "a"]] $ \paths ->
    expectFailure ("invalid owned paths " ++ show paths) $ do
      h <- start paths (replicate (length paths) [0, 255])
      void (G.stopGit h)
  forM_ ["-bad", "", "/bad", "HEAD", "a..b", "a//b", "a/", "a.", ".bad",
         "a/.bad", "a.lock", "a.lock/b", "x@{y", "bad name", "a\0b"] $ \branch ->
    expectFailure ("invalid branch " ++ show branch) $ do
      h <- startWith branch [] [] []
      void (G.stopGit h)
  forM_ [["BAD-NAME=value"], ["A=1", "A=2"], ["A=x\0y"], ["=empty"], ["NO_EQUALS"]] $ \vars ->
    expectFailure ("invalid environment " ++ show vars) $ do
      h <- startWith "main" vars [] []
      void (G.stopGit h)
  expectFailure "owned byte bounds" $ start ["a"] [[256]] >>= void . G.stopGit
  expectFailure "owned contents arity" $ start ["a"] [] >>= void . G.stopGit
  forM_ [".git", ".git/config", "../escape", "/abs", "a/../b", "a//b", "a\0b"] $ \path ->
    expectFailure ("invalid gitWriteFile " ++ show path) $ do
      h <- start [] []
      void (G.callGit h (write path [0, 255]))
      void (G.stopGit h)
  forM_ [".git", ".git/config", "../escape"] $ \path ->
    expectFailure ("invalid gitRemoveFile " ++ show path) $ do
      h <- start [] []
      void (G.callGit h (command "U" [path]))
      void (G.stopGit h)
  -- A malicious target can replace an owned leaf or an ancestor. stopGit must
  -- reject both without chmod/write traversal to this external 0400 sentinel.
  (sentinelRelative, handle) <- H.openBinaryTempFile "tmp/ext-tools-build" "git-sentinel-"
  let sentinelBytes = B.pack [0, 255, 128, 13, 10, 1]
  B.hPut handle sentinelBytes
  H.hClose handle
  sentinel <- D.makeAbsolute sentinelRelative
  F.setFileMode sentinel 0o400
  E.finally (do
    forM_ [False, True] $ \replace -> do
      expectFailure (if replace then "symlink owned readback" else "deleted owned readback") $ do
        h <- start ["note"] [[1, 2, 3]]
        let source = "import os; os.unlink('note')" ++
              if replace then "; os.symlink(" ++ show sentinel ++ ", 'note')" else ""
        runPython h 2000 source >>= assertSuccess
        void (G.stopGit h)
      unchangedSentinel sentinel sentinelBytes
    expectFailure "symlink ancestor readback" $ do
      h <- start ["sub/note"] [[7]]
      runPython h 2000 ("import os; os.unlink('sub/note'); os.rmdir('sub'); os.symlink(" ++ show sentinel ++ ", 'sub')") >>= assertSuccess
      void (G.stopGit h)
    unchangedSentinel sentinel sentinelBytes
    expectFailure "gitWriteFile through symlink ancestor" $ do
      h <- start [] []
      runPython h 2000 ("import os; os.symlink(" ++ show sentinel ++ ", 'sub')") >>= assertSuccess
      void (G.callGit h (write "sub/escape" [9]))
      void (G.stopGit h)
    unchangedSentinel sentinel sentinelBytes
    expectFailure "gitWriteFile replacing symlink leaf" $ do
      h <- start ["note"] [[1]]
      runPython h 2000 ("import os; os.unlink('note'); os.symlink(" ++ show sentinel ++ ", 'note')") >>= assertSuccess
      void (G.callGit h (write "note" [9]))
      void (G.stopGit h)
    unchangedSentinel sentinel sentinelBytes
    putStrLn "PASS cleanup preserves external sentinel bytes and 0400 mode") (D.removeFile sentinel)
  h <- start ["nested/bytes"] [[0 .. 255]]
  roots <- D.listDirectory scratch
  unless (length roots == 1) (error "expected one active Git root")
  forM_ roots $ \root -> do
    mode <- F.fileMode <$> F.getSymbolicLinkStatus (scratch </> root)
    unless (mode `F.intersectFileModes` F.accessModes == 0o700) (error "active Git root is not 0700")
  restored <- G.stopGit h
  unless (restored == [[0 .. 255]]) (error "raw binary owned Git readback changed")
  putStrLn "PASS active root 0700 and binary owned readback"
  expectFailure "call after stop" (void (G.callGit h (T.pack "S")))
  expectFailure "double stop" (void (G.stopGit h))
  failed <- start [] []
  expectFailure "failed command closes handle" (void (G.callGit failed (write "../bad" [0])))
  expectFailure "call after failed call" (void (G.callGit failed (T.pack "S")))
  expectFailure "stop after failed call" (void (G.stopGit failed))
  exact <- start [] []
  G.Wire envOut envErr _ envStatus envTimed _ <- G.callGit exact (target 2000 "/usr/bin/env" [] [])
  unless (envOut == map (toInteger . fromEnum) "DECLARED=visible\nLC_ALL=C\n"
    && null envErr && envStatus == Just 0 && not envTimed) (error "target environment is not exact")
  void (G.stopGit exact)
  clean "exact target environment"
  putStrLn "PASS target exact environment excludes inherited secrets"
  binary <- start [] []
  let payload = concat (replicate 256 [0 .. 255])
      source = "import sys; b=bytes(range(256))*256; sys.stdout.buffer.write(b); sys.stdout.buffer.flush(); sys.stderr.buffer.write(b); sys.stderr.buffer.flush(); x=sys.stdin.buffer.read(); sys.stdout.buffer.write(x[::-1])"
  G.Wire out err _ status timed summary <- G.callGit binary
    (target 5000 "/usr/bin/python3" ["-I", "-S", "-c", source] payload)
  unless (out == payload ++ reverse payload && err == payload && status == Just 0
    && not timed && summary == Nothing) (error "concurrent binary target transfer changed bytes")
  void (G.stopGit binary)
  clean "binary target transfer"
  putStrLn "PASS concurrent binary stdin/stdout/stderr"
  timeoutHandle <- start [] []
  before <- getMonotonicTimeNSec
  G.Wire childBytes _ _ timeoutStatus timeoutFlag _ <- runPython timeoutHandle 200
    "import os,time; pid=os.fork(); print(os.getpid(),flush=True) if pid==0 else None; time.sleep(5)"
  after <- getMonotonicTimeNSec
  let elapsed = (after - before) `div` 1000000
      pids = words (map (toEnum . fromInteger) childBytes)
  unless (timeoutStatus == Just 124 && timeoutFlag && elapsed >= 100 && elapsed < 2500)
    (error ("target timeout mismatch: " ++ show elapsed))
  forM_ pids $ \pid -> do
    alive <- D.doesDirectoryExist ("/proc" </> pid)
    unless (not alive) (error ("target descendant survived timeout: " ++ pid))
  void (G.stopGit timeoutHandle)
  clean "timeout cleanup"
  putStrLn "PASS timeout kills and reaps child/grandchild"
  putStrLn "ALL GIT LIFECYCLE TESTS PASS"
