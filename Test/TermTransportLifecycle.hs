-- Failure-path tests for the resource boundary. No terminal interpretation.
module Main where

import qualified Control.Exception as E
import Control.Monad (unless, void, forM_)
import qualified Data.Text as T
import qualified System.Directory as D
import qualified System.Posix.Files as F
import System.FilePath ((</>))
import qualified TermTransport as TT

scratch :: FilePath
scratch = "tmp/term-sandboxes"

start :: Bool -> String -> [String] -> [String] -> IO TT.TermHandle
start pipe code paths contents = TT.openTerm
  (T.pack "tmp/term-build/term-relay") (T.pack scratch) False T.empty pipe
  (T.pack "/usr/bin/python3") (map T.pack ["-I", "-S", "-c", code])
  [T.pack "LC_ALL=C.UTF-8"] 24 80 (map T.pack paths) (map T.pack contents)

expectFailure :: String -> IO () -> IO ()
expectFailure label action = do
  result <- E.try action :: IO (Either E.SomeException ())
  case result of
    Left _ -> putStrLn ("PASS " ++ label)
    Right _ -> error ("expected failure: " ++ label)
  remaining <- D.listDirectory scratch
  unless (null remaining) (error ("workspace residue after " ++ label))

main :: IO ()
main = do
  sentinel <- D.makeAbsolute "tmp/term-cleanup-sentinel"
  writeFile sentinel "untouched"
  F.setFileMode sentinel 0o400
  forM_ [["../escape"], ["/tmp/absolute"], ["a/./b"], ["a", "a"], ["a", "a/b"]] $ \paths ->
    expectFailure ("reject owned paths " ++ show paths) $ do
      h <- start True "pass" paths (replicate (length paths) "data")
      void (TT.stopTerm h)
  expectFailure "failed exec cleans workspace" $ do
    h <- TT.openTerm (T.pack "tmp/term-build/term-relay") (T.pack scratch) False T.empty True
      (T.pack "/nonexistent/codetransport-command") [] [] 24 80 [] []
    void (TT.stopTerm h)
  expectFailure "allTTY rejects independent EOF and cleans live child" $ do
    h <- start False "import time; time.sleep(60)" [] []
    void (TT.callTerm h (T.pack "C"))
    void (TT.stopTerm h)
  forM_ [("symlink", "os.unlink('note'); os.symlink(" ++ show sentinel ++ ", 'note')"),
         ("missing file", "os.unlink('note')"),
         ("binary text file", "open('note','wb').write(bytes([255]))")] $ \(label, change) ->
    expectFailure (label ++ " readback fails and cleans workspace") $ do
      h <- start True ("import os; " ++ change ++ "; os.write(1, b'changed')") ["note"] ["original"]
      let await 0 = error "fixture failed to acknowledge its file edit"
          await n = do
            TT.Wire _ out _ _ <- TT.callTerm h (T.pack "D")
            if null out then await (n - 1 :: Int) else pure ()
      await 100
      void (TT.stopTerm h)
  sentinelMode <- F.fileMode <$> F.getFileStatus sentinel
  contents <- readFile sentinel
  unless (sentinelMode `F.intersectFileModes` F.accessModes == 0o400 && contents == "untouched")
    (error "cleanup modified the external symlink target")
  D.removeFile sentinel
  putStrLn "PASS cleanup preserves external symlink target bytes and permissions"
  -- Even the writable Docker subtree is underneath a private mkdtemp parent.
  h <- start True "import time; time.sleep(60)" [] []
  roots <- D.listDirectory scratch
  forM_ roots $ \root -> do
    mode <- F.fileMode <$> F.getFileStatus (scratch </> root)
    unless (mode `F.intersectFileModes` F.accessModes == 0o700) (error "session root is not private")
  void (TT.stopTerm h)
  expectFailure "double stop is rejected without residue" (void (TT.stopTerm h))
