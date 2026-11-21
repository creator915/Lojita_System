{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar, threadDelay)
import qualified Control.Exception as E
import Control.Monad (forM_, unless, void)
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified System.Directory as D
import System.Environment (lookupEnv, setEnv)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import qualified System.Posix.Files as F
import qualified System.Posix.Temp as Temp
import qualified System.Process as P
import qualified System.Timeout as Timeout
import qualified WebTransport as W

scratch :: FilePath
scratch = "tmp/web-lifecycle-sandboxes"

relay :: T.Text
relay = "tmp/web-build/web-relay"

image :: T.Text
image = "programbench/junegunn_1776_fzf.b56d614:task_cleanroom_v6"

start :: Bool -> [T.Text] -> IO W.WebHandle
start docker files = W.openWeb relay (T.pack scratch) docker image 8 8 files (map (const [0,255]) files)

check :: Bool -> String -> IO ()
check good msg = unless good (fail msg)

clean :: IO ()
clean = D.listDirectory scratch >>= \ps -> check (null ps) ("web workspace residue: " ++ show ps)

fails :: String -> IO a -> IO ()
fails label action = do
  attempt <- E.try (void action) :: IO (Either E.SomeException ())
  case attempt of
    Right () -> fail ("expected failure: " ++ label)
    Left _ -> clean >> putStrLn ("PASS " ++ label)

liveRoot :: IO FilePath
liveRoot = do
  [subdir] <- D.listDirectory scratch
  pure (scratch </> subdir)

symlinkCase :: Bool -> FilePath -> Bool -> Bool -> IO ()
symlinkCase docker sentinel parent atExport = do
  h <- start docker ["nested/frame.ppm"]
  work <- (</> "work") <$> liveRoot
  if parent then do
    D.removePathForcibly (work </> "nested")
    F.createSymbolicLink sentinel (work </> "nested")
  else do
    D.removeFile (work </> "nested/frame.ppm")
    F.createSymbolicLink (sentinel </> "frame.ppm") (work </> "nested/frame.ppm")
  let label = (if parent then "parent " else "leaf ") ++ (if atExport then "export" else "restore")
  fails ("symlink " ++ label) $
    if atExport then void (W.callWeb h "EXPORT_PPM nested/frame.ppm") else void (W.stopWeb h)
  fails "failed handle is closed" (W.callWeb h "PIXEL 0 0")

suite :: Bool -> FilePath -> IO ()
suite docker sentinel = do
  putStrLn (if docker then "Docker lifecycle" else "Local lifecycle")
  forM_ [[""],["../escape"],["/absolute"],["a/./b"],["a//b"],["a/"],["a\0b"],
         ["a","a"],["a","a/b"],["a/b","a"],["a\nb"]] $ \ps ->
    fails ("owned paths " ++ show ps) (start docker ps)
  h <- start docker ["nested/frame.ppm","data"]
  dir <- liveRoot
  mode <- F.fileMode <$> F.getFileStatus dir
  check (F.intersectFileModes mode F.accessModes == 0o700) "session root mode"
  frame <- W.flushWeb h "FILL 0 255 128 0 0 8 8\nSAVE\nCLIP 1 1 3 2\nSTROKE 9 8 7 0 1 4 2\nRESTORE"
  check (frame == W.Frame 5 0) "full frame count/depth"
  -- Concurrent requests may arrive in either order, with distinct replies.
  a <- newEmptyMVar
  b <- newEmptyMVar
  void $ forkIO $ W.callWeb h "PIXEL 0 0" >>= putMVar a
  void $ forkIO $ W.callWeb h "PIXEL 1 1" >>= putMVar b
  pa <- takeMVar a
  pb <- takeMVar b
  check (pa == W.Pixel True 0 255 128 && pb == W.Pixel True 9 8 7) "serialized pixel replies"
  _ <- W.flushWeb h "LINE 7 8 9 0 7 5 7\nTEXT 21 22 23 0 0 8 8 41"
  lineInk <- W.callWeb h "PIXEL 2 7"
  textInk <- W.callWeb h "PIXEL 6 0"
  clear <- W.callWeb h "PIXEL 0 0"
  check (lineInk == W.Pixel True 7 8 9 && textInk == W.Pixel True 21 22 23 &&
         clear == W.Pixel False 0 0 0) "line, glyph and transparent samples"
  void $ W.callWeb h "EXPORT_PPM nested/frame.ppm"
  [ppm, restored] <- W.stopWeb h
  check (take 2 ppm == [80,54] && restored == [0,255]) "file restoration"
  fails "call after stop" (W.callWeb h "PIXEL 0 0")
  fails "stop twice" (W.stopWeb h)
  forM_ ["EXPORT_PPM ../escape","EXPORT_PPM sibling","PIXEL 0 0\nSTOP","PIXEL 0 0 extra","RESIZE 2 2 extra","FLUSH 0","FLUSH 524553544f5245"] $ \cmd -> do
    bad <- start docker ["out"]
    fails ("reject request " ++ show cmd) (W.callWeb bad cmd)
    fails "cannot reuse failed handle" (W.stopWeb bad)
  forM_ [False, True] $ \parent ->
    forM_ [False, True] $ \atExport -> symlinkCase docker sentinel parent atExport
  before <- B.readFile (sentinel </> "frame.ppm")
  check (before == B.pack [0,255,193]) "external sentinel changed"
  clean

-- A deliberately slow local fixture makes cancellation of a pending reply
-- deterministic. Its child shares the process group created by the transport.
cancelPending :: FilePath -> IO ()
cancelPending dir = do
  let fixture = dir </> "slow-relay"
  writeFile fixture $ unlines ["#!/bin/sh", "test -z \"$WEB_HOST_SECRET\" || exit 9",
    "printf 'READY\\n'", "read -r request", "sleep 60 &", "echo $! > child", "wait"]
  F.setFileMode fixture 0o700
  setEnv "WEB_HOST_SECRET" "must-stay-outside"
  h <- W.openWeb (T.pack fixture) (T.pack scratch) False "" 2 2 ["child"] [[]]
  root <- liveRoot
  done <- newEmptyMVar
  thread <- forkIO $ (E.try (W.callWeb h "PIXEL 0 0") :: IO (Either E.SomeException W.Wire)) >>= putMVar done
  let awaitPid = do
        contents <- B.readFile (root </> "work/child")
        if B.null contents then threadDelay 10000 >> awaitPid
                           else pure (read (map (toEnum . fromIntegral) (B.unpack contents)) :: Int)
  child <- Timeout.timeout 2000000 awaitPid
  E.throwTo thread E.ThreadKilled
  _ <- takeMVar done
  case child of
    Nothing -> fail "fixture child did not start"
    Just pid -> do
      let proc = "/proc/" ++ show pid ++ "/stat"
      let dead = do
            status <- E.try (B.readFile proc) :: IO (Either E.IOException B.ByteString)
            case status of
              Left _ -> pure True
              Right bytes -> pure (take 1 (drop 2 (words (map (toEnum . fromIntegral) (B.unpack bytes)))) == ["Z"])
      let awaitExit = do exited <- dead
                         unless exited (threadDelay 10000 >> awaitExit)
      exited <- Timeout.timeout 2000000 awaitExit
      check (exited == Just ()) "cancelled relay left a live descendant"
  fails "cancelled group closed and removed" (W.stopWeb h)

main :: IO ()
main = do
  D.createDirectoryIfMissing True scratch
  clean
  E.bracket (Temp.mkdtemp "tmp/web-build/lifecycle-") D.removePathForcibly $ \tmp -> do
    dir <- D.makeAbsolute tmp
    B.writeFile (dir </> "frame.ppm") (B.pack [0,255,193])
    suite False dir
    fails "failed relay startup cleans files"
      (W.openWeb (T.pack (dir </> "missing")) (T.pack scratch) False "" 2 2 ["x"] [[1]])
    cancelPending dir
    docker <- P.rawSystem "/bin/sh" ["-c","docker info >/dev/null 2>&1"]
    required <- lookupEnv "REQUIRE_DOCKER"
    case (docker, required) of
      (ExitSuccess, _) -> suite True dir
      (_, Just "1") -> fail "Docker required and unavailable"
      _ -> putStrLn "SKIP Docker lifecycle (docker info unavailable)"
    clean
