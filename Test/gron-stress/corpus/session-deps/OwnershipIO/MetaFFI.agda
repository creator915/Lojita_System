module OwnershipIO.MetaFFI where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
open import IO.Primitive using (_>>=_)

infixl 1 _>>_
_>>_ : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
m >> k = m >>= λ _ → k

{-# FOREIGN GHC
import qualified Control.Exception as E
import Control.Monad (forM_, unless, when)
import qualified Data.ByteString as BS
import Data.Char (ord)
import Data.List (isPrefixOf, isSuffixOf)
import qualified Data.Text as T
import qualified Data.Text.Encoding as UTF8
import qualified System.Directory as D
import qualified System.Environment as Env
import System.Exit (ExitCode(ExitSuccess))
import qualified System.FilePath as FP
import qualified System.IO as H
import qualified GHC.IO.Handle.Lock as Lock
import qualified System.Posix.Files as U
import qualified System.Posix.Temp as U
import qualified System.Posix.Time as UTime
import qualified System.Process as Proc
import qualified Agda.Syntax.Parser as P
import qualified Agda.Syntax.Parser.Tokens as K
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Name as N
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Position (mkRangeFile)
import Agda.Utils.FileName (mkAbsolute)
import Agda.Utils.Pretty (prettyShow)
import qualified Data.Foldable as Fold

readBytes :: T.Text -> IO (Maybe BS.ByteString)
readBytes path = E.catch (Just <$> BS.readFile (T.unpack path))
  (\e -> let _ = e :: E.IOException in pure Nothing)

decodeBytes :: BS.ByteString -> Maybe T.Text
decodeBytes = either (const Nothing) Just . UTF8.decodeUtf8'

-- Read the path once. Hash that byte buffer before attempting UTF-8 decoding,
-- so concurrent replacement, invalid sequences and newline handling cannot
-- make the parser see different bytes from the digest.
readVerified :: T.Text -> T.Text -> IO (Maybe T.Text)
readVerified path key = readBytes path >>= maybe (pure Nothing) verify
  where
    verify bytes = Proc.withCreateProcess command $ \(Just input) (Just output) _ process -> do
      BS.hPut input bytes
      H.hClose input
      digest <- BS.take 64 <$> BS.hGetLine output
      status <- Proc.waitForProcess process
      pure $ if status == ExitSuccess && digest == UTF8.encodeUtf8 key
             then decodeBytes bytes else Nothing
    command = (Proc.proc "sha256sum" []) { Proc.std_in = Proc.CreatePipe, Proc.std_out = Proc.CreatePipe }

withPrivate :: T.Text -> (T.Text -> IO a) -> IO a
withPrivate parent action = E.bracket acquire removePrivate (action . T.pack)
  where
    acquire = do
      base <- D.makeAbsolute (T.unpack parent)
      D.createDirectoryIfMissing True base
      U.mkdtemp (base FP.</> "cas-meta-")
    -- Only chmod our own directories. Never follow a link during teardown.
    removePrivate p = do
      st <- U.getSymbolicLinkStatus p
      if U.isDirectory st then do
        U.setFileMode p 0o700
        D.listDirectory p >>= mapM_ (removePrivate . (p FP.</>))
        D.removeDirectory p
      else D.removeFile p

-- Sources and backups live in the caller's unique staging directory on the
-- same filesystem. Unwind every installed projection if the final ref fails.
replaceDuring :: T.Text -> T.Text -> IO a -> IO a
replaceDuring incoming destination action = E.mask $ \restore -> do
  let src = T.unpack incoming
      dst = T.unpack destination
      backup = src ++ ".previous"
  D.createDirectoryIfMissing True (FP.takeDirectory dst)
  exists <- D.doesPathExist dst
  when exists (D.renamePath dst backup)
  let undo = when exists (D.renamePath backup dst)
  D.renamePath src dst `E.onException` undo
  restore action `E.onException` (D.renamePath dst src >> undo)

withTreeLock :: T.Text -> IO a -> IO a
withTreeLock workspace action = do
  let ws = T.unpack workspace
  D.createDirectoryIfMissing True ws
  H.withFile (ws FP.</> ".tree.lock") H.AppendMode $ \h ->
    Lock.hLock h Lock.ExclusiveLock >> action

below :: FilePath -> FilePath -> Bool
below parent path = isPrefixOf (FP.splitDirectories parent) (FP.splitDirectories path)

-- Sources are private copies. Changing their modes or removing the view
-- cannot change a source inode in Context or in a published ancestor.
copySources :: T.Text -> T.Text -> [T.Text] -> IO ()
copySources source dest excluded = do
  src <- D.canonicalizePath (T.unpack source)
  dst <- D.canonicalizePath (T.unpack dest)
  when (below src dst) (ioError (userError "sandbox: include tree contains its own view"))
  copyDir (map T.unpack excluded) (T.unpack source) dst
  where
    copyDir skip src dst = do
      st <- U.getSymbolicLinkStatus src
      unless (U.isDirectory st) (ioError (userError ("sandbox: expected a source directory: " ++ src)))
      D.createDirectory dst
      entries <- D.listDirectory src
      forM_ entries $ \name -> unless (isPrefixOf "." name || elem name skip) $ do
        let from = src FP.</> name
            to = dst FP.</> name
        info <- U.getSymbolicLinkStatus from
        if U.isDirectory info then copyDir [] from to
          else when (U.isRegularFile info && any (sourceFile name skip) P.acceptableFileExts) $ do
            D.copyFile from to
            U.setFileMode to 0o444
      U.setFileMode dst 0o555
    sourceFile name skip ext =
      isSuffixOf ext name && notElem (take (length name - length ext) name) skip

-- Ask Agda's file parser for the actual top-level module and its lexer for
-- every import keyword, including local imports. Neither resolves imports.
-- Comments, string literals, layout and aliases retain Agda's own semantics.
sourceNames :: T.Text -> IO (Maybe [[T.Text]])
sourceNames input = do
  let src = T.unpack input
      path = mkRangeFile (mkAbsolute "/Object.agda") Nothing
  (parsed, _) <- P.runPMIO (P.parseFile P.moduleParser path src)
  (lexed, _) <- P.runPMIO (P.parse P.tokensParser src)
  pure $ do
    ((m, _), _) <- either (const Nothing) Just parsed
    (tokens, _) <- either (const Nothing) Just lexed
    [name] <- pure [q | C.Module _ q _ _ <- C.modDecls m]
    imports <- imported (filter significant tokens)
    pure (map (T.pack . N.nameToRawName) (Fold.toList (N.qnameParts name)) : imports)
  where
    significant (K.TokComment _) = False
    significant _ = True
    imported (K.TokKeyword K.KwImport _ : t : ts) = do
      q <- case t of
        K.TokId (_, n) -> Just [T.pack n]
        K.TokQId ns    -> Just (map (T.pack . snd) ns)
        _              -> Nothing
      (q :) <$> imported ts
    imported (_ : ts) = imported ts
    imported [] = Just []

sourceNamesDiag :: T.Text -> IO T.Text
sourceNamesDiag input = do
  let stripped = T.strip input
      src      = T.unpack input
      srcLines = lines src
      path     = mkRangeFile (mkAbsolute "/Object.agda") Nothing
  if T.null stripped then
    pure (T.pack "source block is empty")
  else if T.isPrefixOf (T.pack "@") stripped then
    pure (T.pack ("source begins with '" ++ T.unpack (T.take 48 stripped)
      ++ "' instead of 'module <Name> where' (write bare @<name> without double quotes in S-expr, or save the block via write_draft first)"))
  else do
    (parsed, _) <- P.runPMIO (P.parseFile P.moduleParser path src)
    (lexed, _)  <- P.runPMIO (P.parse P.tokensParser src)
    case parsed of
      Left err -> pure (T.pack (formatParseErr srcLines (prettyShow err)))
      Right ((m, _), _) -> case lexed of
        Left lerr -> pure (T.pack (formatParseErr srcLines (prettyShow lerr)))
        Right _ ->
          let mods = [q | C.Module _ q _ _ <- C.modDecls m]
              firstLine = case srcLines of { (l : _) -> take 120 l ; [] -> "" }
          in case mods of
               [_] -> pure (T.pack ("malformed 'import' target token in module (first line: " ++ firstLine ++ ")"))
               []  -> pure (T.pack ("missing top-level 'module <Name> where' header (first line: " ++ firstLine ++ ")"))
               _   -> pure (T.pack ("multiple top-level 'module' headers (" ++ show (length mods) ++ " found); exactly one top-level module is allowed"))
  where
    formatParseErr :: [String] -> String -> String
    formatParseErr ls msg =
      let lineHint = case extractLineNo msg of
            Just ln | ln >= 1 && ln <= length ls ->
              "\noffending line " ++ show ln ++ ": " ++ take 200 (ls !! (ln - 1))
            _ -> ""
      in msg ++ lineHint
    extractLineNo :: String -> Maybe Int
    extractLineNo msg =
      let pfx :: String
          pfx = "/Object.agda:"
      in if isPrefixOf pfx msg then
           let rest = drop (length pfx) msg
               digits = takeWhile (\c -> c >= '0' && c <= '9') rest
           in if null digits then Nothing else Just (read digits :: Int)
         else Nothing

escapeJsonStr :: String -> String
escapeJsonStr [] = []
escapeJsonStr ('"'  : cs) = '\\' : '"'  : escapeJsonStr cs
escapeJsonStr ('\\' : cs) = '\\' : '\\' : escapeJsonStr cs
escapeJsonStr ('\n' : cs) = '\\' : 'n'  : escapeJsonStr cs
escapeJsonStr ('\r' : cs) = '\\' : 'r'  : escapeJsonStr cs
escapeJsonStr ('\t' : cs) = '\\' : 't'  : escapeJsonStr cs
escapeJsonStr (c    : cs)
  | ord c < 32 = ' ' : escapeJsonStr cs
  | otherwise  = c   : escapeJsonStr cs

logNarrowingEvent :: T.Text -> T.Text -> T.Text -> T.Text -> IO ()
logNarrowingEvent explicitPath kindT modT detailT =
  E.catch go (\(_ :: E.SomeException) -> pure ())
  where
    go = do
      envP <- Env.lookupEnv "CODETRANSPORT_NARROW_LOG"
      let chosen = if not (T.null explicitPath) then T.unpack explicitPath
                   else maybe "" id envP
      unless (null chosen) $ do
        D.createDirectoryIfMissing True (FP.takeDirectory chosen)
        ts <- UTime.epochTime
        let detailShort = take 600 (T.unpack detailT)
            entry = "{\"ts\":" ++ show ts
                 ++ ",\"source\":\"host\""
                 ++ ",\"kind\":\"" ++ escapeJsonStr (T.unpack kindT) ++ "\""
                 ++ ",\"module\":\"" ++ escapeJsonStr (T.unpack modT) ++ "\""
                 ++ ",\"detail\":\"" ++ escapeJsonStr detailShort ++ "\"}\n"
        H.withFile (chosen ++ ".lock") H.AppendMode $ \lh -> do
          Lock.hLock lh Lock.ExclusiveLock
          BS.appendFile chosen (UTF8.encodeUtf8 (T.pack entry))

-- Precompile Context/{Blueprint,PolyTransport,Terminal}.agda once per content
-- digest outside scratch, then copy the sealed Context view and _build cache
-- into the caller's private temp directory.
populateCachedContext :: T.Text -> T.Text -> IO ()
populateCachedContext repoT tmpT = do
  let repoDir = T.unpack repoT
      tmpDir  = T.unpack tmpT
      ctxFiles = [ "Blueprint.agda"
                 , "PolyTransport.agda"
                 , "Terminal.agda"
                 , "Filter.agda"
                 , "Taboo.agda"
                 , "Tools" FP.</> "FuzzGen.agda"
                 , "Tools" FP.</> "FsSandbox.agda"
                 , "Tools" FP.</> "NetSandbox.agda"
                 , "Tools" FP.</> "GitSandbox.agda" ]
  blobs <- mapM (\f -> BS.readFile (repoDir FP.</> "Context" FP.</> f)) ctxFiles
  digest <- shaBytes (BS.concat [BS.concat [UTF8.encodeUtf8 (T.pack f), BS.singleton 0, b, BS.singleton 0] | (f, b) <- zip ctxFiles blobs])
  sysTmp <- D.getTemporaryDirectory
  let cacheBase = sysTmp FP.</> "codetransport-context-cache-v2"
      entry     = cacheBase FP.</> digest
      ready     = entry FP.</> "ready"
  D.createDirectoryIfMissing True cacheBase
  H.withFile (cacheBase FP.</> ".cache.lock") H.AppendMode $ \lh -> do
    Lock.hLock lh Lock.ExclusiveLock
    ok <- D.doesFileExist ready
    unless ok $ do
      stale <- D.doesPathExist entry
      when stale (removeTreePerm entry)
      E.bracketOnError (U.mkdtemp (cacheBase FP.</> "stage-")) removeTreePerm $ \stage -> do
        BS.writeFile (stage FP.</> "whitelist.agda-lib") (UTF8.encodeUtf8 (T.pack "name: whitelist-cache\n"))
        let sCtx = stage FP.</> "context" FP.</> "Context"
            sTools = sCtx FP.</> "Tools"
            agdaCfg = stage FP.</> ".agda"
        D.createDirectoryIfMissing True sTools
        D.createDirectoryIfMissing True agdaCfg
        forM_ ctxFiles $ \f -> do
          let dst = sCtx FP.</> f
          D.createDirectoryIfMissing True (FP.takeDirectory dst)
          D.copyFileWithMetadata (repoDir FP.</> "Context" FP.</> f) dst
          U.setFileMode dst 0o444
        U.setFileMode sTools 0o555
        U.setFileMode sCtx 0o555
        U.setFileMode (stage FP.</> "context") 0o555
        forM_ ctxFiles $ \f -> do
          let cp = (Proc.proc "/usr/bin/env"
                     [ "AGDA_DIR=" ++ agdaCfg, "agda", "--no-libraries"
                     , "-i", stage FP.</> "context", "-i", "/usr/share/agda-stdlib"
                     , sCtx FP.</> f ]) { Proc.cwd = Just stage }
          (_, _, _) <- Proc.readCreateProcessWithExitCode cp ""
          pure ()
        removeTreePerm agdaCfg
        BS.writeFile ( stage FP.</> "ready" ) BS.empty
        D.renamePath stage entry
    BS.writeFile (tmpDir FP.</> "whitelist.agda-lib") (UTF8.encodeUtf8 (T.pack "name: whitelist-cache\n"))
    copySealed (entry FP.</> "context") (tmpDir FP.</> "context")
    hasBuild <- D.doesDirectoryExist (entry FP.</> "_build")
    when hasBuild (copyWritable (entry FP.</> "_build") (tmpDir FP.</> "_build"))
  where
    shaBytes bytes = Proc.withCreateProcess
      ((Proc.proc "sha256sum" []) { Proc.std_in = Proc.CreatePipe, Proc.std_out = Proc.CreatePipe }) $
      \(Just inp) (Just out) _ ph -> do
        BS.hPut inp bytes
        H.hClose inp
        d <- BS.take 64 <$> BS.hGetLine out
        st <- Proc.waitForProcess ph
        if st == ExitSuccess then pure (T.unpack (UTF8.decodeUtf8 d))
          else ioError (userError "sandbox: sha256sum failed")
    removeTreePerm p = do
      st <- U.getSymbolicLinkStatus p
      if U.isDirectory st then do
        U.setFileMode p 0o700
        D.listDirectory p >>= mapM_ (removeTreePerm . (p FP.</>))
        D.removeDirectory p
      else D.removeFile p
    copySealed src dst = do
      D.createDirectory dst
      entries <- D.listDirectory src
      forM_ entries $ \name -> do
        let from = src FP.</> name
            to   = dst FP.</> name
        st <- U.getSymbolicLinkStatus from
        if U.isDirectory st then copySealed from to else do
          D.copyFileWithMetadata from to
          U.setFileMode to 0o444
      U.setFileMode dst 0o555
    copyWritable src dst = do
      D.createDirectory dst
      U.setFileMode dst 0o700
      entries <- D.listDirectory src
      forM_ entries $ \name -> do
        let from = src FP.</> name
            to   = dst FP.</> name
        st <- U.getSymbolicLinkStatus from
        if U.isDirectory st then copyWritable from to else do
          D.copyFileWithMetadata from to
          U.setFileMode to 0o600
#-}

postulate
  readUTF8 : String → IO (Maybe String)
  readVerifiedUTF8 : String → String → IO (Maybe String)
  writeUTF8 : String → String → IO ⊤
  withPrivateTemp : ∀ {a} {A : Set a} → String → (String → IO A) → IO A
  catchIO : ∀ {a} {A : Set a} → IO A → (String → IO A) → IO A
  replaceDuring : ∀ {a} {A : Set a} → String → String → IO A → IO A
  withTreeLock : ∀ {a} {A : Set a} → String → IO A → IO A
  pathWithin : String → String → IO Bool
  copySourceTree : String → String → List String → IO ⊤
  copyReadOnly : String → String → IO ⊤
  sealDirectory : String → IO ⊤
  inspectSource : String → IO (Maybe (List (List String)))
  inspectSourceDiag : String → IO String
  appendNarrowingEvent : String → String → String → String → IO ⊤
  populateContextCache : String → String → IO ⊤

{-# COMPILE GHC readUTF8 = \p -> fmap (>>= decodeBytes) (readBytes p) #-}
{-# COMPILE GHC readVerifiedUTF8 = readVerified #-}
{-# COMPILE GHC writeUTF8 = \p s -> BS.writeFile (T.unpack p) (UTF8.encodeUtf8 s) #-}
{-# COMPILE GHC withPrivateTemp = \_ _ -> withPrivate #-}
{-# COMPILE GHC catchIO = \_ _ io f -> E.catch io (\e -> f (T.pack (show (e :: E.IOException)))) #-}
{-# COMPILE GHC replaceDuring = \_ _ -> replaceDuring #-}
{-# COMPILE GHC withTreeLock = \_ _ -> withTreeLock #-}
{-# COMPILE GHC pathWithin = \p q -> below <$> D.canonicalizePath (T.unpack p) <*> D.canonicalizePath (T.unpack q) #-}
{-# COMPILE GHC copySourceTree = copySources #-}
{-# COMPILE GHC copyReadOnly = \src dst -> D.copyFile (T.unpack src) (T.unpack dst) >> U.setFileMode (T.unpack dst) 0o444 #-}
{-# COMPILE GHC sealDirectory = \p -> U.setFileMode (T.unpack p) 0o555 #-}
{-# COMPILE GHC inspectSource = sourceNames #-}
{-# COMPILE GHC inspectSourceDiag = sourceNamesDiag #-}
{-# COMPILE GHC appendNarrowingEvent = logNarrowingEvent #-}
{-# COMPILE GHC populateContextCache = populateCachedContext #-}
