{-# OPTIONS --guardedness #-}
------------------------------------------------------------------------
-- OwnershipIO/WorldRunner.agda —— Single Audited Thin IO Interpreter (`PandocIO`)
--
-- The sole host-IO execution boundary for verified `Context.World` target
-- programs (`CliApp Δ` and `ReactiveApp Δ S`):
--   * Every closed-world `WorldProg Δ A` is a finite, `--safe` inductive tree
--     interpreted without unbounded loops by `runWorldIO` / `runCliIO`.
--   * Long-running interactive / daemon programs (`ReactiveApp Δ S`) place
--     their single outer `while` event loop exclusively in `runReactiveIO`.
--   * All domain logic, argv[0] symlink dispatch, TTY ANSI coloring, file/net
--     error codes, and timeouts live inside verified `--safe` `WorldProg`
--     specifications and implementations rather than hand-written IO glue.
------------------------------------------------------------------------
module OwnershipIO.WorldRunner where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≡ᵇ_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Fin.Base using () renaming (toℕ to octet)
open import Data.List.Base using (map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import IO.Primitive using (return; _>>=_)

open import Context.Terminal using
  ( Byte; Bytes; byte; Signal; sigINT; sigTERM; sigHUP; sigQUIT )
open import Context.Tools.FsSandbox using
  ( FsNodeKind; regularNode; dirNode; symlinkNode )
open import Context.Tools.GitSandbox using
  ( PureGitRepo; stepPureGit; projectSummary )
open import Context.Tools.WebOperad using
  ( compileDraw; hitTest )
open import Context.World using
  ( Cap; clockCap; envCap; ttyCap; fsCap; netCap; gitCap; webCap
  ; _∈_; findCap∈
  ; FsError; fsNotFound; fsIsDirectory; fsNotDirectory; fsAlreadyExists
  ; fsPermissionDenied; fsSymlinkLoop; fsInvalidPath; fsIoError
  ; NetError; netConnRefused; netTimedOut; netInvalidEndpoint; netTlsError; netIoError
  ; CanvasDOM; domViewport; domEvents; emptyCanvasDOM; defaultGitRepo; popWebEvent
  ; Op; opNowMono; opNowWall; opSleepMs
  ; opGetProgName; opGetArgs; opLookupEnv; opReadStdinAll; opReadStdinLine
  ; opIsTTYStdin; opIsTTYStdout; opIsTTYStderr; opTermSize
  ; opWriteStdout; opWriteStderr; opReadTTYByte
  ; opReadFile; opWriteFile; opMkdir; opSymlink; opUnlink; opStat
  ; opTcpExchange; opTlsExchange
  ; opGitStep; opGitSummary
  ; opWebViewport; opWebSetTitle; opWebDrawScene; opWebHitTest; opWebPollInput
  ; Ret; WorldProg; pure; step
  ; ExitCode; CliApp; EventPayload; evTickMs; evSignal; evResize; evTTYBytes
  ; Event; mkEvent; ReactiveApp; init; onStep )

{-# FOREIGN GHC {-# LANGUAGE ForeignFunctionInterface #-} #-}
{-# FOREIGN GHC
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Word (Word8, Word32, Word64)
import Foreign.C.String (CString, peekCString)
import Foreign.C.Types (CChar, CInt(..), CSize(..), CUInt(..), CULong(..))
import Foreign.Marshal.Alloc (alloca)
import Foreign.Marshal.Array (peekArray, withArrayLen)
import Foreign.Ptr (Ptr, nullPtr, castPtr)
import Foreign.Storable (peek)
import GHC.IO.Encoding (setLocaleEncoding, utf8)
import qualified System.Environment as Env
import qualified System.IO as H

foreign import ccall unsafe "ct_now_mono_ms"         c_wr_now_mono_ms  :: IO Word64
foreign import ccall unsafe "ct_now_wall_ms"         c_wr_now_wall_ms  :: IO Word64
foreign import ccall safe   "ct_sleep_ms"            c_wr_sleep_ms     :: CUInt -> IO ()
foreign import ccall unsafe "ct_get_prog_name"       c_wr_prog_name    :: IO CString
foreign import ccall unsafe "ct_get_argc"            c_wr_argc         :: IO CInt
foreign import ccall unsafe "ct_get_arg"             c_wr_arg          :: CInt -> IO CString
foreign import ccall unsafe "ct_lookup_env_n"        c_wr_lookup_env   :: Ptr CChar -> CSize -> IO CString
foreign import ccall safe   "ct_read_stdin_all"      c_wr_stdin_all    :: Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign import ccall safe   "ct_read_stdin_line"     c_wr_stdin_line   :: Ptr CInt -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign import ccall unsafe "ct_is_tty"              c_wr_is_tty       :: CInt -> IO CInt
foreign import ccall unsafe "ct_term_size"           c_wr_term_size    :: Ptr CUInt -> Ptr CUInt -> IO ()
foreign import ccall safe   "ct_write_fd_all"        c_wr_write_fd     :: CInt -> Ptr Word8 -> CSize -> IO CInt
foreign import ccall safe   "ct_read_tty_byte"       c_wr_read_tty_b   :: Ptr CInt -> Ptr Word8 -> IO CInt
foreign import ccall safe   "ct_poll_reactive_event" c_wr_poll_react   :: CUInt -> Ptr CUInt -> Ptr CUInt -> IO CInt
foreign import ccall safe   "ct_fs_read_file"        c_wr_fs_read      :: Ptr CChar -> CSize -> Ptr (Ptr Word8) -> Ptr CSize -> IO CInt
foreign import ccall safe   "ct_fs_write_file"       c_wr_fs_write     :: Ptr CChar -> CSize -> Ptr Word8 -> CSize -> IO CInt
foreign import ccall safe   "ct_fs_mkdir"            c_wr_fs_mkdir     :: Ptr CChar -> CSize -> CUInt -> IO CInt
foreign import ccall safe   "ct_fs_symlink"          c_wr_fs_symlink   :: Ptr CChar -> CSize -> Ptr CChar -> CSize -> IO CInt
foreign import ccall safe   "ct_fs_unlink"           c_wr_fs_unlink    :: Ptr CChar -> CSize -> IO CInt
foreign import ccall safe   "ct_fs_stat"             c_wr_fs_stat      :: Ptr CChar -> CSize -> Ptr CInt -> IO CInt
foreign import ccall safe   "ct_tcp_exchange_code"   c_wr_tcp_code     ::
  Ptr CChar -> CSize -> CUInt -> Ptr Word8 -> CSize -> CInt -> CUInt ->
  Ptr (Ptr Word8) -> Ptr CSize -> Ptr CInt -> IO CInt
foreign import ccall safe   "ct_tls_exchange_code"   c_wr_tls_code     ::
  Ptr CChar -> CSize -> CUInt -> Ptr CChar -> CSize -> CInt ->
  Ptr Word8 -> CSize -> Ptr Word8 -> CSize -> CUInt ->
  Ptr (Ptr Word8) -> Ptr CSize -> Ptr CInt -> IO CInt
foreign import ccall unsafe "ct_free_buf"            c_wr_free_buf     :: Ptr Word8 -> IO ()
foreign import ccall unsafe "ct_exit_code"           c_wr_exit_code    :: CUInt -> IO ()

data WREither a b = WRLeft a | WRRight b
data WRPair a b = WRPair a b

withTextBytes :: T.Text -> (Ptr CChar -> CSize -> IO a) -> IO a
withTextBytes txt k =
  let bs = TE.encodeUtf8 txt in
  BSU.unsafeUseAsCStringLen bs $ \(ptr, len) -> k ptr (fromIntegral len)

wrLockUTF8 :: IO ()
wrLockUTF8 = do
  setLocaleEncoding utf8
  H.hSetEncoding H.stdout utf8
  H.hSetEncoding H.stderr utf8

wrNowMono :: IO Integer
wrNowMono = fmap fromIntegral c_wr_now_mono_ms

wrNowWall :: IO Integer
wrNowWall = fmap fromIntegral c_wr_now_wall_ms

wrSleepMs :: Integer -> IO ()
wrSleepMs ms = c_wr_sleep_ms (fromIntegral (min 3600000 (max 0 ms)))

wrGetProgName :: IO T.Text
wrGetProgName = do
  p <- c_wr_prog_name
  if p == nullPtr then fmap T.pack Env.getProgName else fmap T.pack (peekCString p)

wrGetArgs :: IO [T.Text]
wrGetArgs = do
  n <- c_wr_argc
  if n <= 0 then fmap (map T.pack) Env.getArgs
  else mapM (\i -> c_wr_arg i >>= fmap T.pack . peekCString) [0 .. n - 1]

wrLookupEnv :: T.Text -> IO (Maybe T.Text)
wrLookupEnv k = withTextBytes k $ \ptr len -> do
  v <- c_wr_lookup_env ptr len
  if v == nullPtr then pure Nothing else fmap (Just . T.pack) (peekCString v)

wrReadStdinAll :: IO [Integer]
wrReadStdinAll =
  alloca $ \bufPtr ->
  alloca $ \lenPtr -> do
    _ <- c_wr_stdin_all bufPtr lenPtr
    buf <- peek bufPtr
    len <- peek lenPtr
    octs <- if len == 0 || buf == nullPtr then pure [] else peekArray (fromIntegral len) buf
    if buf /= nullPtr then c_wr_free_buf buf else pure ()
    pure (map fromIntegral octs)

wrReadStdinLine :: IO (Maybe [Integer])
wrReadStdinLine =
  alloca $ \gotPtr ->
  alloca $ \bufPtr ->
  alloca $ \lenPtr -> do
    _ <- c_wr_stdin_line gotPtr bufPtr lenPtr
    got <- peek gotPtr
    buf <- peek bufPtr
    len <- peek lenPtr
    if got == 0 then do
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      pure Nothing
    else do
      octs <- if len == 0 || buf == nullPtr then pure [] else peekArray (fromIntegral len) buf
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      pure (Just (map fromIntegral octs))

wrIsTTY :: Integer -> IO Bool
wrIsTTY fd = fmap (/= 0) (c_wr_is_tty (fromIntegral fd))

wrTermSize :: IO (WRPair Integer Integer)
wrTermSize =
  alloca $ \rPtr ->
  alloca $ \cPtr -> do
    c_wr_term_size rPtr cPtr
    r <- peek rPtr
    c <- peek cPtr
    pure (WRPair (fromIntegral r) (fromIntegral c))

wrWriteFd :: Integer -> [Integer] -> IO ()
wrWriteFd fd octs =
  withArrayLen (map fromIntegral octs :: [Word8]) $ \len ptr -> do
    _ <- c_wr_write_fd (fromIntegral fd) ptr (fromIntegral len)
    pure ()

wrReadTTYByte :: IO (Maybe Integer)
wrReadTTYByte =
  alloca $ \gotPtr ->
  alloca $ \bPtr -> do
    _ <- c_wr_read_tty_b gotPtr bPtr
    got <- peek gotPtr
    if got == 0 then pure Nothing
    else fmap (Just . fromIntegral) (peek bPtr)

wrPollReactive :: Integer -> IO (WRPair Integer (WRPair Integer Integer))
wrPollReactive waitMs =
  alloca $ \aPtr ->
  alloca $ \bPtr -> do
    k <- c_wr_poll_react (fromIntegral (min 60000 (max 0 waitMs))) aPtr bPtr
    a <- peek aPtr
    b <- peek bPtr
    pure (WRPair (fromIntegral k) (WRPair (fromIntegral a) (fromIntegral b)))

wrFsRead :: T.Text -> IO (WREither Integer [Integer])
wrFsRead p =
  withTextBytes p $ \pPtr pLen ->
  alloca $ \bufPtr ->
  alloca $ \lenPtr -> do
    rc <- c_wr_fs_read pPtr pLen bufPtr lenPtr
    buf <- peek bufPtr
    len <- peek lenPtr
    if rc /= 0 then do
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      pure (WRLeft (fromIntegral rc))
    else do
      octs <- if len == 0 || buf == nullPtr then pure [] else peekArray (fromIntegral len) buf
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      pure (WRRight (map fromIntegral octs))

wrFsWrite :: T.Text -> [Integer] -> IO (WREither Integer ())
wrFsWrite p octs =
  withTextBytes p $ \pPtr pLen ->
  withArrayLen (map fromIntegral octs :: [Word8]) $ \bLen bPtr -> do
    rc <- c_wr_fs_write pPtr pLen bPtr (fromIntegral bLen)
    pure (if rc == 0 then WRRight () else WRLeft (fromIntegral rc))

wrFsMkdir :: T.Text -> Integer -> IO (WREither Integer ())
wrFsMkdir p mode =
  withTextBytes p $ \pPtr pLen -> do
    rc <- c_wr_fs_mkdir pPtr pLen (fromIntegral mode)
    pure (if rc == 0 then WRRight () else WRLeft (fromIntegral rc))

wrFsSymlink :: T.Text -> T.Text -> IO (WREither Integer ())
wrFsSymlink p dst =
  withTextBytes p $ \pPtr pLen ->
  withTextBytes dst $ \dPtr dLen -> do
    rc <- c_wr_fs_symlink pPtr pLen dPtr dLen
    pure (if rc == 0 then WRRight () else WRLeft (fromIntegral rc))

wrFsUnlink :: T.Text -> IO (WREither Integer ())
wrFsUnlink p =
  withTextBytes p $ \pPtr pLen -> do
    rc <- c_wr_fs_unlink pPtr pLen
    pure (if rc == 0 then WRRight () else WRLeft (fromIntegral rc))

wrFsStat :: T.Text -> IO (WREither Integer Integer)
wrFsStat p =
  withTextBytes p $ \pPtr pLen ->
  alloca $ \kPtr -> do
    rc <- c_wr_fs_stat pPtr pLen kPtr
    if rc /= 0 then pure (WRLeft (fromIntegral rc))
    else fmap (WRRight . fromIntegral) (peek kPtr)

wrTcpExchange :: T.Text -> Integer -> [Integer] -> Bool -> Integer -> IO (WREither Integer [Integer])
wrTcpExchange host port reqOcts halfClose timeoutMs =
  withTextBytes host $ \hPtr hLen ->
  withArrayLen (map fromIntegral reqOcts :: [Word8]) $ \reqLen reqPtr ->
  alloca $ \outBufPtr ->
  alloca $ \outLenPtr ->
  alloca $ \errCodePtr -> do
    rc <- c_wr_tcp_code
            hPtr hLen
            (fromIntegral (port `mod` 65536))
            reqPtr (fromIntegral reqLen)
            (if halfClose then 1 else 0)
            (fromIntegral (min 3600000 (max 0 timeoutMs)))
            outBufPtr outLenPtr errCodePtr
    buf <- peek outBufPtr
    len <- peek outLenPtr
    if rc /= 0 then do
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      ec <- peek errCodePtr
      pure (WRLeft (fromIntegral ec))
    else do
      octs <- if len == 0 || buf == nullPtr then pure [] else peekArray (fromIntegral len) buf
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      pure (WRRight (map fromIntegral octs))

wrTlsExchange :: T.Text -> Integer -> T.Text -> Bool -> [Integer] -> [Integer] -> Integer -> IO (WREither Integer [Integer])
wrTlsExchange host port sni insecure tunOcts reqOcts timeoutMs =
  withTextBytes host $ \hPtr hLen ->
  withTextBytes sni $ \sPtr sLen ->
  withArrayLen (map fromIntegral tunOcts :: [Word8]) $ \tunLen tunPtr ->
  withArrayLen (map fromIntegral reqOcts :: [Word8]) $ \reqLen reqPtr ->
  alloca $ \outBufPtr ->
  alloca $ \outLenPtr ->
  alloca $ \errCodePtr -> do
    rc <- c_wr_tls_code
            hPtr hLen
            (fromIntegral (port `mod` 65536))
            sPtr sLen
            (if insecure then 1 else 0)
            tunPtr (fromIntegral tunLen)
            reqPtr (fromIntegral reqLen)
            (fromIntegral (min 3600000 (max 0 timeoutMs)))
            outBufPtr outLenPtr errCodePtr
    buf <- peek outBufPtr
    len <- peek outLenPtr
    if rc /= 0 then do
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      ec <- peek errCodePtr
      pure (WRLeft (fromIntegral ec))
    else do
      octs <- if len == 0 || buf == nullPtr then pure [] else peekArray (fromIntegral len) buf
      if buf /= nullPtr then c_wr_free_buf buf else pure ()
      pure (WRRight (map fromIntegral octs))

wrExitCode :: Integer -> IO ()
wrExitCode c = c_wr_exit_code (fromIntegral (c `mod` 256))
#-}

private
  data WREither (A B : Set) : Set where
    wrLeft  : A → WREither A B
    wrRight : B → WREither A B
  {-# COMPILE GHC WREither = data WREither (WRLeft | WRRight) #-}

  data WRPair (A B : Set) : Set where
    wrPair : A → B → WRPair A B
  {-# COMPILE GHC WRPair = data WRPair (WRPair) #-}

  postulate
    primLockUTF8    : IO ⊤
    primNowMono     : IO Nat
    primNowWall     : IO Nat
    primSleepMs     : Nat → IO ⊤
    primGetProgName : IO String
    primGetArgs     : IO (List String)
    primLookupEnv   : String → IO (Maybe String)
    primStdinAll    : IO (List Nat)
    primStdinLine   : IO (Maybe (List Nat))
    primIsTTY       : Nat → IO Bool
    primTermSize    : IO (WRPair Nat Nat)
    primWriteFd     : Nat → List Nat → IO ⊤
    primReadTTYByte : IO (Maybe Nat)
    primPollReact   : Nat → IO (WRPair Nat (WRPair Nat Nat))
    primFsRead      : String → IO (WREither Nat (List Nat))
    primFsWrite     : String → List Nat → IO (WREither Nat ⊤)
    primFsMkdir     : String → Nat → IO (WREither Nat ⊤)
    primFsSymlink   : String → String → IO (WREither Nat ⊤)
    primFsUnlink    : String → IO (WREither Nat ⊤)
    primFsStat      : String → IO (WREither Nat Nat)
    primTcpCode     : String → Nat → List Nat → Bool → Nat → IO (WREither Nat (List Nat))
    primTlsCode     : String → Nat → String → Bool → List Nat → List Nat → Nat → IO (WREither Nat (List Nat))
    primExitCode    : Nat → IO ⊤

  {-# COMPILE GHC primLockUTF8    = wrLockUTF8 #-}
  {-# COMPILE GHC primNowMono     = wrNowMono #-}
  {-# COMPILE GHC primNowWall     = wrNowWall #-}
  {-# COMPILE GHC primSleepMs     = wrSleepMs #-}
  {-# COMPILE GHC primGetProgName = wrGetProgName #-}
  {-# COMPILE GHC primGetArgs     = wrGetArgs #-}
  {-# COMPILE GHC primLookupEnv   = wrLookupEnv #-}
  {-# COMPILE GHC primStdinAll    = wrReadStdinAll #-}
  {-# COMPILE GHC primStdinLine   = wrReadStdinLine #-}
  {-# COMPILE GHC primIsTTY       = wrIsTTY #-}
  {-# COMPILE GHC primTermSize    = wrTermSize #-}
  {-# COMPILE GHC primWriteFd     = wrWriteFd #-}
  {-# COMPILE GHC primReadTTYByte = wrReadTTYByte #-}
  {-# COMPILE GHC primPollReact   = wrPollReactive #-}
  {-# COMPILE GHC primFsRead      = wrFsRead #-}
  {-# COMPILE GHC primFsWrite     = wrFsWrite #-}
  {-# COMPILE GHC primFsMkdir     = wrFsMkdir #-}
  {-# COMPILE GHC primFsSymlink   = wrFsSymlink #-}
  {-# COMPILE GHC primFsUnlink    = wrFsUnlink #-}
  {-# COMPILE GHC primFsStat      = wrFsStat #-}
  {-# COMPILE GHC primTcpCode     = wrTcpExchange #-}
  {-# COMPILE GHC primTlsCode     = wrTlsExchange #-}
  {-# COMPILE GHC primExitCode    = wrExitCode #-}

  decodeFsError : Nat → FsError
  decodeFsError 1 = fsNotFound
  decodeFsError 2 = fsIsDirectory
  decodeFsError 3 = fsNotDirectory
  decodeFsError 4 = fsAlreadyExists
  decodeFsError 5 = fsPermissionDenied
  decodeFsError 6 = fsSymlinkLoop
  decodeFsError 7 = fsInvalidPath
  decodeFsError _ = fsIoError

  decodeNodeKind : Nat → FsNodeKind
  decodeNodeKind 0 = regularNode
  decodeNodeKind 1 = dirNode
  decodeNodeKind _ = symlinkNode

  decodeNetError : Nat → NetError
  decodeNetError 1 = netConnRefused
  decodeNetError 2 = netTimedOut
  decodeNetError 3 = netInvalidEndpoint
  decodeNetError 4 = netTlsError
  decodeNetError _ = netIoError

  decodeSignal : Nat → Signal
  decodeSignal 1 = sigINT
  decodeSignal 2 = sigTERM
  decodeSignal 3 = sigHUP
  decodeSignal _ = sigQUIT

  execOpIO : ∀ {c} → (op : Op c) → PureGitRepo → CanvasDOM → IO (Ret op × PureGitRepo × CanvasDOM)
  -- Clock
  execOpIO opNowMono g w =
    primNowMono >>= λ t → return (t , g , w)
  execOpIO opNowWall g w =
    primNowWall >>= λ t → return (t , g , w)
  execOpIO (opSleepMs ms) g w =
    primSleepMs ms >>= λ _ → return (tt , g , w)
  -- Process Env
  execOpIO opGetProgName g w =
    primGetProgName >>= λ p → return (p , g , w)
  execOpIO opGetArgs g w =
    primGetArgs >>= λ as → return (as , g , w)
  execOpIO (opLookupEnv k) g w =
    primLookupEnv k >>= λ mv → return (mv , g , w)
  execOpIO opReadStdinAll g w =
    primStdinAll >>= λ ns → return (map byte ns , g , w)
  execOpIO opReadStdinLine g w =
    primStdinLine >>= λ where
      nothing   → return (nothing , g , w)
      (just ns) → return (just (map byte ns) , g , w)
  -- Terminal / Stdio
  execOpIO opIsTTYStdin g w =
    primIsTTY 0 >>= λ b → return (b , g , w)
  execOpIO opIsTTYStdout g w =
    primIsTTY 1 >>= λ b → return (b , g , w)
  execOpIO opIsTTYStderr g w =
    primIsTTY 2 >>= λ b → return (b , g , w)
  execOpIO opTermSize g w =
    primTermSize >>= λ { (wrPair r c) → return ((r , c) , g , w) }
  execOpIO (opWriteStdout bs) g w =
    primWriteFd 1 (map octet bs) >>= λ _ → return (tt , g , w)
  execOpIO (opWriteStderr bs) g w =
    primWriteFd 2 (map octet bs) >>= λ _ → return (tt , g , w)
  execOpIO opReadTTYByte g w =
    primReadTTYByte >>= λ where
      nothing  → return (nothing , g , w)
      (just b) → return (just (byte b) , g , w)
  -- Filesystem
  execOpIO (opReadFile p) g w =
    primFsRead p >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeFsError ec) , g , w)
      (wrRight ns) → return (inj₂ (map byte ns) , g , w)
  execOpIO (opWriteFile p bs) g w =
    primFsWrite p (map octet bs) >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeFsError ec) , g , w)
      (wrRight _)  → return (inj₂ tt , g , w)
  execOpIO (opMkdir p mode) g w =
    primFsMkdir p mode >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeFsError ec) , g , w)
      (wrRight _)  → return (inj₂ tt , g , w)
  execOpIO (opSymlink p dst) g w =
    primFsSymlink p dst >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeFsError ec) , g , w)
      (wrRight _)  → return (inj₂ tt , g , w)
  execOpIO (opUnlink p) g w =
    primFsUnlink p >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeFsError ec) , g , w)
      (wrRight _)  → return (inj₂ tt , g , w)
  execOpIO (opStat p) g w =
    primFsStat p >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeFsError ec) , g , w)
      (wrRight kd) → return (inj₂ (decodeNodeKind kd) , g , w)
  -- Network
  execOpIO (opTcpExchange host port req hc tms) g w =
    primTcpCode host port (map octet req) hc tms >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeNetError ec) , g , w)
      (wrRight ns) → return (inj₂ (map byte ns) , g , w)
  execOpIO (opTlsExchange host port sni ins tun req tms) g w =
    primTlsCode host port sni ins (map octet tun) (map octet req) tms >>= λ where
      (wrLeft ec)  → return (inj₁ (decodeNetError ec) , g , w)
      (wrRight ns) → return (inj₂ (map byte ns) , g , w)
  -- Git
  execOpIO (opGitStep gs) g w =
    let r = stepPureGit gs g
    in return (proj₂ r , proj₁ r , w)
  execOpIO opGitSummary g w =
    return (projectSummary g , g , w)
  -- Web Canvas / DOM
  execOpIO opWebViewport g w =
    return (domViewport w , g , w)
  execOpIO (opWebSetTitle title) g w =
    return (tt , g , record w { domTitle = title })
  execOpIO (opWebDrawScene sc) g w =
    return (tt , g , record w { domCommands = compileDraw sc })
  execOpIO (opWebHitTest sc q) g w =
    return (hitTest sc q , g , w)
  execOpIO opWebPollInput g w =
    let r = popWebEvent (domEvents w)
    in return (proj₁ r , g , record w { domEvents = proj₂ r })

  runWorldState : ∀ {Δ A} → PureGitRepo → CanvasDOM → WorldProg Δ A → IO (A × PureGitRepo × CanvasDOM)
  runWorldState g w (pure a)      = return (a , g , w)
  runWorldState g w (step _ op k) =
    execOpIO op g w >>= λ { (ret , g′ , w′) →
    runWorldState g′ w′ (k ret) }

  hasLiveEventSource : List Cap → Bool
  hasLiveEventSource Δ with findCap∈ clockCap Δ | findCap∈ envCap Δ | findCap∈ ttyCap Δ
  ... | just _  | _       | _       = true
  ... | nothing | just _  | _       = true
  ... | nothing | nothing | just _  = true
  ... | nothing | nothing | nothing = false

  decodePolledEvent : (Δ : List Cap) → Nat → Nat → Nat → Maybe (Event Δ)
  decodePolledEvent Δ kind a b with kind ≡ᵇ 2
  ... | true with findCap∈ envCap Δ
  ...   | just hEnv = just (mkEvent hEnv (evSignal (decodeSignal a)))
  ...   | nothing   = nothing
  decodePolledEvent Δ kind a b | false with kind ≡ᵇ 3
  ... | true with findCap∈ ttyCap Δ
  ...   | just hTty = just (mkEvent hTty (evResize a b))
  ...   | nothing   = nothing
  decodePolledEvent Δ kind a b | false | false with kind ≡ᵇ 4
  ... | true with findCap∈ ttyCap Δ
  ...   | just hTty = just (mkEvent hTty (evTTYBytes (byte a ∷ [])))
  ...   | nothing   = nothing
  decodePolledEvent Δ kind a b | false | false | false with findCap∈ clockCap Δ
  ... | just hClk = just (mkEvent hClk (evTickMs a))
  ... | nothing   = nothing

  -- The ONLY unbounded loop in the target-program execution stack:
  {-# NON_TERMINATING #-}
  reactiveLoop : ∀ {Δ S} → ReactiveApp Δ S → PureGitRepo → CanvasDOM → S → IO ⊤
  reactiveLoop {Δ} app g w s =
    ifBool (hasLiveEventSource Δ)
      (primPollReact 25 >>= λ { (wrPair kind (wrPair a b)) →
       dispatch (decodePolledEvent Δ kind a b) })
      (primExitCode 0)
    where
      ifBool : ∀ {A : Set} → Bool → A → A → A
      ifBool true  t _ = t
      ifBool false _ f = f

      dispatch : Maybe (Event Δ) → IO ⊤
      dispatch nothing   = reactiveLoop app g w s
      dispatch (just ev) =
        runWorldState g w (onStep app ev s) >>= λ where
          (inj₁ s′   , g′ , w′) → reactiveLoop app g′ w′ s′
          (inj₂ code , _  , _ ) → primExitCode code

runWorldIO : ∀ {Δ A} → WorldProg Δ A → IO A
runWorldIO prog =
  primLockUTF8 >>= λ _ →
  runWorldState defaultGitRepo emptyCanvasDOM prog >>= λ { (a , _ , _) →
  return a }

runCliIO : ∀ {Δ} → CliApp Δ → IO ⊤
runCliIO app =
  runWorldIO app >>= primExitCode

runReactiveIO : ∀ {Δ S} → ReactiveApp Δ S → IO ⊤
runReactiveIO app =
  primLockUTF8 >>= λ _ →
  runWorldState defaultGitRepo emptyCanvasDOM (init app) >>= λ { (s₀ , g₀ , w₀) →
  reactiveLoop app g₀ w₀ s₀ }
