module Backend.PrismFFI where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Backend.Mode using (BackendMode; parseBackendMode)

{-# FOREIGN GHC
import qualified System.Environment as Env
import qualified Data.Text as T

lookupEnvText :: T.Text -> IO (Maybe T.Text)
lookupEnvText k = fmap (fmap T.pack) (Env.lookupEnv (T.unpack k))
#-}

postulate
  lookupEnv : String → IO (Maybe String)
{-# COMPILE GHC lookupEnv = lookupEnvText #-}

-- Resolve active backend mode: if `CODETRANSPORT_BACKEND` is set to a recognized
-- mode (`legacy` | `prism` | `audit`), it overrides the caller's default mode,
-- enabling zero-recompile hot-switching between backends.
resolveBackendMode : BackendMode → IO BackendMode
resolveBackendMode defaultMode =
  IO.Primitive._>>=_ (lookupEnv "CODETRANSPORT_BACKEND") λ where
    nothing  → IO.Primitive.return defaultMode
    (just s) → case parseBackendMode s of λ where
      nothing  → IO.Primitive.return defaultMode
      (just m) → IO.Primitive.return m
  where
    import IO.Primitive
    open import Function.Base using (case_of_)
