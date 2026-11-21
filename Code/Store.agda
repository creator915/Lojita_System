module Code.Store where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String) renaming (_++_ to _++ˢ_)
open import Data.Unit using (⊤)
import IO.Primitive as IO
import IO.Primitive.Finite as F
open import OwnershipIO.FFI
open import Code
open import Code.Encode using (encodeCanonical)
open import Code.Parse using (parse)

putCode : String → Code → IO.IO String
putCode dir c = sha256 (encodeCanonical c) IO.>>= λ key →
  mkdirP dir IO.>>= λ _ → F.writeFile (dir ++ˢ "/" ++ˢ key ++ˢ ".sexp") (encodeCanonical c) IO.>>= λ _ → IO.return key

getCode : String → String → IO.IO (Maybe Code)
getCode dir key = fileExists (dir ++ˢ "/" ++ˢ key ++ˢ ".sexp") IO.>>= λ where
  false → IO.return nothing
  true → F.readFile (dir ++ˢ "/" ++ˢ key ++ˢ ".sexp") IO.>>= λ txt →
    sha256 txt IO.>>= λ actual → IO.return (if actual ==ˢ key then parse txt else nothing)
