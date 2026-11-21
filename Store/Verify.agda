{-# OPTIONS --guardedness #-}
module Store.Verify where

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; is-just)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import IO.Primitive using (IO; return; _>>=_)
open import Code.Codecs using (HomeValue)
open import Store.CAS

verifyCommitDAG : String → Hash → IO Bool
verifyCommitDAG dir tip = do
  readHome ← newCommitHomeReader dir
  readCommit ← newDAGReader dir commitK (verify readHome)
  result ← readCommit tip
  return (is-just result)
  where
  allParents : Reader ⊤ → List Hash → IO (Maybe ⊤)
  allParents read [] = return (just tt)
  allParents read (h ∷ hs) = read h >>=? λ _ → allParents read hs

  verify : (CommitObj → IO (Maybe HomeValue)) → Reader ⊤ → Reader ⊤
  verify readHome readParent h = getCommit dir h >>=? λ c →
    readHome c >>=? λ _ → allParents readParent (parents c)
