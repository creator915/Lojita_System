{-# OPTIONS --guardedness #-}
module Code.Tools.AllTools where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.String using (String)
open import Ownership using (Spec; ≡-inst)
open import Code.Driver using (Registry; Pick; SubT; select; all-nil; all-cons)
open import Code.Tools.FsTool using (fsSpec; fsTool)
open import Code.Tools.NetTool using (netSpec; netTool)
open import Code.Tools.GitTool using (gitSpec; gitTool)
open import Code.TermTool using (ptySpec; ptyTool)

record ExtRelayPaths : Set where
  constructor extRelayPaths
  field
    fsRelay netRelay gitRelay termRelay : String
open ExtRelayPaths public

ExtToolsΨ : List Spec
ExtToolsΨ = fsSpec ∷ netSpec ∷ gitSpec ∷ []

FullExtΨ : List Spec
FullExtΨ = ptySpec ∷ ExtToolsΨ

-- Transports allocate distinct private sessions beneath the shared scratch root.
extToolsRegistry : ExtRelayPaths → String → Registry ExtToolsΨ
extToolsRegistry paths scratch =
  fsTool (fsRelay paths) scratch ∷
  netTool (netRelay paths) scratch ∷
  gitTool (gitRelay paths) scratch ∷ []

fullExtRegistry : ExtRelayPaths → String → Registry FullExtΨ
fullExtRegistry paths scratch = ptyTool (termRelay paths) scratch
  ∷ extToolsRegistry paths scratch

-- The omitted {{sub}} arguments are solved by all-nil, all-cons and ≡-inst.
-- Reordering exercises name lookup rather than positional registry projection.
selectFsNet : Registry FullExtΨ → Registry (fsSpec ∷ netSpec ∷ [])
selectFsNet reg = select (fsSpec ∷ netSpec ∷ []) reg

selectGitFs : Registry FullExtΨ → Registry (gitSpec ∷ fsSpec ∷ [])
selectGitFs reg = select (gitSpec ∷ fsSpec ∷ []) reg

selectAllExt : Registry FullExtΨ → Registry ExtToolsΨ
selectAllExt reg = select ExtToolsΨ reg

selectFullExt : Registry FullExtΨ → Registry FullExtΨ
selectFullExt reg = select FullExtΨ reg

selectTermGit : Registry FullExtΨ → Registry (ptySpec ∷ gitSpec ∷ [])
selectTermGit reg = select (ptySpec ∷ gitSpec ∷ []) reg

selectExtGitFs : Registry ExtToolsΨ → Registry (gitSpec ∷ fsSpec ∷ [])
selectExtGitFs reg = select (gitSpec ∷ fsSpec ∷ []) reg

-- Explicit compile-time witnesses use exactly the same instance search.
private
  resolve : ∀ {a} {A : Set a} {{proof : A}} → A
  resolve {{proof}} = proof

pickFs : Pick fsSpec FullExtΨ
pickFs = resolve

pickNet : Pick netSpec FullExtΨ
pickNet = resolve

pickGit : Pick gitSpec FullExtΨ
pickGit = resolve

pickTerm : Pick ptySpec FullExtΨ
pickTerm = resolve

subAllExt : SubT ExtToolsΨ FullExtΨ
subAllExt = resolve

subFullExt : SubT FullExtΨ FullExtΨ
subFullExt = resolve
