-- CodeTransport command line: AST tools, persistent nodes, lifting and session scripts.
{-# OPTIONS --guardedness #-}
module Main where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.String using (String)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as Unit
import IO.Primitive as Prim
import IO.Primitive.Finite as PF
open import IO using (IO; Main; run; putStrLn; _>>=_; _>>_; pure; lift)
open import System.Environment using (getArgs)

open import Code.PureCLI public using
  ( parseCode; renderCode; showObj; showCategory
  ; roundtripText; unitsText; applyTexts; orderText )
open import OwnershipIO.FFI using (enableLineBuffering; currentDirectory)
open import Backend.Switch using (leanPrism; resolveBackendMode; runHarnessEngine)
import Code.CLI as CLI

liftUnit : Prim.IO Unit.⊤ → IO ⊤
liftUnit action = lift action >> pure tt

private
  runEngineCmd : List String → Prim.IO String → IO ⊤
  runEngineCmd args fallback =
    lift (currentDirectory Prim.>>= λ repo →
          resolveBackendMode leanPrism Prim.>>= λ mode →
          runHarnessEngine mode repo args fallback) >>= putStrLn

dispatch : List String → IO ⊤
dispatch ("node" ∷ spec ∷ state ∷ []) = liftUnit (CLI.runTask spec state [] nothing)
dispatch ("lift" ∷ spec ∷ state ∷ base ∷ descriptor ∷ []) = liftUnit (CLI.runLift spec state base descriptor)
dispatch ("script" ∷ file ∷ []) = liftUnit (CLI.runFile file)
dispatch ("session" ∷ workspace ∷ goal ∷ ref ∷ []) = liftUnit (CLI.runSession workspace goal ref)
dispatch ("session-probe" ∷ workspace ∷ ref ∷ script ∷ []) = liftUnit (CLI.runSessionProbe workspace ref script)
dispatch ("roundtrip" ∷ f ∷ []) =
  runEngineCmd ("roundtrip" ∷ f ∷ []) (PF.readFile f Prim.>>= λ txt → Prim.return (roundtripText txt))
dispatch ("units" ∷ f ∷ []) =
  runEngineCmd ("units" ∷ f ∷ []) (PF.readFile f Prim.>>= λ txt → Prim.return (unitsText txt))
dispatch ("apply" ∷ f ∷ g ∷ []) =
  runEngineCmd ("apply" ∷ f ∷ g ∷ [])
    (PF.readFile f Prim.>>= λ old →
     PF.readFile g Prim.>>= λ pl →
     Prim.return (applyTexts old pl))
dispatch ("order" ∷ f ∷ []) =
  runEngineCmd ("order" ∷ f ∷ []) (PF.readFile f Prim.>>= λ txt → Prim.return (orderText txt))
dispatch _ = putStrLn "usage: Main (roundtrip|units|order) File.sexp | apply Code Plan | node Spec.agda State | lift Spec State BaseState Lift.sexp | script Script.agda | session Workspace Goal.txt Ref.sexp"

main : Main
main = run (liftUnit enableLineBuffering >> getArgs >>= dispatch)
