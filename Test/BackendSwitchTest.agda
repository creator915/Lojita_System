{-# OPTIONS --guardedness #-}
module Test.BackendSwitchTest where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; not)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; unlines) renaming (_++_ to _++ˢ_)
import Data.Unit as Unit
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import IO.Primitive as Prim
open import IO using (Main; run; lift; pure; _>>_)
import IO.Primitive.Finite as PF

open import OwnershipIO using (onCall)
open import OwnershipIO.FFI using (currentDirectory; mkdirP; removeAll; readProcessAt; ProcResult; procResult; exitFailure; failIO)
open import Code using (Code; _==ˢ_; renameCode)
open import Code.Encode using (encodeCanonical)
open import Code.Protocol using (dumpReq; DumpResult; dumped; dumpFailed; agdaCheck)
open import Code.Transport using (CheckResult; pass; fail; requalify)
open import Backend.Mode
open import Backend.Switch

------------------------------------------------------------------------
-- §1  Compile-Time `refl` Verification of Seamless Routing Contracts
------------------------------------------------------------------------

_ : dispatchPure leanPrism (λ (n : ℕ) → n) (λ _ → 0) 42 (wireBot "coinductive") ≡ 42
_ = bot-falls-back-exact (λ n → n) (λ _ → 0) 42 "coinductive"

_ : dispatchPure legacyAgda (λ (n : ℕ) → n) (λ _ → 0) 99 (wireOK 7) ≡ 99
_ = legacy-mode-exact (λ n → n) (λ _ → 0) 99 (wireOK 7)

_ : parseBackendMode "prism" ≡ just leanPrism
_ = refl

_ : parseBackendMode "legacy" ≡ just legacyAgda
_ = refl

_ : parseBackendMode "audit" ≡ just shadowAudit
_ = refl

_ : acceptsWire true (glueWire 42 true true) ≡ true
_ = lens-cut-sound-and-complete 42 true true true refl

_ : acceptsWire false (glueWire 42 true false) ≡ false
_ = lens-cut-sound-and-complete 42 false true false refl

------------------------------------------------------------------------
-- §2  End-to-End Multi-Mode Switching & Differential Equivalence Suite
------------------------------------------------------------------------

private
  infixl 1 _>>=ᵢ_ _>>ᵢ_
  _>>=ᵢ_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → (A → Prim.IO B) → Prim.IO B
  _>>=ᵢ_ = Prim._>>=_
  _>>ᵢ_ : ∀ {a b} {A : Set a} {B : Set b} → Prim.IO A → Prim.IO B → Prim.IO B
  m >>ᵢ n = m >>=ᵢ λ _ → n

  abortTest : ∀ {A : Set} → String → Prim.IO A
  abortTest msg = PF.putStrLn ("FAIL: " ++ˢ msg) >>ᵢ exitFailure >>ᵢ failIO msg

  assertTrue : String → Bool → Prim.IO Unit.⊤
  assertTrue label true  = PF.putStrLn ("  [OK] " ++ˢ label)
  assertTrue label false = abortTest label

  expectDumped : String → DumpResult → Prim.IO Code
  expectDumped label (dumped c)     = PF.putStrLn ("  [OK] " ++ˢ label) >>ᵢ Prim.return c
  expectDumped label (dumpFailed e) = abortTest (label ++ˢ " -> " ++ˢ e)

  expectDumpFailed : String → DumpResult → Prim.IO Unit.⊤
  expectDumpFailed label (dumpFailed _) = PF.putStrLn ("  [OK] " ++ˢ label ++ˢ " (rejected as expected)")
  expectDumpFailed label (dumped _)     = abortTest (label ++ˢ " -> unexpectedly accepted!")

  expectPass : String → CheckResult → Prim.IO Unit.⊤
  expectPass label pass     = PF.putStrLn ("  [OK] " ++ˢ label)
  expectPass label (fail e) = abortTest (label ++ˢ " -> " ++ˢ e)

  expectFail : String → CheckResult → Prim.IO Unit.⊤
  expectFail label (fail _) = PF.putStrLn ("  [OK] " ++ˢ label ++ˢ " (rejected as expected)")
  expectFail label pass     = abortTest (label ++ˢ " -> unexpectedly passed!")

  depSrc : String
  depSrc = unlines
    ( "{-# OPTIONS --safe #-}"
    ∷ "module Gen.E1.MathDep where"
    ∷ "open import Data.Nat using (ℕ; zero; suc; _+_)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
    ∷ "tri : ℕ → ℕ"
    ∷ "tri zero = zero"
    ∷ "tri (suc n) = suc n + tri n"
    ∷ "_ : tri 5 ≡ 15"
    ∷ "_ = refl"
    ∷ [] )

  candSrc : String
  candSrc = unlines
    ( "{-# OPTIONS --safe #-}"
    ∷ "module Gen.E1.Root where"
    ∷ "open import Data.Nat using (ℕ; _+_)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
    ∷ "open import Gen.E1.MathDep using (tri)"
    ∷ "answer : ℕ"
    ∷ "answer = tri 6"
    ∷ "leftZero : (m : ℕ) → 0 + m ≡ m"
    ∷ "leftZero m = refl"
    ∷ "_ : answer ≡ 21"
    ∷ "_ = refl"
    ∷ [] )

  exeSrc : String
  exeSrc = unlines
    ( "{-# OPTIONS --safe #-}"
    ∷ "module Main where"
    ∷ "open import Data.Nat.Show using (show)"
    ∷ "open import Data.String using () renaming (_++_ to _++ˢ_)"
    ∷ "open import Data.Unit.Polymorphic using (⊤)"
    ∷ "open import IO using (Main; run; putStrLn)"
    ∷ "open import Gen.E1.Root using (answer)"
    ∷ "main : Main"
    ∷ "main = run (putStrLn (\"ans=\" ++ˢ show answer))"
    ∷ [] )

  -- Module-level ⊥ construct (--without-K) -> routes to LegacyAgda seamlessly
  withoutKSrc : String
  withoutKSrc = unlines
    ( "{-# OPTIONS --without-K --safe #-}"
    ∷ "module Gen.E1.WithoutKTail where"
    ∷ "open import Data.Nat using (ℕ)"
    ∷ "idN : ℕ → ℕ"
    ∷ "idN n = n"
    ∷ [] )

  -- Hybrid Optic Lens module: Fast F₁ + Coinductive Stream S + Fast F₂ + Main!
  hybridCoindSrc : String
  hybridCoindSrc = unlines
    ( "{-# OPTIONS --guardedness #-}"
    ∷ "module Gen.E1.HybridEntry where"
    ∷ "open import Data.Nat using (ℕ; zero; suc; _+_; _*_)"
    ∷ "open import Data.Nat.Show using (show)"
    ∷ "open import Data.List using (List; []; _∷_)"
    ∷ "open import Data.String using () renaming (_++_ to _++ˢ_)"
    ∷ "open import Data.Unit.Polymorphic using (⊤)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
    ∷ "open import IO using (Main; run; putStrLn)"
    ∷ "fastWeight : ℕ → ℕ"
    ∷ "fastWeight n = n * 2 + 1"
    ∷ "fastStep : ℕ → ℕ"
    ∷ "fastStep n = n + 3"
    ∷ "sumList : List ℕ → ℕ"
    ∷ "sumList [] = zero"
    ∷ "sumList (x ∷ xs) = x + sumList xs"
    ∷ "_ : sumList (1 ∷ 2 ∷ 3 ∷ []) ≡ 6"
    ∷ "_ = refl"
    ∷ "record Stream : Set where"
    ∷ "  coinductive"
    ∷ "  field"
    ∷ "    hd : ℕ"
    ∷ "    tl : Stream"
    ∷ "open Stream public"
    ∷ "orbitFrom : ℕ → Stream"
    ∷ "hd (orbitFrom n) = fastWeight n"
    ∷ "tl (orbitFrom n) = orbitFrom (fastStep n)"
    ∷ "takeStream : ℕ → Stream → List ℕ"
    ∷ "takeStream zero _ = []"
    ∷ "takeStream (suc k) s = hd s ∷ takeStream k (tl s)"
    ∷ "main : Main"
    ∷ "main = run (putStrLn (\"hybrid=\" ++ˢ show (sumList (takeStream 5 (orbitFrom 1)))))"
    ∷ [] )

  -- Adversarial broken Agda cases:
  badGluedSrc : String
  badGluedSrc = unlines
    ( "module Gen.E1.BadGlued where"
    ∷ "open import Data.Nat using (ℕ)"
    ∷ "open import Data.Product using (_×_; _,_)"
    ∷ "p : ℕ × ℕ"
    ∷ "p = (1, 2)"
    ∷ [] )

  badAutoImpSrc : String
  badAutoImpSrc = unlines
    ( "module Gen.E1.BadTypo where"
    ∷ "typo : Nta → Nta"
    ∷ "typo x = x"
    ∷ [] )

  badProofIrrelSrc : String
  badProofIrrelSrc = unlines
    ( "module Gen.E1.BadIrrel where"
    ∷ "open import Data.Nat using (ℕ)"
    ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
    ∷ "cheat : (x y : ℕ) → (p q : x ≡ y) → p ≡ q"
    ∷ "cheat x y p q = refl"
    ∷ [] )

  badMetaShadowSrc : String
  badMetaShadowSrc = unlines
    ( "module Ownership where"
    ∷ "open import Data.Nat using (ℕ)"
    ∷ "x : ℕ"
    ∷ "x = 0"
    ∷ [] )

  runSuite : Prim.IO Unit.⊤
  runSuite =
    currentDirectory >>=ᵢ λ repo →
    let scratch = repo ++ˢ "/tmp/backend-switch-test"
        dumpBin = repo ++ˢ "/dump/dump"
    in
    removeAll scratch >>ᵢ mkdirP scratch >>ᵢ
    PF.putStrLn "== [1/6] Testing Sweet-Spot Seamless Switching (legacyAgda / leanPrism / shadowAudit) ==" >>ᵢ
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq depSrc [] []) >>=ᵢ expectDumped "leanPrism dump depSrc") >>=ᵢ λ depC →
    (switchDump legacyAgda dumpBin repo scratch [] (dumpReq depSrc [] []) >>=ᵢ expectDumped "legacyAgda dump depSrc") >>=ᵢ λ depCLeg →
    assertTrue "encodeCanonical bit-for-bit match (leanPrism == legacyAgda)" (encodeCanonical depC ==ˢ encodeCanonical depCLeg) >>ᵢ
    (switchDump shadowAudit dumpBin repo scratch [] (dumpReq candSrc [] (depC ∷ [])) >>=ᵢ expectDumped "shadowAudit dump candSrc") >>=ᵢ λ candC →
    (switchCheck legacyAgda repo scratch [] (agdaCheck candC (depC ∷ [])) >>=ᵢ expectPass "legacyAgda check candC") >>ᵢ
    (switchCheck leanPrism repo scratch [] (agdaCheck candC (depC ∷ [])) >>=ᵢ expectPass "leanPrism check candC") >>ᵢ
    (switchCheck shadowAudit repo scratch [] (agdaCheck candC (depC ∷ [])) >>=ᵢ expectPass "shadowAudit check candC") >>ᵢ

    PF.putStrLn "== [2/6] Testing Module-Level ⊥ Seamless Fallback (--without-K) ==" >>ᵢ
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq withoutKSrc [] []) >>=ᵢ expectDumped "leanPrism ⊥-fallback dump withoutKSrc") >>=ᵢ λ wkC →
    (switchCheck leanPrism repo scratch [] (agdaCheck wkC []) >>=ᵢ expectPass "leanPrism ⊥-fallback check withoutKSrc") >>ᵢ
    (switchCheck shadowAudit repo scratch [] (agdaCheck wkC []) >>=ᵢ expectPass "shadowAudit ⊥-fallback check withoutKSrc") >>ᵢ

    PF.putStrLn "== [3/6] Testing v2 Unit-SCC Optic Lens & Unified Thunk C Linker ==" >>ᵢ
    (switchDump shadowAudit dumpBin repo scratch [] (dumpReq hybridCoindSrc [] []) >>=ᵢ expectDumped "shadowAudit dump hybridCoindSrc (canonical Code match!)") >>=ᵢ λ rawHybC →
    (switchCheck shadowAudit repo scratch [] (agdaCheck rawHybC []) >>=ᵢ expectPass "shadowAudit check hybridCoindSrc (Lean FastFocus + Agda SlowSlice)") >>ᵢ
    let mainQ = Code.mkQ ("Main" ∷ [])
        hybMainC = renameCode (requalify (Code.modName rawHybC) mainQ) (record rawHybC { modName = mainQ })
        hybPrismBin = scratch ++ˢ "/hyb-prism"
        hybLegacyBin = scratch ++ˢ "/hyb-legacy"
    in
    (switchCompileExe leanPrism repo scratch hybPrismBin hybMainC [] >>=ᵢ expectPass "leanPrism unified Thunk+partial C build for hybrid coinductive Main") >>ᵢ
    (switchCompileExe legacyAgda repo scratch hybLegacyBin hybMainC [] >>=ᵢ expectPass "legacyAgda MAlonzo build for hybrid coinductive Main") >>ᵢ
    (readProcessAt scratch 30000 hybPrismBin [] "" >>=ᵢ λ { (procResult hpCode hpOut _) →
     readProcessAt scratch 30000 hybLegacyBin [] "" >>=ᵢ λ { (procResult hlCode hlOut _) →
     assertTrue "hybrid Thunk C binary and MAlonzo binary both output 'hybrid=75\\n'"
       ((hpCode ≡ᵇ 0) ∧ (hlCode ≡ᵇ 0) ∧ (hpOut ==ˢ "hybrid=75\n") ∧ (hpOut ==ˢ hlOut)) }}) >>ᵢ

    PF.putStrLn "== [4/6] Testing Adversarial Soundness Gates Across Modes ==" >>ᵢ
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq badGluedSrc [] []) >>=ᵢ expectDumpFailed "leanPrism rejects glued '(1, 2)'") >>ᵢ
    (switchDump shadowAudit dumpBin repo scratch [] (dumpReq badGluedSrc [] []) >>=ᵢ expectDumpFailed "shadowAudit agrees on glued '(1, 2)'") >>ᵢ
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq badAutoImpSrc [] []) >>=ᵢ expectDumpFailed "leanPrism rejects autoImplicit typo 'Nta'") >>ᵢ
    (switchDump shadowAudit dumpBin repo scratch [] (dumpReq badAutoImpSrc [] []) >>=ᵢ expectDumpFailed "shadowAudit agrees on typo 'Nta'") >>ᵢ
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq badMetaShadowSrc [] []) >>=ᵢ expectDumpFailed "leanPrism blocks meta-namespace 'Ownership'") >>ᵢ
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq badProofIrrelSrc [] []) >>=ᵢ expectDumped "dump parses well-scoped badProofIrrelSrc") >>=ᵢ λ badIrrelC →
    (switchCheck leanPrism repo scratch [] (agdaCheck badIrrelC []) >>=ᵢ expectFail "leanPrism kernel rejects Prop proof-irrelevance cheat") >>ᵢ
    (switchCheck shadowAudit repo scratch [] (agdaCheck badIrrelC []) >>=ᵢ expectFail "shadowAudit agrees on proof-irrelevance cheat") >>ᵢ

    PF.putStrLn "== [5/6] Testing Pure Sweet-Spot Multi-Module Executable Build ==" >>ᵢ
    let entrySrc = unlines
          ( "{-# OPTIONS --guardedness #-}"
          ∷ "module Gen.E1.EntryMain where"
          ∷ "open import Data.Nat.Show using (show)"
          ∷ "open import Data.String using () renaming (_++_ to _++ˢ_)"
          ∷ "open import Data.Unit.Polymorphic using (⊤)"
          ∷ "open import IO using (Main; run; putStrLn)"
          ∷ "open import Gen.E1.Root using (answer)"
          ∷ "main : Main"
          ∷ "main = run (putStrLn (\"ans=\" ++ˢ show answer))"
          ∷ [] )
    in
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq entrySrc [] (depC ∷ candC ∷ [])) >>=ᵢ expectDumped "dump entry module") >>=ᵢ λ rawEntryC →
    let mainC = renameCode (requalify (Code.modName rawEntryC) mainQ) (record rawEntryC { modName = mainQ })
        prismBinOut = scratch ++ˢ "/cand-prism"
        legacyBinOut = scratch ++ˢ "/cand-legacy"
    in
    (switchCompileExe leanPrism repo scratch prismBinOut mainC (depC ∷ candC ∷ []) >>=ᵢ expectPass "leanPrism compileExe -> native C binary") >>ᵢ
    (switchCompileExe legacyAgda repo scratch legacyBinOut mainC (depC ∷ candC ∷ []) >>=ᵢ expectPass "legacyAgda compileExe -> MAlonzo binary") >>ᵢ
    (readProcessAt scratch 30000 prismBinOut [] "" >>=ᵢ λ { (procResult pCode pOut _) →
     readProcessAt scratch 30000 legacyBinOut [] "" >>=ᵢ λ { (procResult lCode lOut _) →
     assertTrue "both binaries exit 0 and output identical 'ans=21\\n'"
       ((pCode ≡ᵇ 0) ∧ (lCode ≡ᵇ 0) ∧ (pOut ==ˢ "ans=21\n") ∧ (pOut ==ˢ lOut)) }}) >>ᵢ

    PF.putStrLn "== [6/8] Testing RunningIO Tool Handle Hot-Switch ==" >>ᵢ
    let toolChk = switchAgdaTool leanPrism repo scratch [] in
    (onCall toolChk (agdaCheck candC (depC ∷ [])) >>=ᵢ expectPass "RunningIO switchAgdaTool call pass") >>ᵢ

    PF.putStrLn "== [7/8] Testing Non-Empty Ancestor Directories (Session baseTrees Path) ==" >>ᵢ
    let ancDir = scratch ++ˢ "/anc-view"
        ancModDir = ancDir ++ˢ "/Gen/T0"
        ancSrc = unlines
          ( "{-# OPTIONS --safe #-}"
          ∷ "module Gen.T0.BaseAnc where"
          ∷ "open import Data.Nat using (ℕ; _+_)"
          ∷ "bump : ℕ → ℕ"
          ∷ "bump n = n + 10"
          ∷ [] )
        upperSrc = unlines
          ( "{-# OPTIONS --safe #-}"
          ∷ "module Gen.T1.UpperChild where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
          ∷ "import Gen.T0.BaseAnc as Anc"
          ∷ "val : ℕ"
          ∷ "val = Anc.bump 5"
          ∷ "_ : val ≡ 15"
          ∷ "_ = refl"
          ∷ [] )
    in
    mkdirP ancModDir >>ᵢ
    PF.writeFile (ancModDir ++ˢ "/BaseAnc.agda") ancSrc >>ᵢ
    (switchDump shadowAudit dumpBin repo scratch (ancDir ∷ []) (dumpReq upperSrc [] []) >>=ᵢ expectDumped "shadowAudit dump with non-empty ancestors") >>=ᵢ λ upperC →
    (switchCheck shadowAudit repo scratch (ancDir ∷ []) (agdaCheck upperC []) >>=ᵢ expectPass "shadowAudit check with non-empty ancestors") >>ᵢ

    PF.putStrLn "== [8/8] Testing Native Lean 4 Arbitrary ℕ (39 / 8232) & String Literal Patterns ==" >>ᵢ
    let bigNatSrc = unlines
          ( "{-# OPTIONS --guardedness #-}"
          ∷ "module Gen.E1.BigNatLit where"
          ∷ "open import Data.Nat using (ℕ)"
          ∷ "open import Data.String using (String) renaming (_++_ to _++ˢ_)"
          ∷ "open import Data.Unit.Polymorphic using (⊤)"
          ∷ "open import Relation.Binary.PropositionalEquality using (_≡_; refl)"
          ∷ "open import IO using (Main; run; putStrLn)"
          ∷ "escapeTag : ℕ → String"
          ∷ "escapeTag 39 = \"apos\""
          ∷ "escapeTag 8232 = \"u2028\""
          ∷ "escapeTag _ = \"other\""
          ∷ "kwTag : String → String"
          ∷ "kwTag \"json\" = \"ok\""
          ∷ "kwTag _ = \"no\""
          ∷ "_ : escapeTag 8232 ≡ \"u2028\""
          ∷ "_ = refl"
          ∷ "_ : kwTag \"json\" ≡ \"ok\""
          ∷ "_ = refl"
          ∷ "main : Main"
          ∷ "main = run (putStrLn (escapeTag 39 ++ˢ \":\" ++ˢ escapeTag 8232 ++ˢ \":\" ++ˢ kwTag \"json\"))"
          ∷ [] )
    in
    (switchDump leanPrism dumpBin repo scratch [] (dumpReq bigNatSrc [] []) >>=ᵢ expectDumped "leanPrism dump 39 / 8232 / String patterns") >>=ᵢ λ rawBigC →
    (switchCheck leanPrism repo scratch [] (agdaCheck rawBigC []) >>=ᵢ expectPass "leanPrism FastFocus check 39 / 8232 / String patterns (fixes old Agda suc-chain bug)") >>ᵢ
    let bigMainC = renameCode (requalify (Code.modName rawBigC) mainQ) (record rawBigC { modName = mainQ })
        bigBin = scratch ++ˢ "/big-nat-prism"
    in
    (switchCompileExe leanPrism repo scratch bigBin bigMainC [] >>=ᵢ expectPass "leanPrism native C build with 39 / 8232 / String patterns") >>ᵢ
    (readProcessAt scratch 30000 bigBin [] "" >>=ᵢ λ { (procResult bCode bOut _) →
     assertTrue "native binary outputs 'apos:u2028:ok\\n'" ((bCode ≡ᵇ 0) ∧ (bOut ==ˢ "apos:u2028:ok\n")) }) >>ᵢ

    removeAll scratch >>ᵢ
    PF.putStrLn "== ALL BACKEND SWITCH TESTS PASSED =="

main : Main
main = run (lift runSuite >> pure tt)
