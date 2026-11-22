#!/usr/bin/env python3
"""End-to-end verification of the categorical interface-cut countermodel submission gate."""
import json
from pathlib import Path
import select
import subprocess
import sys
import time

repo, scratch = map(Path, sys.argv[1:])
build = repo / "runtime/lean-prism/.lake/build"
prism = build / "bin/agda2lean"
engine = build / "bin/harness-engine"
dump_bin = repo / "dump/dump"


def run(args, expected=True, *, stdin=None, cwd=None, timeout=240):
    p = subprocess.run(list(map(str, args)), input=stdin, text=True, capture_output=True, timeout=timeout, cwd=cwd)
    if (p.returncode == 0) != expected:
        raise AssertionError(
            f"cmd={args}\nexit={p.returncode} (expected_ok={expected})\nSTDOUT:\n{p.stdout[-2000:]}\nSTDERR:\n{p.stderr[-3000:]}"
        )
    return p.stdout if expected else (p.stdout + "\n" + p.stderr)


# 0. Compile Test/CountermodelGateTest.agda driver
driver_build = scratch / "driver-build"
driver_build.mkdir(parents=True, exist_ok=True)
print("Compiling Test/CountermodelGateTest.agda ...", flush=True)
run([
    "agda", "--no-libraries", "--compile", "--ghc-flag=-O0",
    f"--ghc-flag=-i{repo}/runtime", f"--ghc-flag=-i{repo}/runtime/tools",
    f"--ghc-flag={repo}/runtime/cli_host.c", f"--compile-dir={driver_build}",
    "-i", ".", "-i", "/usr/share/agda-stdlib", "Test/CountermodelGateTest.agda",
], cwd=repo, timeout=600)
gate_bin = driver_build / "CountermodelGateTest"
assert "COUNTERMODEL_SELF_OK" in run([gate_bin, "self"], cwd=repo)

# 1. Verify prompts/Countermodel.agda FastFocus (0 SlowSlice) and canonical parity
cm_src_dir = scratch / "cm_lib"
cm_src_dir.mkdir(parents=True, exist_ok=True)
cm_file = cm_src_dir / "Countermodel.agda"
cm_rendered = run([engine, "countermodel-lib"], cwd=repo)
cm_file.write_text(cm_rendered)
run(["agda", "--safe", "--no-libraries", "-i", cm_src_dir, "-i", "/usr/share/agda-stdlib", cm_file], cwd=cm_src_dir)
slice_info = run([
    prism, "inspect-slice", "--lib-dir", build / "lib/lean",
    "--work-dir", scratch / "slice", "--dump-bin", dump_bin, "--main", cm_file,
])
assert "SLOW_UNITS (0):" in slice_info, slice_info
print("PASS Countermodel library passes Agda --safe and Lean Prism FastFocus (0 SlowSlice)")


def write_case(name, spec_src, model_src, refute_src, bases=()):
    d = scratch / "cases" / name
    d.mkdir(parents=True, exist_ok=True)
    sf = d / "spec.agda"
    mf = d / "model.agda"
    rf = d / "refute.agda"
    sf.write_text(spec_src)
    mf.write_text(model_src)
    rf.write_text(refute_src)
    bfs = []
    for i, b in enumerate(bases):
        bf = d / f"base_{i}.agda"
        bf.write_text(b)
        bfs.append(bf)
    return d, sf, mf, rf, bfs


def check_gate(name, spec_src, model_src, refute_src, expected=True, *, expect_err=None, modes=("prism",), bases=()):
    if not expected and not expect_err:
        raise ValueError(f"{name}: negative test must specify expect_err")
    d, sf, mf, rf, bfs = write_case(name, spec_src, model_src, refute_src, bases)
    out = ""
    for mode in modes:
        out = run([gate_bin, "check", mode, "pass" if expected else "fail", repo, d / f"work_{mode}", sf, mf, rf, *bfs], cwd=repo)
        if not expected and expect_err not in out:
            raise AssertionError(f"{name} ({mode}): expected {expect_err!r} in:\n{out}")
    return out


# 2. Extract prompt example (DashSpec + DashModel + DashRefute) directly from prompts/node-closed-world.md
prompt_txt = (repo / "prompts/node-closed-world.md").read_text()
dash_spec = "module DashSpec where" + prompt_txt.split("module DashSpec where", 1)[1].split("\n```", 1)[0] + "\n"
dash_model = prompt_txt.split("```agda dashModel\n", 1)[1].split("\n```", 1)[0] + "\n"
dash_refute = prompt_txt.split("```agda dashRefute\n", 1)[1].split("\n```", 1)[0] + "\n"

check_gate("DashAllModes", dash_spec, dash_model, dash_refute, expected=True, modes=("prism", "legacy", "audit"))
print("PASS DashSpec countermodel verified across prism, legacy, and audit modes (zero SHADOW_AUDIT_VIOLATION)")

# 3. Roundtrip via swapStringModel
roundtrip_spec = """module Gen.T2.Roundtrip where
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.String using (String; primStringToList; primStringFromList)

starts : List Char → Bool
starts [] = false
starts (c ∷ _) = primCharToNat c == 97

startsA : String → Bool
startsA s = starts (primStringToList s)

postulate
  law : (s : String) → startsA s ≡ true → primStringFromList (primStringToList s) ≡ s
"""

roundtrip_model = """{-# OPTIONS --safe #-}
module RoundtripModel where
open import Countermodel using
  ( StringAlg; CountermodelBundle; stringCountermodel
  ; swapStringModel; fromListSwapped; modelHead; within; false≢true )
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Data.List.Base using (replicate)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)

starts : List Char → Bool
starts [] = false
starts (c ∷ _) = primCharToNat c == 97

Claim : StringAlg → Set
Claim S = (s : StringAlg.Str S) → starts (StringAlg.toList S s) ≡ true →
          StringAlg.fromList S (StringAlg.toList S s) ≡ s

over : (k : Nat) → within k ('a' ∷ replicate k 'a') ≡ false
over zero = refl
over (suc k) = over k

swapped : (k : Nat) → starts (fromListSwapped 'a' 'b' k ('a' ∷ replicate k 'a')) ≡ false
swapped k = cong (λ b → primCharToNat (modelHead 'a' 'b' b 'a') == 97) (over k)

bundle : CountermodelBundle
bundle = stringCountermodel Claim (swapStringModel 'a' 'b') (λ k h →
  false≢true (trans (sym (swapped k)) (cong starts (h ('a' ∷ replicate k 'a') refl))))
"""

roundtrip_refute = """module RoundtripRefute where
import Gen.T2.Roundtrip as Spec
import RoundtripModel as M
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (primStringToList)
open import Relation.Binary.PropositionalEquality.Core using (trans)

sameStarts : (xs : List Char) → Spec.starts xs ≡ M.starts xs
sameStarts [] = refl
sameStarts (_ ∷ _) = refl

witness : VerifiedClaim
witness = verifiedClaim (λ s p → Spec.law s (trans (sameStarts (primStringToList s)) p))
"""
check_gate("Roundtrip", roundtrip_spec, roundtrip_model, roundtrip_refute, expected=True, modes=("prism", "audit"))
print("PASS String roundtrip countermodel verified")

# 4. Infinite even-codepoint Char reflexivity subdomain via custom SoundCharModel
# (Infinitely many odd codepoints remain unconstrained, so global taboo-primCharRefl is impossible!)
even_char_spec = """module Gen.T2.EvenChar where
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primCharToNat; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

isEven : Nat → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

postulate
  evenCharRefl : (c : Char) → isEven (primCharToNat c) ≡ true → primCharEquality c c ≡ true
"""

even_char_model = """{-# OPTIONS --safe #-}
module EvenCharModel where
open import Countermodel using
  ( CharAlg; SoundCharModel; soundCharModel; CountermodelBundle; charCountermodel
  ; phantomCharModel; withinNat; false≢true )
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (primCharToNat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (inj₂)
open import Data.Unit.Base using (tt)

isEven : Nat → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

double : Nat → Nat
double zero = zero
double (suc n) = suc (suc (double n))

evenDouble : (k : Nat) → isEven (double k) ≡ true
evenDouble zero = refl
evenDouble (suc k) = evenDouble k

stepWithinNat : (x m : Nat) → withinNat x m ≡ true → withinNat x (suc m) ≡ true
stepWithinNat zero _ _ = refl
stepWithinNat (suc _) zero p = ⊥-elim (false≢true p)
stepWithinNat (suc x) (suc m) p = stepWithinNat x m p

widenOdd : (x k : Nat) → withinNat x k ≡ true → withinNat x (suc (double k)) ≡ true
widenOdd zero _ _ = refl
widenOdd (suc _) zero p = ⊥-elim (false≢true p)
widenOdd (suc x) (suc k) p = stepWithinNat x (suc (double k)) (widenOdd x k p)

-- Evaluating phantomCharModel at odd stage (2k + 1) places the phantom codepoint at 2(k + 1), which is even!
evenPhantomModel : SoundCharModel
evenPhantomModel = soundCharModel
  (λ k → SoundCharModel.atCharStage phantomCharModel (suc (double k)))
  (λ k → SoundCharModel.embedChar phantomCharModel (suc (double k)))
  (λ k c p → SoundCharModel.charToNatWithin phantomCharModel (suc (double k)) c (widenOdd (primCharToNat c) k p))
  (λ k n → SoundCharModel.natToCharLaw phantomCharModel (suc (double k)) n)
  (λ k c d → SoundCharModel.charEqLaw phantomCharModel (suc (double k)) c d)

Claim : CharAlg → Set
Claim C = (c : CharAlg.Chr C) → isEven (CharAlg.charToNat C c) ≡ true →
          CharAlg.charEq C c c ≡ true

bundle : CountermodelBundle
bundle = charCountermodel Claim evenPhantomModel (λ k h →
  false≢true (h (inj₂ tt) (evenDouble k)))
"""

even_char_refute = """module EvenCharRefute where
import Gen.T2.EvenChar as Spec
import EvenCharModel as M
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Char using (primCharToNat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality.Core using (trans)

sameEven : (n : Nat) → Spec.isEven n ≡ M.isEven n
sameEven zero = refl
sameEven (suc zero) = refl
sameEven (suc (suc n)) = sameEven n

witness : VerifiedClaim
witness = verifiedClaim (λ c p → Spec.evenCharRefl c (trans (sameEven (primCharToNat c)) p))
"""
check_gate("EvenCharSubdomain", even_char_spec, even_char_model, even_char_refute, expected=True, modes=("prism", "audit"))
print("PASS Infinite even-codepoint Char subdomain (irreducible to SafeTaboo) refuted via custom SoundCharModel")

# 5. Custom 2nd-character perturbing SoundStringModel built from scratch
# (Refutes a law fixing head '!' and observing index 1 — impossible in old v8-s2's head-only Perturb!)
second_char_spec = """module Gen.T2.SecondChar where
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (_==_)
open import Agda.Builtin.String using (primStringToList; primStringFromList)

secondIsX : List Char → Bool
secondIsX (_ ∷ c ∷ _) = primCharToNat c == 120
secondIsX _ = false

postulate
  law : (cs : List Char) → secondIsX (primStringToList (primStringFromList ('!' ∷ 'x' ∷ cs))) ≡ true
"""

second_char_model = """{-# OPTIONS --safe #-}
module SecondCharModel where
open import Countermodel using
  ( StringAlg; stringAlg; SoundStringModel; soundStringModel
  ; CountermodelBundle; stringCountermodel
  ; swapStringModel; fromListSwapped; within; eqChars; false≢true )
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (_++_; replicate)
open import Relation.Binary.PropositionalEquality.Core using (cong; sym; trans)

-- Perturb the tail (starting at index 1!) while always keeping index 0 intact:
fromListTail : Nat → List Char → List Char
fromListTail _ [] = []
fromListTail k (c ∷ cs) = c ∷ fromListSwapped 'x' 'y' k cs

headOf : Char → List Char → Char
headOf d [] = d
headOf _ (x ∷ _) = x

tailOf : List Char → List Char
tailOf [] = []
tailOf (_ ∷ ts) = ts

tailInj : (k : Nat) (xs ys : List Char) → fromListTail k xs ≡ fromListTail k ys → xs ≡ ys
tailInj _ [] [] _ = refl
tailInj _ [] (_ ∷ _) ()
tailInj _ (_ ∷ _) [] ()
tailInj k (a ∷ xs) (b ∷ ys) p =
  trans (cong (λ h → h ∷ xs) (cong (headOf a) p))
        (cong (λ t → b ∷ t) (StringAlg.fromListInjective (SoundStringModel.atStage (swapStringModel 'x' 'y') k) xs ys (cong tailOf p)))

widenTail : (k : Nat) (c : Char) (cs : List Char) → within k (c ∷ cs) ≡ true → within k cs ≡ true
widenTail zero _ _ p = ⊥-elim (false≢true p)
widenTail (suc _) _ [] _ = refl
widenTail (suc k) c (d ∷ cs) p = widenTail k d cs p

toFromTail : (k : Nat) (xs : List Char) → within k xs ≡ true → fromListTail k xs ≡ xs
toFromTail _ [] _ = refl
toFromTail k (c ∷ cs) p =
  cong (λ t → c ∷ t) (SoundStringModel.toFromWithin (swapStringModel 'x' 'y') k cs (widenTail k c cs p))

cong₂ : {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ f {x₁} {x₂} {y₁} {y₂} px py = trans (cong (λ u → f u y₁) px) (cong (f x₂) py)

customTailModel : SoundStringModel
customTailModel = soundStringModel
  (λ k → stringAlg (List Char) (λ s → s) (fromListTail k) _++_ eqChars (λ _ _ p → p) (tailInj k))
  toFromTail
  (λ k xs ys px py pxy → trans (cong₂ _++_ (toFromTail k xs px) (toFromTail k ys py)) (sym (toFromTail k (xs ++ ys) pxy)))
  (λ k xs ys px py → cong₂ eqChars (toFromTail k xs px) (toFromTail k ys py))

secondIsX : List Char → Bool
secondIsX (_ ∷ c ∷ _) = primCharToNat c == 120
secondIsX _ = false

over : (k : Nat) → within k ('x' ∷ replicate k 'x') ≡ false
over zero = refl
over (suc k) = over k

swapped2 : (k : Nat) → secondIsX (fromListTail k ('!' ∷ 'x' ∷ replicate k 'x')) ≡ false
swapped2 k = cong (λ b → primCharToNat (Countermodel.modelHead 'x' 'y' b 'x') == 120) (over k)

Claim : StringAlg → Set
Claim S = (cs : List Char) → secondIsX (StringAlg.toList S (StringAlg.fromList S ('!' ∷ 'x' ∷ cs))) ≡ true

bundle : CountermodelBundle
bundle = stringCountermodel Claim customTailModel (λ k h →
  false≢true (trans (sym (swapped2 k)) (h (replicate k 'x'))))
"""

second_char_refute = """module SecondCharRefute where
import Gen.T2.SecondChar as Spec
import SecondCharModel as M
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (primStringToList; primStringFromList)
open import Relation.Binary.PropositionalEquality.Core using (trans)

sameSecond : (xs : List Char) → M.secondIsX xs ≡ Spec.secondIsX xs
sameSecond [] = refl
sameSecond (_ ∷ []) = refl
sameSecond (_ ∷ _ ∷ _) = refl

witness : VerifiedClaim
witness = verifiedClaim (λ cs → trans (sameSecond (primStringToList (primStringFromList ('!' ∷ 'x' ∷ cs)))) (Spec.law cs))
"""
check_gate("CustomSecondCharModel", second_char_spec, second_char_model, second_char_refute, expected=True, modes=("prism", "audit"))
print("PASS Custom node-authored tail-perturbing SoundStringModel verified from scratch")

# 6. Real gron-v7 Gen.T4.Gron.Reader.Prefix + multi-layer Gen.T4.Gron (with SamePart referencing postulate partText!)
prefix_spec = """module Gen.T4.Gron.Reader.Prefix where

open import Data.Char using (Char; fromℕ)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Context.Terminal using (byte)
open import Context.World using (decodeUtf8)

Text : Set
Text = List Char

data JsonSpace : Char → Set where
  space : JsonSpace (fromℕ 32)
  tab : JsonSpace (fromℕ 9)
  lineFeed : JsonSpace (fromℕ 10)
  carriageReturn : JsonSpace (fromℕ 13)

data Start : Set where
  end : Start
  mark : Start
  content : Char → Text → Start

postulate
  atStart : Text → Start
  startEmpty : atStart [] ≡ end
  startSpace : (c : _) → (rest : _) → JsonSpace c → atStart (c ∷ rest) ≡ atStart rest
  startContent : (c : _) → (rest : _) → (JsonSpace c → ⊥) → (c ≢ fromℕ 65279) → atStart (c ∷ rest) ≡ content c rest
  startMark : (rest : _) → atStart (fromℕ 65279 ∷ rest) ≡ mark
  startFromBytes : (tail : _) → (s : _) → decodeUtf8 (byte 239 ∷ byte 187 ∷ byte 191 ∷ tail) ≡ just s → atStart (toList s) ≡ atStart (fromℕ 65279 ∷ [])
"""

prefix_model = """{-# OPTIONS --safe #-}
module PrefixModel where
open import Countermodel using
  ( StringAlg; CountermodelBundle; stringCountermodel
  ; swapStringModel; fromListSwapped; modelHead; within )
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Char using (Char; primNatToChar)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (replicate)
open import Relation.Binary.PropositionalEquality.Core using (cong)

bom : Char
bom = primNatToChar 65279

Claim : StringAlg → Set
Claim S = (n : Nat) →
  StringAlg.toList S (StringAlg.fromList S (bom ∷ replicate n 'a')) ≡ ('a' ∷ replicate n 'a') → ⊥

overA : (k : Nat) → within k ('a' ∷ replicate k 'a') ≡ false
overA zero = refl
overA (suc k) = overA k

over : (k : Nat) → within k (bom ∷ replicate k 'a') ≡ false
over zero = refl
over (suc k) = overA k

swapped : (k : Nat) → fromListSwapped bom 'a' k (bom ∷ replicate k 'a') ≡ ('a' ∷ replicate k 'a')
swapped k = cong (λ b → modelHead bom 'a' b bom ∷ replicate k 'a') (over k)

bundle : CountermodelBundle
bundle = stringCountermodel Claim (swapStringModel bom 'a') (λ k h → h k (swapped k))
"""

prefix_refute = """module PrefixRefute where
import Gen.T4.Gron.Reader.Prefix as Spec
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char; primNatToChar; primCharToNat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _==_)
open import Agda.Builtin.String using (primStringFromList)
open import Data.Empty using (⊥)
open import Data.Fin.Base using () renaming (toℕ to octet)
open import Data.List.Base using (List; []; _∷_; map; replicate)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst; sym; trans)
open import Context.Terminal using (Bytes; byte)
open import Context.World using (decodeUtf8Chars)

bom : Char
bom = primNatToChar 65279

ascii : Nat → Bytes
ascii n = replicate n (byte 97)

asciiStep : (ns : List Nat) (cs : List Char) → decodeUtf8Chars ns ≡ just cs →
            decodeUtf8Chars (97 ∷ ns) ≡ just ('a' ∷ cs)
asciiStep ns cs p rewrite p = refl

asciiDecoded : (n : Nat) → decodeUtf8Chars (map octet (ascii n)) ≡ just (replicate n 'a')
asciiDecoded zero = refl
asciiDecoded (suc n) = asciiStep (map octet (ascii n)) (replicate n 'a') (asciiDecoded n)

bomStep : (ns : List Nat) (cs : List Char) → decodeUtf8Chars ns ≡ just cs →
          decodeUtf8Chars (239 ∷ 187 ∷ 191 ∷ ns) ≡ just (bom ∷ cs)
bomStep ns cs p rewrite p = refl

decoded : (n : Nat) → decodeUtf8Chars (map octet (byte 239 ∷ byte 187 ∷ byte 191 ∷ ascii n)) ≡ just (bom ∷ replicate n 'a')
decoded n = bomStep (map octet (ascii n)) (replicate n 'a') (asciiDecoded n)

boxed : (n : Nat) → Context.World.decodeUtf8 (byte 239 ∷ byte 187 ∷ byte 191 ∷ ascii n) ≡
        just (primStringFromList (bom ∷ replicate n 'a'))
boxed n rewrite decoded n = refl

atFalse : Bool → Set
atFalse false = ⊤
atFalse true = ⊥

isA : Char → Bool
isA c = primCharToNat c == 97

spaceNotA : (c : Char) → Spec.JsonSpace c → isA c ≡ false
spaceNotA _ Spec.space = refl
spaceNotA _ Spec.tab = refl
spaceNotA _ Spec.lineFeed = refl
spaceNotA _ Spec.carriageReturn = refl

notSpace : Spec.JsonSpace 'a' → ⊥
notSpace p = subst atFalse (sym (spaceNotA 'a' p)) tt

notBom : 'a' ≡ bom → ⊥
notBom p = subst atFalse (sym (cong isA p)) tt

isMark : Spec.Start → Bool
isMark Spec.end = false
isMark Spec.mark = true
isMark (Spec.content _ _) = false

witness : VerifiedClaim
witness = verifiedClaim (λ n eq →
  let cs = replicate n 'a'
      asContent = trans (cong Spec.atStart eq) (Spec.startContent 'a' cs notSpace notBom)
      asMark = trans (Spec.startFromBytes (ascii n) (primStringFromList (bom ∷ cs)) (boxed n))
                     (Spec.startMark [])
  in subst atFalse (cong isMark (trans (sym asContent) asMark)) tt)
"""
check_gate("GronPrefix", prefix_spec, prefix_model, prefix_refute, expected=True, modes=("prism", "audit"))
print("PASS Real gron-v7 Gen.T4.Gron.Reader.Prefix verified across prism and audit (prism + legacy) modes")

# Repaired character-level Prefix is constructively provable in --safe Agda AND rejects the countermodel!
repaired_prefix_spec = prefix_spec.replace(
    "open import Context.World using (decodeUtf8)",
    "open import Data.Fin.Base using () renaming (toℕ to octet)\nopen import Data.List.Base using (map)\nopen import Context.World using (decodeUtf8Chars)",
).replace(
    "decodeUtf8 (byte 239 ∷ byte 187 ∷ byte 191 ∷ tail) ≡ just s → atStart (toList s)",
    "decodeUtf8Chars (map octet (byte 239 ∷ byte 187 ∷ byte 191 ∷ tail)) ≡ just s → atStart s",
)
repaired_false_refute = prefix_refute.replace(
    """boxed : (n : Nat) → Context.World.decodeUtf8 (byte 239 ∷ byte 187 ∷ byte 191 ∷ ascii n) ≡
        just (primStringFromList (bom ∷ replicate n 'a'))
boxed n rewrite decoded n = refl\n\n""",
    "",
).replace("primStringFromList (bom ∷ cs)", "(bom ∷ cs)").replace("boxed n", "decoded n")
check_gate(
    "RepairedPrefixRejectsFalseCountermodel",
    repaired_prefix_spec,
    prefix_model,
    repaired_false_refute,
    expected=False,
    expect_err="@refute independenceCheck failed:\nLEAN_TYPE_ERROR",
)
print("PASS Repaired decodeUtf8Chars Prefix rejects false countermodel witness at kernel typecheck")

# 7. Multi-layer Gen.T0.Gron + Gen.T2.Gron + Gen.T4.Gron (with SamePart referencing postulate partText!)
t0_base = """module Gen.T0.Gron where
open import Data.Maybe using (Maybe; just; nothing)
data DocumentMode : Set where
  singleDocument documentStream : DocumentMode
data JsonKind : Set where
  arrayKind objectKind : JsonKind
rootKind : DocumentMode → Maybe JsonKind → Maybe JsonKind
rootKind singleDocument k = k
rootKind documentStream _ = just arrayKind
"""

t2_base = """module Gen.T2.Gron where
open import Data.Nat using (ℕ)
data Format : Set where
  jsAssignments valuesOnly : Format
record Reply : Set where
  constructor reply
  field
    status : ℕ
"""

t4_spec = """module Gen.T4.Gron where
open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to decimal)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Context.Terminal using (Bytes; byte)
open import Context.World using (decodeUtf8)
import Gen.T0.Gron as Base
import Gen.T2.Gron as CLI

Text : Set
Text = List Char

data Component : Set where
  property : Text → Component
  index : ℕ → Component

postulate
  partText : Bool → Component → Text
  indexLaw : ∀ n → partText false (index n) ≡ toList (decimal n)

-- Inductive family referencing a prior postulate (caused arity-lifting complexity in old v8-s2):
data SamePart : Component → Component → Set where
  sameIndex : ∀ n → SamePart (index n) (index n)
  sameProperty : ∀ {k l} → partText false (property k) ≡ partText false (property l) →
                 SamePart (property k) (property l)

postulate
  runBytes : Base.DocumentMode → CLI.Format → Bytes → CLI.Reply
  runText : Base.DocumentMode → CLI.Format → Text → CLI.Reply
  byteForward : ∀ m f raw s → decodeUtf8 raw ≡ just s → runBytes m f raw ≡ runText m f (toList s)
  emptyArrayOK : ∀ f rest → CLI.Reply.status (runText Base.singleDocument f ('[' ∷ ']' ∷ rest)) ≡ 0
  initialBOMErr : ∀ f tail → CLI.Reply.status (runBytes Base.singleDocument f (byte 239 ∷ byte 187 ∷ byte 191 ∷ tail)) ≡ 3
"""

t4_model = """{-# OPTIONS --safe #-}
module T4BomModel where
open import Countermodel using
  ( StringAlg; CountermodelBundle; stringCountermodel
  ; swapStringModel; fromListSwapped; modelHead; within )
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Char using (Char; primNatToChar)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (replicate)
open import Relation.Binary.PropositionalEquality.Core using (cong)

bom : Char
bom = primNatToChar 65279

chars : Nat → List Char
chars n = ']' ∷ replicate n ' '

Claim : StringAlg → Set
Claim S = (n : Nat) →
  StringAlg.toList S (StringAlg.fromList S (bom ∷ chars n)) ≡ ('[' ∷ chars n) → ⊥

overSpace : (k : Nat) → within k (' ' ∷ ' ' ∷ replicate k ' ') ≡ false
overSpace zero = refl
overSpace (suc k) = overSpace k

over : (k : Nat) → within k (bom ∷ chars k) ≡ false
over zero = refl
over (suc zero) = refl
over (suc (suc k)) = overSpace k

swapped : (k : Nat) → fromListSwapped bom '[' k (bom ∷ chars k) ≡ ('[' ∷ chars k)
swapped k = cong (λ b → modelHead bom '[' b bom ∷ chars k) (over k)

bundle : CountermodelBundle
bundle = stringCountermodel Claim (swapStringModel bom '[') (λ k h → h k (swapped k))
"""

t4_refute = """module T4BomRefute where
import Gen.T4.Gron as Spec
import Gen.T0.Gron as Base
import Gen.T2.Gron as CLI
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Char using (Char; primNatToChar)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (primStringFromList)
open import Data.Empty using (⊥)
open import Data.Fin.Base using () renaming (toℕ to octet)
open import Data.List.Base using (List; []; _∷_; map; replicate)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (cong; subst; sym; trans)
open import Context.Terminal using (Bytes; byte)
open import Context.World using (decodeUtf8Chars)

bom : Char
bom = primNatToChar 65279

rawTail : Nat → Bytes
rawTail n = byte 93 ∷ replicate n (byte 32)

spaceStep : (ns : List Nat) (cs : List Char) → decodeUtf8Chars ns ≡ just cs →
            decodeUtf8Chars (32 ∷ ns) ≡ just (' ' ∷ cs)
spaceStep ns cs p rewrite p = refl

spaces : (n : Nat) → decodeUtf8Chars (map octet (replicate n (byte 32))) ≡ just (replicate n ' ')
spaces zero = refl
spaces (suc n) = spaceStep (map octet (replicate n (byte 32))) (replicate n ' ') (spaces n)

closeStep : (ns : List Nat) (cs : List Char) → decodeUtf8Chars ns ≡ just cs →
            decodeUtf8Chars (93 ∷ ns) ≡ just (']' ∷ cs)
closeStep ns cs p rewrite p = refl

bomStep : (ns : List Nat) (cs : List Char) → decodeUtf8Chars ns ≡ just cs →
          decodeUtf8Chars (239 ∷ 187 ∷ 191 ∷ ns) ≡ just (bom ∷ cs)
bomStep ns cs p rewrite p = refl

decoded : (n : Nat) → decodeUtf8Chars (map octet (byte 239 ∷ byte 187 ∷ byte 191 ∷ rawTail n))
          ≡ just (bom ∷ ']' ∷ replicate n ' ')
decoded n = bomStep (map octet (rawTail n)) (']' ∷ replicate n ' ')
              (closeStep (map octet (replicate n (byte 32))) (replicate n ' ') (spaces n))

boxed : (n : Nat) → Context.World.decodeUtf8 (byte 239 ∷ byte 187 ∷ byte 191 ∷ rawTail n)
        ≡ just (primStringFromList (bom ∷ ']' ∷ replicate n ' '))
boxed n rewrite decoded n = refl

positive : Nat → Set
positive zero = ⊥
positive (suc _) = ⊤

three≢zero : 3 ≡ 0 → ⊥
three≢zero p = subst positive p tt

witness : VerifiedClaim
witness = verifiedClaim (λ n eq →
  let raw = byte 239 ∷ byte 187 ∷ byte 191 ∷ rawTail n
      s = primStringFromList (bom ∷ ']' ∷ replicate n ' ')
      byBytes = cong CLI.Reply.status (Spec.byteForward Base.singleDocument CLI.jsAssignments raw s (boxed n))
      byText = trans (cong (λ xs → CLI.Reply.status (Spec.runText Base.singleDocument CLI.jsAssignments xs)) eq)
                     (Spec.emptyArrayOK CLI.jsAssignments (replicate n ' '))
      is3 = Spec.initialBOMErr CLI.jsAssignments (rawTail n)
  in three≢zero (trans (sym is3) (trans byBytes byText)))
"""
check_gate("MultiLayerT4Gron", t4_spec, t4_model, t4_refute, expected=True, modes=("prism", "audit"), bases=(t0_base, t2_base))
print("PASS Multi-layer Gen.T4.Gron (with SamePart depending on postulate partText + T0/T2 bases) verified with zero AST rewriting")

# 8. Live Node MCP check_agda RPC test (@model standalone + @refute with dep_blocks=["@model"])
mcp_ctx = scratch / "mcp_ctx"
(mcp_ctx / "drafts").mkdir(parents=True, exist_ok=True)
(mcp_ctx / "ancestors").mkdir(parents=True, exist_ok=True)
(mcp_ctx / "node-prompt.txt").write_text(
    "CURRENT CODE\nmodule Gen.T4.Gron.Reader.Prefix where\n\nSPECIFICATION\n"
    + prefix_spec
    + "\nREFUTATION EXTRA POSTULATES ({{SPEC_MOD}})\n-- (no extra test postulates beyond core specification)\nLOCKED SEEDS\n"
)
mcp_cmd = [
    prism, "mcp", "--mode", "node", "--repo", repo,
    "--lib-dir", build / "lib/lean", "--ir-dir", build / "ir",
    "--ctx-dir", mcp_ctx, "--workspace", scratch / "mcp_ws", "--dump-bin", dump_bin,
]
with subprocess.Popen(mcp_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True) as srv:
    def rpc(req_id, method, params):
        srv.stdin.write(json.dumps({"jsonrpc": "2.0", "id": req_id, "method": method, "params": params}) + "\n")
        srv.stdin.flush()
        assert select.select([srv.stdout], [], [], 120)[0], "MCP timed out"
        return json.loads(srv.stdout.readline())["result"]

    try:
        rpc(1, "initialize", {})
        rpc(2, "tools/call", {"name": "write_draft", "arguments": {"name": "m", "content": prefix_model}})
        rpc(3, "tools/call", {"name": "write_draft", "arguments": {"name": "r", "content": prefix_refute}})
        t0 = time.monotonic()
        res_m = rpc(4, "tools/call", {"name": "check_agda", "arguments": {"main_block": "@m"}})
        dt_m = time.monotonic() - t0
        txt_m = res_m["content"][0]["text"]
        assert not res_m["isError"] and "[witness: countermodel-bundle]" in txt_m and "0 SlowSlice" in txt_m, txt_m
        t1 = time.monotonic()
        res_r = rpc(5, "tools/call", {"name": "check_agda", "arguments": {"main_block": "@r", "dep_blocks": ["@m"]}})
        dt_r = time.monotonic() - t1
        txt_r = res_r["content"][0]["text"]
        assert not res_r["isError"] and "[witness: countermodel]" in txt_r and "0 SlowSlice" in txt_r, txt_r
    finally:
        srv.stdin.close()
print(f"PASS Node MCP check_agda verified @model ({dt_m:.3f}s) and @refute ({dt_r:.3f}s) in FastFocus")

# 9. Full SessionRunner E2E: T0 -> T2 -> T4 (countermodel -> independent) -> Repaired T4 (rejects false countermodel -> seals ok)
ws = scratch / "session_ws"
e2e_dir = scratch / "session_files"
e2e_dir.mkdir(parents=True, exist_ok=True)


def sess_drive(epoch, spec_text, bases=()):
    bs = " ".join(json.dumps(b) for b in bases)
    return f'(session-action (kind drive-tree) (treeName "{epoch}") (why "Drive {epoch}") (specSrc @spec) (baseTrees {bs}) (maybeLiftSrc nothing) (maybeTransportSrc nothing))\n```agda spec\n{spec_text.rstrip()}\n```\n'


def plan_reply(main_src, moves=()):
    ms = " ".join(f'(move bot (unit "{m}"))' for m in moves)
    return f'(submission (kind plan) (why "Implement") (main @main) (subspecs) (moves {ms}))\n```agda main\n{main_src.rstrip()}\n```\n'


def cm_reply(why, m_src, r_src):
    return (
        f'(submission (kind countermodel) (why "{why}") (model @model) (refute @refute))\n'
        f"```agda model\n{m_src.rstrip()}\n```\n"
        f"```agda refute\n{r_src.rstrip()}\n```\n"
    )


t0_spec_s = """module Gen.T0.Gron where
open import Data.Maybe using (Maybe; just)
data DocumentMode : Set where
  singleDocument documentStream : DocumentMode
data JsonKind : Set where
  arrayKind objectKind : JsonKind
postulate
  rootKind : DocumentMode → Maybe JsonKind → Maybe JsonKind
"""
(e2e_dir / "act_t0").write_text(sess_drive("T0", t0_spec_s))
(e2e_dir / "rep_t0").write_text(plan_reply(t0_base))
assert "ACCEPTED: ok T0" in run([gate_bin, "session", repo, ws, e2e_dir / "act_t0", "Gen.T0.Gron", e2e_dir / "rep_t0"], cwd=repo)

t2_spec_s = """module Gen.T2.Gron where
open import Data.Nat using (ℕ)
data Format : Set where
  jsAssignments valuesOnly : Format
record Reply : Set where
  constructor reply
  field
    status : ℕ
"""
(e2e_dir / "act_t2").write_text(sess_drive("T2", t2_spec_s))
(e2e_dir / "rep_t2").write_text(plan_reply(t2_base))
assert "ACCEPTED: ok T2" in run([gate_bin, "session", repo, ws, e2e_dir / "act_t2", "Gen.T2.Gron", e2e_dir / "rep_t2"], cwd=repo)

(e2e_dir / "act_t4").write_text(sess_drive("T4", t4_spec, ("T0", "T2")))
(e2e_dir / "rep_t4").write_text(cm_reply("BOM decodeUtf8+toList open roundtrip", t4_model, t4_refute))
out_t4 = run([gate_bin, "session", repo, ws, e2e_dir / "act_t4", "Gen.T4.Gron", e2e_dir / "rep_t4"], cwd=repo)
assert "ACCEPTED: independent T4 — BOM decodeUtf8+toList open roundtrip" in out_t4, out_t4
assert (ws / "trees/T4/verdict").read_text().strip() == "independent"
print("PASS Full SessionRunner E2E accepted (kind countermodel) on multi-layer T4 and recorded verdict=independent")

# 10. Formal --safe Anti-Strawman Metatheorems + Exact-Diagnostic Negative & Security Suite
anti_strawman_src = """{-# OPTIONS --safe #-}
module AntiStrawmanLaws where
open import Countermodel using (StringAlg; SoundStringModel; CharAlg; SoundCharModel)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (_++_)
open import Relation.Binary.PropositionalEquality.Core using (cong; trans)

cong₂ : {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ f {x₁} {x₂} {y₁} {y₂} px py = trans (cong (λ u → f u y₁) px) (cong (f x₂) py)

-- (a) Universal anti-strawman theorem: NO SoundStringModel can refute sixteen "ab" (32 chars)
doubleAlg : (S : StringAlg) → StringAlg.Str S → StringAlg.Str S
doubleAlg S s = StringAlg.append S s s

sixteenAlg : (S : StringAlg) → StringAlg.Str S → StringAlg.Str S
sixteenAlg S s = doubleAlg S (doubleAlg S (doubleAlg S (doubleAlg S s)))

cs2 cs4 cs8 cs16 cs32 : List Char
cs2 = 'a' ∷ 'b' ∷ []
cs4 = cs2 ++ cs2
cs8 = cs4 ++ cs4
cs16 = cs8 ++ cs8
cs32 = cs16 ++ cs16

Claim32 : StringAlg → Set
Claim32 S = StringAlg.strEq S (sixteenAlg S (StringAlg.fromList S cs2))
                              (sixteenAlg S (StringAlg.fromList S cs2)) ≡ true

eq2 : (M : SoundStringModel) →
      doubleAlg (SoundStringModel.atStage M 32) (StringAlg.fromList (SoundStringModel.atStage M 32) cs2)
      ≡ StringAlg.fromList (SoundStringModel.atStage M 32) cs4
eq2 M = SoundStringModel.appendWithin M 32 cs2 cs2 refl refl refl

eq4 : (M : SoundStringModel) →
      doubleAlg (SoundStringModel.atStage M 32) (doubleAlg (SoundStringModel.atStage M 32) (StringAlg.fromList (SoundStringModel.atStage M 32) cs2))
      ≡ StringAlg.fromList (SoundStringModel.atStage M 32) cs8
eq4 M = trans (cong₂ (StringAlg.append (SoundStringModel.atStage M 32)) (eq2 M) (eq2 M))
              (SoundStringModel.appendWithin M 32 cs4 cs4 refl refl refl)

eq8 : (M : SoundStringModel) →
      doubleAlg (SoundStringModel.atStage M 32) (doubleAlg (SoundStringModel.atStage M 32) (doubleAlg (SoundStringModel.atStage M 32) (StringAlg.fromList (SoundStringModel.atStage M 32) cs2)))
      ≡ StringAlg.fromList (SoundStringModel.atStage M 32) cs16
eq8 M = trans (cong₂ (StringAlg.append (SoundStringModel.atStage M 32)) (eq4 M) (eq4 M))
              (SoundStringModel.appendWithin M 32 cs8 cs8 refl refl refl)

eq16 : (M : SoundStringModel) →
       sixteenAlg (SoundStringModel.atStage M 32) (StringAlg.fromList (SoundStringModel.atStage M 32) cs2)
       ≡ StringAlg.fromList (SoundStringModel.atStage M 32) cs32
eq16 M = trans (cong₂ (StringAlg.append (SoundStringModel.atStage M 32)) (eq8 M) (eq8 M))
               (SoundStringModel.appendWithin M 32 cs16 cs16 refl refl refl)

realize32 : (M : SoundStringModel) → Claim32 (SoundStringModel.atStage M 32)
realize32 M = trans (cong₂ (StringAlg.strEq (SoundStringModel.atStage M 32)) (eq16 M) (eq16 M))
                    (SoundStringModel.strEqWithin M 32 cs32 cs32 refl refl)

noSoundModelRefutes32 : (M : SoundStringModel) → ((k : Nat) → Claim32 (SoundStringModel.atStage M k) → ⊥) → ⊥
noSoundModelRefutes32 M refute = refute 32 (realize32 M)

-- (b) Universal anti-strawman theorem: NO SoundStringModel can refute finite-domain Bool string law
pickBool : (S : StringAlg) → Bool → StringAlg.Str S
pickBool S true  = StringAlg.fromList S ('a' ∷ [])
pickBool S false = StringAlg.fromList S ('b' ∷ 'c' ∷ [])

ClaimFiniteBool : StringAlg → Set
ClaimFiniteBool S = (b : Bool) → StringAlg.strEq S (pickBool S b) (pickBool S b) ≡ true

realizeBool : (M : SoundStringModel) → ClaimFiniteBool (SoundStringModel.atStage M 2)
realizeBool M true  = SoundStringModel.strEqWithin M 2 ('a' ∷ []) ('a' ∷ []) refl refl
realizeBool M false = SoundStringModel.strEqWithin M 2 ('b' ∷ 'c' ∷ []) ('b' ∷ 'c' ∷ []) refl refl

noSoundModelRefutesFiniteBool : (M : SoundStringModel) → ((k : Nat) → ClaimFiniteBool (SoundStringModel.atStage M k) → ⊥) → ⊥
noSoundModelRefutesFiniteBool M refute = refute 2 (realizeBool M)

-- (c) Universal anti-strawman theorem: NO SoundCharModel can refute bounded closed codepoint evaluation
ClaimBoundedChar : CharAlg → Set
ClaimBoundedChar C = CharAlg.charToNat C (CharAlg.natToChar C 65) ≡ 65

realizeBoundedChar : (MC : SoundCharModel) → ClaimBoundedChar (SoundCharModel.atCharStage MC 65)
realizeBoundedChar MC =
  trans (cong (CharAlg.charToNat (SoundCharModel.atCharStage MC 65)) (SoundCharModel.natToCharLaw MC 65 65))
        (SoundCharModel.charToNatWithin MC 65 'A' refl)

noSoundModelRefutesBoundedChar : (MC : SoundCharModel) → ((k : Nat) → ClaimBoundedChar (SoundCharModel.atCharStage MC k) → ⊥) → ⊥
noSoundModelRefutesBoundedChar MC refute = refute 65 (realizeBoundedChar MC)
"""
anti_file = cm_src_dir / "AntiStrawmanLaws.agda"
anti_file.write_text(anti_strawman_src)
run(["agda", "--safe", "--no-libraries", "-i", cm_src_dir, "-i", "/usr/share/agda-stdlib", anti_file], cwd=cm_src_dir)
run([
    prism, "prism-check", "--lib-dir", build / "lib/lean",
    "--work-dir", scratch / "anti_prism", "--dump-bin", dump_bin,
    "--dep", cm_file, "--main", anti_file,
])
print("PASS Formal --safe + Lean Prism metatheorems: NO SoundModel can refute 32-char literal, finite Bool, or bounded Char")

provable_closed_spec = """module ProvableClosed where
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String; primStringAppend; primStringEquality)

double : String → String
double s = primStringAppend s s

sixteen : String → String
sixteen s = double (double (double (double s)))

postulate
  closed32 : primStringEquality (sixteen "ab") (sixteen "ab") ≡ true
"""

lying_model_no_agreement = """{-# OPTIONS --safe #-}
module LyingModel where
open import Countermodel using (StringAlg; stringAlg; SoundStringModel; soundStringModel; CountermodelBundle; stringCountermodel; false≢true)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)

-- Lies about strEq even within stage k: passes validCountermodel, fails kernel typecheck on strEqWithin!
badAlg : Nat → StringAlg
badAlg _ = stringAlg (List Char) (λ s → s) (λ cs → cs) _++_ (λ _ _ → false) (λ _ _ p → p) (λ _ _ p → p)

badModel : SoundStringModel
badModel = soundStringModel badAlg (λ _ _ _ → refl) (λ _ _ _ _ _ _ → refl) (λ _ _ _ _ _ → refl)

Claim : StringAlg → Set
Claim S = StringAlg.strEq S (StringAlg.fromList S ('a' ∷ [])) (StringAlg.fromList S ('a' ∷ [])) ≡ true

bundle : CountermodelBundle
bundle = stringCountermodel Claim badModel (λ _ h → false≢true h)
"""

closed_refute_attempt = """module ClosedRefute where
import ProvableClosed as Spec
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (primStringEquality)

ClaimTrue : primStringEquality "a" "a" ≡ true
ClaimTrue = refl

witness : VerifiedClaim
witness = verifiedClaim ClaimTrue
"""
check_gate(
    "RejectLyingModel",
    provable_closed_spec,
    lying_model_no_agreement,
    closed_refute_attempt,
    expected=False,
    expect_err="@model ordinaryCheck failed:\nLEAN_TYPE_ERROR",
)
print("PASS Lying model violating finite-stage strEqWithin agreement fails at kernel typecheck")

# Sound breakStrEqModel attempting to refute sixteen "ab" (would succeed if k were fixed at 0..31, blocked by ∀ k at k ≥ 32!)
bad_32_model = """{-# OPTIONS --safe #-}
module Bad32Model where
open import Countermodel using (StringAlg; CountermodelBundle; stringCountermodel; breakStrEqModel; false≢true)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (sym)

doubleAlg : (S : StringAlg) → StringAlg.Str S → StringAlg.Str S
doubleAlg S s = StringAlg.append S s s

sixteenAlg : (S : StringAlg) → StringAlg.Str S → StringAlg.Str S
sixteenAlg S s = doubleAlg S (doubleAlg S (doubleAlg S (doubleAlg S s)))

Claim : StringAlg → Set
Claim S = StringAlg.strEq S (sixteenAlg S (StringAlg.fromList S ('a' ∷ 'b' ∷ [])))
                            (sixteenAlg S (StringAlg.fromList S ('a' ∷ 'b' ∷ []))) ≡ true

bundle : CountermodelBundle
bundle = stringCountermodel Claim breakStrEqModel (λ k h → false≢true (sym h))
"""
bad_32_refute = """module Bad32Refute where
import ProvableClosed as Spec
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
witness : VerifiedClaim
witness = verifiedClaim Spec.closed32
"""
check_gate(
    "RejectProvable32CharLiteral",
    provable_closed_spec,
    bad_32_model,
    bad_32_refute,
    expected=False,
    expect_err="@model ordinaryCheck failed:\nLEAN_TYPE_ERROR",
)
print("PASS Sound model cannot refute provable 32-char closed literal equation (blocked at kernel typecheck)")

# Sound breakStrEqModel attempting to refute finite-domain Bool string equation (would succeed at k = 0, blocked by ∀ k!)
finite_bool_spec = """module FiniteBoolSpec where
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool.Base using (if_then_else_)
postulate
  boolStrEq : (b : Bool) → primStringEquality (if b then "a" else "bc") (if b then "a" else "bc") ≡ true
"""
bad_bool_model = """{-# OPTIONS --safe #-}
module BadBoolModel where
open import Countermodel using (StringAlg; CountermodelBundle; stringCountermodel; breakStrEqModel; false≢true)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Bool.Base using (if_then_else_)
open import Relation.Binary.PropositionalEquality.Core using (sym)

pick : (S : StringAlg) → Bool → StringAlg.Str S
pick S b = if b then StringAlg.fromList S ('a' ∷ []) else StringAlg.fromList S ('b' ∷ 'c' ∷ [])

Claim : StringAlg → Set
Claim S = (b : Bool) → StringAlg.strEq S (pick S b) (pick S b) ≡ true

bundle : CountermodelBundle
bundle = stringCountermodel Claim breakStrEqModel (λ k h → false≢true (sym (h true)))
"""
bad_bool_refute = """module BadBoolRefute where
import FiniteBoolSpec as Spec
open import CountermodelCheck using (VerifiedClaim; verifiedClaim)
open import Agda.Builtin.Bool using (true; false)
witness : VerifiedClaim
witness = verifiedClaim (λ { true → Spec.boolStrEq true ; false → Spec.boolStrEq false })
"""
check_gate(
    "RejectProvableFiniteBool",
    finite_bool_spec,
    bad_bool_model,
    bad_bool_refute,
    expected=False,
    expect_err="@model ordinaryCheck failed:\nLEAN_TYPE_ERROR",
)
print("PASS Sound model cannot refute provable finite-domain Bool string equation (blocked at kernel typecheck)")

# Security boundary rejections on @model and @refute — each syntactically complete and asserting its exact gate diagnostic!
security_cases = [
    (
        "ModelMissingSafe",
        dash_model.replace("{-# OPTIONS --safe #-}\n", ""),
        dash_refute,
        'validCountermodel failed:\n(flagEnvelopeViolation)',
    ),
    (
        "ModelImportsBuiltinString",
        dash_model.replace("module DashModel where\n", "module DashModel where\nimport Agda.Builtin.String\n"),
        dash_refute,
        'validCountermodel failed:\n(unauthorizedImport (q "Agda.Builtin.String" "Agda.Builtin.String"))',
    ),
    (
        "ModelImportsDataString",
        dash_model.replace("module DashModel where\n", "module DashModel where\nimport Data.String\n"),
        dash_refute,
        'validCountermodel failed:\n(unauthorizedImport (q "Data.String" "Data.String"))',
    ),
    (
        "ModelUsesNatShow",
        dash_model.replace(
            "module DashModel where\n",
            "module DashModel where\nopen import Data.Nat.Show using (show)\nopen import Data.Unit.Base using (⊤; tt)\n",
        ) + "\nuseShow : ℕ → ⊤\nuseShow n = (λ _ → tt) (show n)\n",
        dash_refute,
        'validCountermodel failed:\n(unauthorizedImport "Data.Nat.Show.show")',
    ),
    (
        "ModelUsesPrimCharEq",
        dash_model.replace(
            "module DashModel where\n",
            "module DashModel where\nopen import Agda.Builtin.Char using (Char; primCharEquality)\nopen import Agda.Builtin.Bool using (Bool)\n",
        ) + "\nusePrimCharEq : Char → Bool\nusePrimCharEq c = primCharEquality c c\n",
        dash_refute,
        'validCountermodel failed:\n(unauthorizedImport "Agda.Builtin.Char.primCharEquality")',
    ),
    (
        "ModelImportsContext",
        dash_model.replace("module DashModel where\n", "module DashModel where\nimport Context.Terminal\n"),
        dash_refute,
        'validCountermodel failed:\n(unauthorizedImport (q "Context.Terminal" "Context.Terminal"))',
    ),
    (
        "ModelStringLiteral",
        dash_model.replace(
            "module DashModel where\n",
            "module DashModel where\nimport Data.Nat.Show\nopen import Data.Unit.Base using (⊤; tt)\n",
        ) + '\nsneakLit : ⊤\nsneakLit = (λ _ → tt) "forbidden"\n',
        dash_refute,
        'validCountermodel failed:\n(flagEnvelopeViolation)',
    ),
    (
        "ModelPostulateWithSafe",
        dash_model + "\npostulate cheat : ℕ\n",
        dash_refute,
        "Cannot postulate cheat with safe flag",
    ),
    (
        "ModelPostulateNoSafe",
        dash_model.replace("{-# OPTIONS --safe #-}\n", "") + "\npostulate cheat : ℕ\n",
        dash_refute,
        '(unimplementedPostulate "DashModel.cheat")',
    ),
    (
        "ModelMissingBundle",
        dash_model.split("\nbundle : CountermodelBundle")[0] + "\n",
        dash_refute,
        "validCountermodel failed:\n(missingCountermodelBundle)",
    ),
    (
        "ModelTrustMe",
        dash_model.replace(
            "module DashModel where\n", "module DashModel where\nimport Agda.Builtin.TrustMe\n"
        ),
        dash_refute,
        "@model dump failed:\nuser error (sandbox: forbidden module name or import in DashModel",
    ),
    (
        "ModelShadowsCountermodel",
        "{-# OPTIONS --safe #-}\nmodule Countermodel where\nopen import Agda.Builtin.Bool using (Bool; true)\nx : Bool\nx = true\n",
        dash_refute,
        'validCountermodel failed:\n(unauthorizedImport "Countermodel")',
    ),
    (
        "RefuteTrustMe",
        dash_model,
        dash_refute.replace("module DashRefute where\n", "module DashRefute where\nimport Agda.Builtin.TrustMe\n"),
        "@refute dump failed:\nuser error (sandbox: forbidden module name or import in DashRefute",
    ),
    (
        "RefutePostulate",
        dash_model,
        dash_refute + "\npostulate cheat : VerifiedClaim\n",
        'validCountermodelRefute failed:\n(unimplementedPostulate "DashRefute.cheat")',
    ),
    (
        "RefutePrivateWitness",
        dash_model,
        dash_refute.replace("witness : VerifiedClaim", "private\n  witness : VerifiedClaim").replace(
            "witness = verifiedClaim", "  witness = verifiedClaim"
        ),
        "validCountermodelRefute failed:\n(missingCountermodelRefute)",
    ),
    (
        "RefuteShadowsBridge",
        dash_model,
        "module CountermodelCheck where\nopen import Agda.Builtin.Bool using (Bool; true)\nx : Bool\nx = true\n",
        'validCountermodelRefute failed:\n(unauthorizedImport "CountermodelCheck")',
    ),
]
for label, bad_m, bad_r, expected_diag in security_cases:
    check_gate(label, dash_spec, bad_m, bad_r, expected=False, expect_err=expected_diag)
    print(f"PASS Rejected {label} with exact diagnostic {expected_diag.splitlines()[-1]}")

print("=== ALL COUNTERMODEL POSITIVE, METATHEOREM, MULTI-LAYER, MCP, SESSION & SECURITY GATES PASSED ===")
