{-# OPTIONS --safe #-}
module Context.Tools.NetLaws where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Char using (Char)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length; drop)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import Context.Terminal using (Byte; Bytes; byte; bytes)
open import Context.Tools.FsSandbox using (all)
open import Context.Tools.FsLaws using (≡ᵇ-refl)
open import Context.Tools.NetSandbox

------------------------------------------------------------------------
-- §1 Byte-Prefix, Framing & Token Predicates
------------------------------------------------------------------------

prefixBytes-refl : ∀ (bs : Bytes) → prefixBytes bs bs ≡ true
prefixBytes-refl []       = refl
prefixBytes-refl (b ∷ bs) rewrite ≡ᵇ-refl (toℕ b) = prefixBytes-refl bs

prefixBytes-++ : ∀ (xs ys : Bytes) → prefixBytes xs (xs ++ ys) ≡ true
prefixBytes-++ []       _  = refl
prefixBytes-++ (x ∷ xs) ys rewrite ≡ᵇ-refl (toℕ x) = prefixBytes-++ xs ys

drop-length-++ : ∀ (xs ys : Bytes) → drop (length xs) (xs ++ ys) ≡ ys
drop-length-++ []       ys = refl
drop-length-++ (_ ∷ xs) ys = drop-length-++ xs ys

NoCR : Bytes → Bool
NoCR = all (λ b → not (13 ≡ᵇ toℕ b))

NoCRLF : Bytes → Bool
NoCRLF = all (λ b → not (13 ≡ᵇ toℕ b) ∧ not (10 ≡ᵇ toℕ b))

TokenByte : Byte → Bool
TokenByte b = not (isAsciiSpaceByte b) ∧ not (13 ≡ᵇ toℕ b) ∧ not (10 ≡ᵇ toℕ b)

NonEmptyBytes : Bytes → Bool
NonEmptyBytes []      = false
NonEmptyBytes (_ ∷ _) = true

ValidTokenBytes : Bytes → Bool
ValidTokenBytes bs = NonEmptyBytes bs ∧ all TokenByte bs

ValidHttpToken : String → Bool
ValidHttpToken s = ValidTokenBytes (bytes s)

private
  and-l : ∀ (a b : Bool) → (a ∧ b) ≡ true → a ≡ true
  and-l true  _ _ = refl
  and-l false _ ()

  and-r : ∀ (a b : Bool) → (a ∧ b) ≡ true → b ≡ true
  and-r true  _ h = h
  and-r false _ ()

  not-true⇒false : ∀ {b : Bool} → not b ≡ true → b ≡ false
  not-true⇒false {false} _ = refl
  not-true⇒false {true}  ()

  rev-step : ∀ {A : Set} (acc : List A) (x : A) (xs : List A) →
    reverse (x ∷ acc) ++ xs ≡ reverse acc ++ (x ∷ xs)
  rev-step acc x xs
    rewrite LP.unfold-reverse x acc
          | LP.++-assoc (reverse acc) (x ∷ []) xs = refl

  noCRLF⇒noCR : ∀ (bs : Bytes) → NoCRLF bs ≡ true → NoCR bs ≡ true
  noCRLF⇒noCR []       _  = refl
  noCRLF⇒noCR (b ∷ bs) ok with 13 ≡ᵇ toℕ b | 10 ≡ᵇ toℕ b
  ... | true  | _     = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false | false = noCRLF⇒noCR bs ok

  allToken⇒noCR : ∀ (bs : Bytes) → all TokenByte bs ≡ true → NoCR bs ≡ true
  allToken⇒noCR []       _  = refl
  allToken⇒noCR (b ∷ bs) ok with isAsciiSpaceByte b
  ... | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false with 13 ≡ᵇ toℕ b | 10 ≡ᵇ toℕ b
  ...   | true  | _     = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ...   | false | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ...   | false | false = allToken⇒noCR bs ok

  noCR-++ : ∀ (xs ys : Bytes) → NoCR xs ≡ true → NoCR ys ≡ true → NoCR (xs ++ ys) ≡ true
  noCR-++ []       _  _   okY = okY
  noCR-++ (x ∷ xs) ys okX okY with 13 ≡ᵇ toℕ x
  ... | true  = ⊥-elim (false≢true okX) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false = noCR-++ xs ys okX okY

  digitChar-token : ∀ (n : ℕ) → TokenByte (byte (Data.Char.toℕ (digitChar n))) ≡ true
  digitChar-token 0 = refl
  digitChar-token 1 = refl
  digitChar-token 2 = refl
  digitChar-token 3 = refl
  digitChar-token 4 = refl
  digitChar-token 5 = refl
  digitChar-token 6 = refl
  digitChar-token 7 = refl
  digitChar-token 8 = refl
  digitChar-token (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))) = refl

  decCharsFuel-allToken : ∀ (fuel n : ℕ) (acc : List Char) →
    all TokenByte (map (λ c → byte (Data.Char.toℕ c)) acc) ≡ true →
    all TokenByte (map (λ c → byte (Data.Char.toℕ c)) (decCharsFuel fuel n acc)) ≡ true
  decCharsFuel-allToken zero _ _ okAcc = okAcc
  decCharsFuel-allToken (suc f) n acc okAcc with n <ᵇ 10
  ... | true  rewrite digitChar-token n = okAcc
  ... | false = decCharsFuel-allToken f (n / 10) (digitChar (n % 10) ∷ acc)
                  (trans (cong (λ z → z ∧ all TokenByte (map (λ c → byte (Data.Char.toℕ c)) acc)) (digitChar-token (n % 10))) okAcc)

  decCharsFuel-nonEmpty-acc : ∀ (fuel n : ℕ) (c : Char) (cs : List Char) →
    NonEmptyBytes (map (λ ch → byte (Data.Char.toℕ ch)) (decCharsFuel fuel n (c ∷ cs))) ≡ true
  decCharsFuel-nonEmpty-acc zero    _ _ _  = refl
  decCharsFuel-nonEmpty-acc (suc f) n c cs with n <ᵇ 10
  ... | true  = refl
  ... | false = decCharsFuel-nonEmpty-acc f (n / 10) (digitChar (n % 10)) (c ∷ cs)

  decBytes-nonEmpty : ∀ (n : ℕ) → NonEmptyBytes (decBytes n) ≡ true
  decBytes-nonEmpty n with n <ᵇ 10
  ... | true  = refl
  ... | false = decCharsFuel-nonEmpty-acc n (n / 10) (digitChar (n % 10)) []

  decBytes-validToken : ∀ (n : ℕ) → ValidTokenBytes (decBytes n) ≡ true
  decBytes-validToken n =
    trans (cong (λ z → z ∧ all TokenByte (decBytes n)) (decBytes-nonEmpty n))
          (decCharsFuel-allToken (suc n) n [] refl)

  decBytes-noCR : ∀ (n : ℕ) → NoCR (decBytes n) ≡ true
  decBytes-noCR n = allToken⇒noCR (decBytes n) (decCharsFuel-allToken (suc n) n [] refl)

  -- Core framing lemma 1: `splitMarkGo (bytes "\r\n")` skips any `NoCR` prefix and splits at `\r\n`!
  split-crlf-go : ∀ (acc pre rest : Bytes) →
    NoCR pre ≡ true →
    splitMarkGo (bytes "\r\n") acc (pre ++ bytes "\r\n" ++ rest) ≡
    just (reverse acc ++ pre , rest)
  split-crlf-go acc [] rest _ rewrite LP.++-identityʳ (reverse acc) = refl
  split-crlf-go acc (b ∷ bs) rest ok with 13 ≡ᵇ toℕ b
  ... | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false =
      trans (split-crlf-go (b ∷ acc) bs rest ok)
            (cong (λ z → just (z , rest)) (rev-step acc b bs))

  -- Core framing lemma 2: `splitMarkGo (bytes "\r\n\r\n")` skips any `NoCR` prefix!
  skip-crlf2-simple : ∀ (acc pre tailB : Bytes) →
    NoCR pre ≡ true →
    splitMarkGo (bytes "\r\n\r\n") acc (pre ++ tailB) ≡
    splitMarkGo (bytes "\r\n\r\n") (Data.List.foldl (λ a x → x ∷ a) acc pre) tailB
  skip-crlf2-simple _   []       _     _  = refl
  skip-crlf2-simple acc (b ∷ bs) tailB ok with 13 ≡ᵇ toℕ b
  ... | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false = skip-crlf2-simple (b ∷ acc) bs tailB ok

  -- Token word splitting lemma:
  words-token-step : ∀ (acc tok rest : Bytes) →
    all TokenByte tok ≡ true →
    wordsBytesGo acc (tok ++ byte 32 ∷ rest) ≡
    wordsBytesGo (Data.List.foldl (λ a x → x ∷ a) acc tok) (byte 32 ∷ rest)
  words-token-step _   []       _    _  = refl
  words-token-step acc (b ∷ bs) rest ok with isAsciiSpaceByte b
  ... | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false = words-token-step (b ∷ acc) bs rest (and-r (not (13 ≡ᵇ toℕ b) ∧ not (10 ≡ᵇ toℕ b)) (all TokenByte bs) ok)

  foldl-rev-id : ∀ (xs : Bytes) → reverse (Data.List.foldl (λ a x → x ∷ a) [] xs) ≡ xs
  foldl-rev-id xs = LP.reverse-involutive xs

  nonEmptyFold : ∀ (x : Byte) (a xs : Bytes) →
    Data.List.foldl (λ acc y → y ∷ acc) (x ∷ a) xs ≡ [] → ⊥
  nonEmptyFold _ _ []       ()
  nonEmptyFold _ a (y ∷ ys) eq = nonEmptyFold y (_ ∷ a) ys eq

  words-nonempty-token : ∀ (tok rest : Bytes) →
    ValidTokenBytes tok ≡ true →
    wordsBytesGo [] (tok ++ byte 32 ∷ rest) ≡ tok ∷ wordsBytesGo [] rest
  words-nonempty-token []       _    ok with ok
  ... | ()
  words-nonempty-token (b ∷ bs) rest ok with isAsciiSpaceByte b
  ... | true  = ⊥-elim (false≢true ok) where false≢true : false ≡ true → ⊥ ; false≢true ()
  ... | false
    rewrite words-token-step (b ∷ []) bs rest (and-r (not (13 ≡ᵇ toℕ b) ∧ not (10 ≡ᵇ toℕ b)) (all TokenByte bs) ok) =
      helper (Data.List.foldl (λ a x → x ∷ a) (b ∷ []) bs) refl
    where
      helper : ∀ (zs : Bytes) →
        zs ≡ Data.List.foldl (λ a x → x ∷ a) (b ∷ []) bs →
        wordsBytesGo zs (byte 32 ∷ rest) ≡ (b ∷ bs) ∷ wordsBytesGo [] rest
      helper []      eq = ⊥-elim (nonEmptyFold b [] bs (sym eq))
      helper (h ∷ t) eq =
        cong (λ w → w ∷ wordsBytesGo [] rest)
          (trans (cong reverse eq) (LP.reverse-involutive (b ∷ bs)))

  req-hdr-tail : ℕ → Bytes → Bytes
  req-hdr-tail len body =
    bytes "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: "
    ++ decBytes len ++ bytes "\r\n\r\n" ++ body

  data ∃SplitBody : Maybe (Bytes × Bytes) → Bytes → Set where
    gotBody : ∀ {hdr} {b} → ∃SplitBody (just (hdr , b)) b

  split-crlf2-req-hdr : ∀ (acc : Bytes) (len : ℕ) (body : Bytes) →
    ∃SplitBody (splitMarkGo (bytes "\r\n\r\n") acc (req-hdr-tail len body)) body
  split-crlf2-req-hdr acc len body =
    substSplit
      (sym (trans
        (stepLiteral acc)
        (skip-crlf2-simple _ (decBytes len) (bytes "\r\n\r\n" ++ body) (decBytes-noCR len))))
      gotBody
    where
      substSplit : ∀ {m₁ m₂ b} → m₁ ≡ m₂ → ∃SplitBody m₁ b → ∃SplitBody m₂ b
      substSplit refl x = x

      -- All 54 bytes of "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: "
      -- end in ": " (bytes 58, 32), so none of its 3 `\r\n` occurrences is followed by `\r`!
      stepLiteral : ∀ (a : Bytes) →
        splitMarkGo (bytes "\r\n\r\n") a (req-hdr-tail len body) ≡
        splitMarkGo (bytes "\r\n\r\n")
          (Data.List.foldl (λ acc′ x → x ∷ acc′) a (bytes "\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: "))
          (decBytes len ++ bytes "\r\n\r\n" ++ body)
      stepLiteral a = refl

------------------------------------------------------------------------
-- §2 Universal HTTP Request Encode/Parse Roundtrip Theorem (`∀ method path body`)
------------------------------------------------------------------------

parseHttpReq-encode-roundtrip :
  ∀ (method path : String) (body : Bytes) →
  ValidHttpToken method ≡ true →
  ValidHttpToken path ≡ true →
  parseHttpReq (encodeHttpReq method path [] body)
    ≡ just (httpReqView (wireText (bytes method)) (wireText (bytes path)) body)
parseHttpReq-encode-roundtrip method path body okM okP =
  let line = bytes method ++ bytes " " ++ bytes path ++ bytes " HTTP/1.1"
      noCrLine : NoCR line ≡ true
      noCrLine =
        noCR-++ (bytes method) (bytes " " ++ bytes path ++ bytes " HTTP/1.1")
          (allToken⇒noCR (bytes method) (and-r (NonEmptyBytes (bytes method)) (all TokenByte (bytes method)) okM))
          (noCR-++ (bytes " ") (bytes path ++ bytes " HTTP/1.1") refl
            (noCR-++ (bytes path) (bytes " HTTP/1.1")
              (allToken⇒noCR (bytes path) (and-r (NonEmptyBytes (bytes path)) (all TokenByte (bytes path)) okP)) refl))
      reassoc : encodeHttpReq method path [] body ≡ line ++ req-hdr-tail (length body) body
      reassoc =
        trans
          (cong (λ tl → bytes method ++ bytes " " ++ bytes path ++ bytes " HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\nContent-Length: " ++ tl)
                (LP.++-assoc (decBytes (length body)) (bytes "\r\n") (bytes "\r\n" ++ body)))
          (sym (trans
            (LP.++-assoc (bytes method) (bytes " " ++ bytes path ++ bytes " HTTP/1.1") (req-hdr-tail (length body) body))
            (cong (λ z → bytes method ++ byte 32 ∷ z)
              (LP.++-assoc (bytes path) (bytes " HTTP/1.1") (req-hdr-tail (length body) body)))))
      reassocCrlf : line ++ req-hdr-tail (length body) body ≡
        line ++ bytes "\r\n" ++ (bytes "Host: 127.0.0.1\r\nConnection: close\r\nContent-Length: "
          ++ decBytes (length body) ++ bytes "\r\n\r\n" ++ body)
      reassocCrlf = refl
      split1 : splitMark (bytes "\r\n") (encodeHttpReq method path [] body)
                 ≡ just (line , (bytes "Host: 127.0.0.1\r\nConnection: close\r\nContent-Length: "
                                  ++ decBytes (length body) ++ bytes "\r\n\r\n" ++ body))
      split1 = trans (cong (splitMark (bytes "\r\n")) reassoc)
                     (split-crlf-go [] line _ noCrLine)
      split2Eq : splitMark (bytes "\r\n\r\n") (encodeHttpReq method path [] body)
                   ≡ splitMarkGo (bytes "\r\n\r\n") (Data.List.foldl (λ a x → x ∷ a) [] line)
                       (req-hdr-tail (length body) body)
      split2Eq = trans (cong (splitMark (bytes "\r\n\r\n")) reassoc)
                       (skip-crlf2-simple [] line (req-hdr-tail (length body) body) noCrLine)
      wordsLine : wordsBytes line ≡ bytes method ∷ bytes path ∷ bytes "HTTP/1.1" ∷ []
      wordsLine =
        trans (words-nonempty-token (bytes method) (bytes path ++ bytes " HTTP/1.1") okM)
              (cong (bytes method ∷_) (words-nonempty-token (bytes path) (bytes "HTTP/1.1") okP))
  in finishReq split1 split2Eq (split-crlf2-req-hdr (Data.List.foldl (λ a x → x ∷ a) [] line) (length body) body) wordsLine
  where
    finishReq :
      ∀ {line rem m₂} →
      splitMark (bytes "\r\n") (encodeHttpReq method path [] body) ≡ just (line , rem) →
      splitMark (bytes "\r\n\r\n") (encodeHttpReq method path [] body) ≡ m₂ →
      ∃SplitBody m₂ body →
      wordsBytes line ≡ bytes method ∷ bytes path ∷ bytes "HTTP/1.1" ∷ [] →
      parseHttpReq (encodeHttpReq method path [] body)
        ≡ just (httpReqView (wireText (bytes method)) (wireText (bytes path)) body)
    finishReq s1 s2 (gotBody {hdr}) wEq
      rewrite s1 | s2 | wEq = refl

parseHttpReq-body-roundtrip :
  ∀ (method path : String) (body : Bytes) →
  ValidHttpToken method ≡ true →
  ValidHttpToken path ≡ true →
  Data.Maybe.map reqBody (parseHttpReq (encodeHttpReq method path [] body)) ≡ just body
parseHttpReq-body-roundtrip method path body okM okP
  rewrite parseHttpReq-encode-roundtrip method path body okM okP = refl

private
  resp-hdr-tail : ℕ → Bytes → Bytes
  resp-hdr-tail len body =
    bytes "\r\nContent-Length: " ++ decBytes len ++ bytes "\r\nConnection: close\r\n\r\n" ++ body

  split-crlf2-resp-hdr : ∀ (acc : Bytes) (len : ℕ) (body : Bytes) →
    ∃SplitBody (splitMarkGo (bytes "\r\n\r\n") acc (resp-hdr-tail len body)) body
  split-crlf2-resp-hdr acc len body =
    let acc₁ = Data.List.foldl (λ acc′ x → x ∷ acc′) acc (bytes "\r\nContent-Length: ")
        acc₂ = Data.List.foldl (λ a x → x ∷ a) acc₁ (decBytes len)
    in substSplit
         (sym (trans
           (stepPrefix acc)
           (trans
             (skip-crlf2-simple acc₁ (decBytes len) (bytes "\r\nConnection: close\r\n\r\n" ++ body) (decBytes-noCR len))
             (stepSuffix acc₂))))
         gotBody
    where
      substSplit : ∀ {m₁ m₂ b} → m₁ ≡ m₂ → ∃SplitBody m₁ b → ∃SplitBody m₂ b
      substSplit refl x = x

      stepPrefix : ∀ (a : Bytes) →
        splitMarkGo (bytes "\r\n\r\n") a (resp-hdr-tail len body) ≡
        splitMarkGo (bytes "\r\n\r\n")
          (Data.List.foldl (λ acc′ x → x ∷ acc′) a (bytes "\r\nContent-Length: "))
          (decBytes len ++ bytes "\r\nConnection: close\r\n\r\n" ++ body)
      stepPrefix _ = refl

      stepSuffix : ∀ (a : Bytes) →
        splitMarkGo (bytes "\r\n\r\n") a (bytes "\r\nConnection: close\r\n\r\n" ++ body) ≡
        just (reverse (Data.List.foldl (λ acc′ x → x ∷ acc′) a (bytes "\r\nConnection: close")) , body)
      stepSuffix _ = refl

parseHttpResp-encode-roundtrip :
  ∀ (status : ℕ) (reason : String) (body : Bytes) →
  statusValue (decBytes status) ≡ just status →
  NoCR (bytes reason) ≡ true →
  parseHttpResp (encodeHttpResp status reason [] body)
    ≡ just (httpRespView status body)
parseHttpResp-encode-roundtrip status reason body okStatus okReason =
  let line = bytes "HTTP/1.1 " ++ decBytes status ++ bytes " " ++ bytes reason
      noCrLine : NoCR line ≡ true
      noCrLine =
        noCR-++ (bytes "HTTP/1.1 ") (decBytes status ++ bytes " " ++ bytes reason) refl
          (noCR-++ (decBytes status) (bytes " " ++ bytes reason) (decBytes-noCR status)
            (noCR-++ (bytes " ") (bytes reason) refl okReason))
      reassoc : encodeHttpResp status reason [] body ≡ line ++ resp-hdr-tail (length body) body
      reassoc =
        trans
          (cong (λ tl → bytes "HTTP/1.1 " ++ decBytes status ++ bytes " " ++ bytes reason ++ bytes "\r\nContent-Length: " ++ tl)
                (LP.++-assoc (decBytes (length body)) (bytes "\r\n") (bytes "Connection: close\r\n\r\n" ++ body)))
          (sym (cong (bytes "HTTP/1.1 " ++_)
                (LP.++-assoc (decBytes status) (bytes " " ++ bytes reason) (resp-hdr-tail (length body) body))))
      split1 : splitMark (bytes "\r\n") (encodeHttpResp status reason [] body)
                 ≡ just (line , (bytes "Content-Length: " ++ decBytes (length body)
                                  ++ bytes "\r\nConnection: close\r\n\r\n" ++ body))
      split1 = trans (cong (splitMark (bytes "\r\n")) reassoc)
                     (split-crlf-go [] line _ noCrLine)
      split2Eq : splitMark (bytes "\r\n\r\n") (encodeHttpResp status reason [] body)
                   ≡ splitMarkGo (bytes "\r\n\r\n") (Data.List.foldl (λ a x → x ∷ a) [] line)
                       (resp-hdr-tail (length body) body)
      split2Eq = trans (cong (splitMark (bytes "\r\n\r\n")) reassoc)
                       (skip-crlf2-simple [] line (resp-hdr-tail (length body) body) noCrLine)
      wordsLine : wordsBytes line ≡ bytes "HTTP/1.1" ∷ decBytes status ∷ wordsBytes (bytes reason)
      wordsLine =
        cong (bytes "HTTP/1.1" ∷_)
          (words-nonempty-token (decBytes status) (bytes reason) (decBytes-validToken status))
  in finishResp split1 split2Eq (split-crlf2-resp-hdr (Data.List.foldl (λ a x → x ∷ a) [] line) (length body) body) wordsLine
  where
    finishResp :
      ∀ {line rem m₂} →
      splitMark (bytes "\r\n") (encodeHttpResp status reason [] body) ≡ just (line , rem) →
      splitMark (bytes "\r\n\r\n") (encodeHttpResp status reason [] body) ≡ m₂ →
      ∃SplitBody m₂ body →
      wordsBytes line ≡ bytes "HTTP/1.1" ∷ decBytes status ∷ wordsBytes (bytes reason) →
      parseHttpResp (encodeHttpResp status reason [] body)
        ≡ just (httpRespView status body)
    finishResp s1 s2 (gotBody {hdr}) wEq
      rewrite s1 | s2 | wEq | okStatus = refl

------------------------------------------------------------------------
-- §3 Universal Stub Exchange Homomorphism Laws (`∀ mode xs ys`)
------------------------------------------------------------------------

evalStubExchange-reqs : ∀ (mode : NetTopology) (reqs : List Bytes) →
  proj₁ (evalStubExchange mode reqs) ≡ reqs
evalStubExchange-reqs _ _ = refl

evalStubExchange-++ : ∀ (mode : NetTopology) (xs ys : List Bytes) →
  proj₂ (evalStubExchange mode (xs ++ ys)) ≡
  proj₂ (evalStubExchange mode xs) ++ proj₂ (evalStubExchange mode ys)
evalStubExchange-++ _   []       _  = refl
evalStubExchange-++ mode (x ∷ xs) ys =
  cong (stubReply mode x ∷_) (evalStubExchange-++ mode xs ys)
