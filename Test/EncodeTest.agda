------------------------------------------------------------------------
-- Test/EncodeTest.agda —— Code → s-expr → Code 回环（存盘格式的正确性），类型检查时算
------------------------------------------------------------------------
module Test.EncodeTest where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Code
open import Code.SExpr
open import Code.Encode
open import Code.Parse
open import Test.TransportTest using (C₀)

-- 编码再解码，一个字都不少
_ : decodeCode (encodeCode C₀) ≡ just C₀
_ = refl

-- 打成字符串再读回来也一样（parse = parseSExpr ∘ decodeCode）
_ : parse (showSExpr (encodeCode C₀)) ≡ just C₀
_ = refl

-- A plan scoped in another module retains its origin across persistence.
open import Code.Transport using (mkPlan)
open import Data.List using ([]; _∷_)

origin-roundtrip : decodePlan (encodePlan (mkPlan "rename scope" (just (mkQ ("Source" ∷ []))) [] []))
                 ≡ just (mkPlan "rename scope" (just (mkQ ("Source" ∷ []))) [] [])
origin-roundtrip = refl

-- CR must survive both the dump pipe and generated Agda source. Text-mode
-- subprocess readers normalize a literal CR to LF unless it is escaped.
open import Code.Render using (escapeStr; renderLit)
open import Data.String using (toList)
open import Data.Char using (toℕ)
open import Data.List using (map)

carriage-return-escape : escapeStr "a\rb" ≡ "a\\rb"
carriage-return-escape = refl

carriage-return-character : renderLit (charL '\r') ≡ "'\\r'"
carriage-return-character = refl

crlf-literal-values : map toℕ (toList "\r\n") ≡ (13 ∷ 10 ∷ [])
crlf-literal-values = refl
