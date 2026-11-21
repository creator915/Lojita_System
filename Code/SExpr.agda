------------------------------------------------------------------------
-- Code/SExpr.agda —— 通用的 s-expression 读取器
--
-- Dump.hs（以及以后别的文件类型的导出器）吐出来的都是这种东西：
--   原子：符号 vis、字符串 "x"、数字 3
--   列表：(tag 子项 …)
-- 这里只管把一串字符变成一棵 SExpr 树；它的意思由 Code/Parse.agda 这种"解码器"决定。
-- 分成两层的好处：以后每种文件类型只需要写自己的解码器，读取器共用。
------------------------------------------------------------------------
module Code.SExpr where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList; fromList)
open import Data.Char using (Char; toℕ; isSpace; isDigit)
open import Agda.Builtin.Char using (primCharEquality)

data SExpr : Set where
  sym  : String → SExpr
  str  : String → SExpr
  num  : ℕ → SExpr
  list : List SExpr → SExpr

------------------------------------------------------------------------
-- 词法
------------------------------------------------------------------------

data Token : Set where
  lp rp invalid : Token
  tsym  : String → Token
  tstr  : String → Token
  tnum  : ℕ → Token

private
  _==ᶜ_ : Char → Char → Bool
  _==ᶜ_ = primCharEquality

  delim : Char → Bool
  delim c = isSpace c ∨ (c ==ᶜ '(') ∨ (c ==ᶜ ')') ∨ (c ==ᶜ '"')

  digitVal : Char → ℕ
  digitVal c = toℕ c ∸ 48

  allDigits : List Char → Bool
  allDigits []       = true
  allDigits (c ∷ cs) = isDigit c ∧ allDigits cs

  toNum : List Char → ℕ
  toNum = go 0
    where
      go : ℕ → List Char → ℕ
      go acc []       = acc
      go acc (c ∷ cs) = go (acc * 10 + digitVal c) cs

  -- 字符串体：处理 \" \\ \n 三个转义。acc 是倒着存的。返回 (内容 , 剩下的字符)
  strBody : List Char → List Char → Maybe (List Char × List Char)
  strBody acc [] = nothing
  strBody acc ('\\' ∷ 'n' ∷ cs) = strBody ('\n' ∷ acc) cs
  strBody acc ('\\' ∷ 'r' ∷ cs) = strBody ('\r' ∷ acc) cs
  strBody acc ('\\' ∷ 't' ∷ cs) = strBody ('\t' ∷ acc) cs
  strBody acc ('\\' ∷ '\\' ∷ cs) = strBody ('\\' ∷ acc) cs
  strBody acc ('\\' ∷ '"' ∷ cs) = strBody ('"' ∷ acc) cs
  strBody acc ('\\' ∷ cs) = nothing
  strBody acc ('"' ∷ cs) = just (reverse acc , cs)
  strBody acc (c ∷ cs) = strBody (c ∷ acc) cs

  -- 符号体：到分隔符为止
  symBody : List Char → List Char → List Char × List Char
  symBody acc []       = reverse acc , []
  symBody acc (c ∷ cs) = if delim c then reverse acc , c ∷ cs else symBody (c ∷ acc) cs

  -- Fuel decreases once per consumed token or whitespace character.
  -- Keep pending tokens in reverse order so native evaluation is tail-recursive.
  lex : ℕ → List Char → List Token → List Token
  lex zero _ acc = reverse acc
  lex (suc n) [] acc = reverse acc
  lex (suc n) ('(' ∷ cs) acc = lex n cs (lp ∷ acc)
  lex (suc n) (')' ∷ cs) acc = lex n cs (rp ∷ acc)
  lex (suc n) ('"' ∷ cs) acc with strBody [] cs
  ... | nothing = invalid ∷ []
  ... | just (body , rest) = lex n rest (tstr (fromList body) ∷ acc)
  lex (suc n) (c ∷ cs) acc with isSpace c
  ... | true = lex n cs acc
  ... | false with symBody [] (c ∷ cs)
  ...   | body , rest = lex n rest ((if allDigits body then tnum (toNum body) else tsym (fromList body)) ∷ acc)

tokenize : String → List Token
tokenize s = let cs = toList s in lex (length cs) cs []

-- Each open parenthesis saves the preceding siblings. The root must contain
-- precisely one expression, and all lists must be closed.
private
  parseTokens : List Token → List SExpr → List (List SExpr) → Maybe SExpr
  parseTokens [] (x ∷ []) [] = just x
  parseTokens [] _ _ = nothing
  parseTokens (lp ∷ ts) xs parents = parseTokens ts [] (xs ∷ parents)
  parseTokens (rp ∷ ts) xs (p ∷ parents) = parseTokens ts (list (reverse xs) ∷ p) parents
  parseTokens (rp ∷ ts) xs [] = nothing
  parseTokens (tsym s ∷ ts) xs parents = parseTokens ts (sym s ∷ xs) parents
  parseTokens (tstr s ∷ ts) xs parents = parseTokens ts (str s ∷ xs) parents
  parseTokens (tnum n ∷ ts) xs parents = parseTokens ts (num n ∷ xs) parents
  parseTokens (invalid ∷ ts) _ _ = nothing

parseSExpr : String → Maybe SExpr
parseSExpr s = parseTokens (tokenize s) [] []

------------------------------------------------------------------------
-- 打印（调试用，也是 s-expr 的 render）
------------------------------------------------------------------------

open import Data.String using () renaming (_++_ to _++ˢ_)
import Data.Nat.Show as ℕshow

escape : String → String
escape s = fromList (go (toList s))
  where
    go : List Char → List Char
    go []          = []
    go ('"' ∷ cs)  = '\\' ∷ '"' ∷ go cs
    go ('\\' ∷ cs) = '\\' ∷ '\\' ∷ go cs
    go ('\n' ∷ cs) = '\\' ∷ 'n' ∷ go cs
    go ('\r' ∷ cs) = '\\' ∷ 'r' ∷ go cs
    go ('\t' ∷ cs) = '\\' ∷ 't' ∷ go cs
    go (c ∷ cs)    = c ∷ go cs

mutual
  showSExpr : SExpr → String
  showSExpr (sym s)   = s
  showSExpr (str s)   = "\"" ++ˢ escape s ++ˢ "\""
  showSExpr (num n)   = ℕshow.show n
  showSExpr (list xs) = "(" ++ˢ showList xs ++ˢ ")"

  showList : List SExpr → String
  showList []           = ""
  showList (x ∷ [])     = showSExpr x
  showList (x ∷ y ∷ ys) = showSExpr x ++ˢ " " ++ˢ showList (y ∷ ys)
