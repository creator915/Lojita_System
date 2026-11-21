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

  -- 燃料 = 剩余字符数，保证终止
  mutual
    lex : ℕ → List Char → List Token
    lex zero    _  = []
    lex (suc n) [] = []
    lex (suc n) (c ∷ cs) =
      if isSpace c then lex n cs
      else if c ==ᶜ '(' then lp ∷ lex n cs
      else if c ==ᶜ ')' then rp ∷ lex n cs
      else if c ==ᶜ '"' then quoted n (strBody [] cs)
      else (let r = symBody [] (c ∷ cs)
                body = proj₁ r
            in (if allDigits body then tnum (toNum body) else tsym (fromList body)) ∷ lex n (proj₂ r))

    quoted : ℕ → Maybe (List Char × List Char) → List Token
    quoted n nothing = invalid ∷ []
    quoted n (just (body , rest)) = tstr (fromList body) ∷ lex n rest

tokenize : String → List Token
tokenize s = let cs = toList s in lex (length cs) cs

------------------------------------------------------------------------
-- 语法：递归下降，燃料 = token 数
------------------------------------------------------------------------

private
  mutual
    -- 读一个 SExpr，返回它和剩下的 token
    one : ℕ → List Token → Maybe (SExpr × List Token)
    one zero    _               = nothing
    one (suc n) []              = nothing
    one (suc n) (tsym s ∷ ts)   = just (sym s , ts)
    one (suc n) (tstr s ∷ ts)   = just (str s , ts)
    one (suc n) (tnum k ∷ ts)   = just (num k , ts)
    one (suc n) (invalid ∷ ts) = nothing
    one (suc n) (rp ∷ ts)       = nothing
    one (suc n) (lp ∷ ts)       = many n ts []

    -- 读到右括号为止
    many : ℕ → List Token → List SExpr → Maybe (SExpr × List Token)
    many zero    _         acc = nothing
    many (suc n) []        acc = nothing
    many (suc n) (rp ∷ ts) acc = just (list (reverse acc) , ts)
    many (suc n) ts        acc with one n ts
    ... | nothing         = nothing
    ... | just (x , rest) = many n rest (x ∷ acc)

parseSExpr : String → Maybe SExpr
parseSExpr s with (let ts = tokenize s in one (suc (length ts)) ts)
... | just (x , []) = just x
... | _             = nothing

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
