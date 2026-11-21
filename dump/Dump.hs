------------------------------------------------------------------------
-- Dump.hs —— 用 Agda 自己的 parser + scope checker 把一个 .agda 文件导出成 s-expression
--
-- 这就是"现成的 parse"：我们不重写 Agda 的 parser，只把它的 abstract 语法树
-- 剥掉 Range / ScopeInfo / NameId / concrete 副本，打成结构化的 s-expr，
-- 由 agda 世界里的 Code/Parse.agda 读进 Code 类型。
--
-- 每个名字输出两份：full（规范路径，身份）和 shown（在这个文件的作用域里怎么写它，只给 render 用）。
--
-- 编译：ghc -O0 -package Agda Dump.hs -o dump      （Agda 2.6.3 的库）
-- 用法：./dump -i . -i /usr/share/agda-stdlib Foo.agda   > Foo.sexp
--
-- s-expr 的文法见 README_code.md §2。
------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
module Main where

import Control.Monad
import Control.Monad.IO.Class
import Data.List (intercalate, isPrefixOf, isSuffixOf)
import Data.Maybe
import qualified Data.Text as T
import System.Environment
import System.Exit
import System.IO
import GHC.IO.Handle (hDuplicate, hDuplicateTo)

import Agda.Main (runTCMPrettyErrors)
import Agda.Interaction.Options
import Agda.Interaction.Imports (parseSource, Source(..), typeCheckMain, pattern ScopeCheck)
import Agda.Interaction.FindFile (SourceFile(..))
import Agda.Utils.FileName (absolute)
import Agda.TypeChecking.Monad (TCM, TCEnv(..), localTC, withScope_, useTC, setTCLens, stCurrentModule, stScope)
import Agda.TypeChecking.Monad.Options (setCommandLineOptions, setOptionsFromPragma)
import Agda.Syntax.Translation.ConcreteToAbstract (concreteToAbstract_, TopLevel(..), TopLevelInfo(..), topLevelModuleName)
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_, RangeAndPragma(..))
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Common
import qualified Agda.Syntax.Info as I
import Agda.Syntax.Literal
import Agda.Syntax.Fixity
import Agda.Syntax.Position (noRange)
import Agda.Utils.Pretty (prettyShow, Pretty)
import qualified Agda.Utils.List1 as List1

------------------------------------------------------------------------
-- s-expression
------------------------------------------------------------------------

data S = L [S] | Sym String | Str String | Num Integer

renderS :: S -> String
renderS (Sym s) = s
renderS (Num n) = show n
renderS (Str s) = '"' : concatMap esc s ++ "\""
  where esc '"'  = "\\\""
        esc '\\' = "\\\\"
        esc '\n' = "\\n"
        esc '\r' = "\\r"
        esc c    = [c]
renderS (L xs) = "(" ++ unwords (map renderS xs) ++ ")"

-- 顶层每条声明一行，方便人看
renderTop :: S -> String
renderTop (L (Sym "module" : nm : ps : ds)) =
  "(module " ++ renderS nm ++ " " ++ renderS ps ++ "\n" ++ concatMap (\d -> "  " ++ renderS d ++ "\n") ds ++ ")"
renderTop s = renderS s

sym :: String -> S
sym = Sym

------------------------------------------------------------------------
-- 名字
------------------------------------------------------------------------

-- 规范路径：定义处的名字，一段一段用 . 连起来
canon :: Name -> String
canon = prettyShow . nameCanonical

fullOfQ :: QName -> String
fullOfQ q = intercalate "." (map canon (qnameToList0 q))

fullOfM :: ModuleName -> String
fullOfM m = intercalate "." (map canon (mnameToList m))

lastSeg :: String -> String
lastSeg s = case break (== '.') s of
  (a, [])    -> a
  (_, _ : r) -> lastSeg r

-- 在当前作用域里这个名字怎么写。算出来的东西经过匿名模块（_）就不可信，退回最后一段。
shownOfQ :: QName -> TCM String
shownOfQ q
  | anonymousPath = return (lastSeg f)            -- where 块 / 匿名模块里的名字：就用最后一段
  | otherwise = do
      c <- abstractToConcrete_ q
      let s = prettyShow c
      return $ if null s || "._." `isInfixOf'` ("." ++ s ++ ".") then lastSeg f else s
  where
    f = fullOfQ q
    anonymousPath = "._." `isInfixOf'` ("." ++ f ++ ".")
    isInfixOf' pat str = any (pat `isPrefixOf`) (suffixes str)
    suffixes [] = [[]]
    suffixes xs@(_ : r) = xs : suffixes r

qnameS :: QName -> TCM S
qnameS q = do
  let f = fullOfQ q
  s <- shownOfQ q
  return $ if s == lastSeg f then Str f else L [sym "q", Str f, Str s]

-- 有歧义的构造子名（AmbQ 里好几个候选，type check 才挑定）：优先挑本文件里的，没有就取第一个
ambS :: AmbiguousQName -> TCM S
ambS a = do
  cur <- useTC stCurrentModule
  let cands = List1.toList (unAmbQ a)
      here  = case cur of
        Just (m, _) -> filter (\q -> (fullOfM m ++ ".") `isPrefixOf` fullOfQ q) cands
        Nothing     -> []
      builtin = filter (\q -> "Agda.Builtin." `isPrefixOf` fullOfQ q) cands   -- 其次挑 builtin 的（[] 、_∷_ 这种）
  qnameS (head (here ++ builtin ++ cands))

-- 定义处的局部名字（模块路径是上下文给的）
localName :: QName -> String
localName = prettyShow . nameConcrete . qnameName

bindNameS :: A.BindName -> String
bindNameS (A.BindName n) = prettyShow (nameConcrete n)

------------------------------------------------------------------------
-- 包装
------------------------------------------------------------------------

hidingS :: Hiding -> S
hidingS NotHidden    = sym "vis"
hidingS Hidden       = sym "hid"
hidingS (Instance _) = sym "inst"

labelS :: Maybe NamedName -> S
labelS Nothing  = sym "_"
labelS (Just n) = Str (rangedThing (woThing n))

argS :: (a -> TCM S) -> NamedArg a -> TCM S
argS f a = do
  x <- f (namedArg a)
  return $ L [sym "arg", hidingS (getHiding a), labelS (nameOf (unArg a)), x]

modsS :: A.DefInfo -> S
modsS = modsS' []

-- 多带几个标记（终止检查的 pragma：它藏在 Mutual 的 MutualInfo 里，不在 DefInfo 里，由 declsS 剥 Mutual 时贴上来）
modsS' :: [S] -> A.DefInfo -> S
modsS' extra di = L $ sym "mods" : catMaybes
  [ case I.defAccess di   of PrivateAccess _ -> Just (sym "private");  _ -> Nothing
  , case I.defInstance di of InstanceDef _   -> Just (sym "instance"); _ -> Nothing
  , case I.defAbstract di of AbstractDef     -> Just (sym "abstract"); _ -> Nothing ] ++ extra

tcFlags :: I.MutualInfo -> [S]
tcFlags mi = case I.mutualTerminationCheck mi of
  NonTerminating -> [sym "nonterminating"]
  Terminating    -> [sym "terminating"]
  _              -> []

-- infixl 6 _+_ 这类：藏在 DefInfo 里，拿出来做成单独一条声明
fixityS :: String -> A.DefInfo -> [S]
fixityS n di = case fixityLevel fx of
    Unrelated -> []
    Related d -> [L [sym "fixity", assocS (fixityAssoc fx), Num (round d), Str n]]
  where fx = theFixity (I.defFixity di)
        assocS LeftAssoc  = sym "l"
        assocS RightAssoc = sym "r"
        assocS NonAssoc   = sym "n"

litS :: Literal -> S
litS (LitNat n)    = L [sym "nat", Num n]
litS (LitString t) = L [sym "str", Str (T.unpack t)]
litS (LitChar c)   = L [sym "chr", Str [c]]
litS (LitWord64 w) = L [sym "nat", Num (fromIntegral w)]
litS (LitFloat d)  = L [sym "str", Str (show d)]          -- 这版不认 float：记成字符串，render 时看得见
litS (LitQName q)  = L [sym "str", Str (fullOfQ q)]
litS (LitMeta _ _) = L [sym "str", Str "?meta"]

-- using / hiding 列表里的名字：按当前作用域里的写法（ℕ 而不是定义处的 Nat），只留最后一段
importedS :: ImportedName' QName ModuleName -> TCM String
importedS (ImportedName q)   = lastSeg <$> shownOfQ q
importedS (ImportedModule m) = return (lastSeg (fullOfM m))

-- 只拿名字本身（renaming 的 to 那一侧：新名字就是它的 concrete 名）
importedPlain :: ImportedName' QName ModuleName -> String
importedPlain (ImportedName q)   = localName q
importedPlain (ImportedModule m) = lastSeg (fullOfM m)

-- 用户写的 directive（concrete）还留在 ModuleInfo 里：有就用它，名字就是用户写的样子
cdirectiveS :: C.ImportDirective -> S
cdirectiveS d = L
  [ sym "dir"
  , case using d of
      UseEverything -> sym "everything"
      Using xs      -> L (sym "using" : map (Str . cimp) xs)
  , L (sym "hiding" : map (Str . cimp) (hiding d))
  , L (sym "renaming" : [ L [Str (cimp (renFrom r)), Str (cimp (renTo r))] | r <- impRenaming d ])
  , if isJust (publicOpen d) then sym "public" else sym "private" ]
  where
    cimp :: (Pretty n, Pretty m) => ImportedName' n m -> String
    cimp (ImportedName n)   = prettyShow n
    cimp (ImportedModule m) = prettyShow m

-- 没有 concrete 的时候从 abstract 的 directive 重建（名字按当前作用域）
directiveS :: A.ImportDirective -> TCM S
directiveS d = do
  us <- case using d of
      UseEverything -> return (sym "everything")
      Using xs      -> L . (sym "using" :) . map Str <$> mapM importedS xs
  hs <- mapM importedS (hiding d)
  rs <- forM (impRenaming d) $ \r -> do
      from <- importedS (renFrom r)
      return $ L [Str from, Str (importedPlain (renTo r))]
  return $ L
    [ sym "dir", us
    , L (sym "hiding" : map Str hs)
    , L (sym "renaming" : rs)
    , if isJust (publicOpen d) then sym "public" else sym "private" ]

------------------------------------------------------------------------
-- 表达式
------------------------------------------------------------------------

isSet :: QName -> Bool
isSet q = fullOfQ q == "Agda.Primitive.Set"

exprS :: A.Expr -> TCM S
exprS = \case
  A.Var n              -> return $ L [sym "var", Str (prettyShow (nameConcrete n))]
  A.Def' q suf
    | isSet q          -> return $ L [sym "set", Num (case suf of NoSuffix -> 0; Suffix k -> k)]
    | otherwise        -> (\x -> L [sym "def", x]) <$> qnameS q
  A.Proj _ a           -> (\x -> L [sym "def", x]) <$> ambS a
  A.Con a              -> (\x -> L [sym "con", x]) <$> ambS a
  A.PatternSyn a       -> (\x -> L [sym "def", x]) <$> ambS a
  A.Macro q            -> (\x -> L [sym "def", x]) <$> qnameS q
  A.Lit _ l            -> return $ L [sym "lit", litS l]
  A.QuestionMark _ _   -> return $ sym "hole"
  A.Underscore _       -> return $ sym "meta"
  A.Dot _ e            -> (\x -> L [sym "dot", x]) <$> exprS e
  A.App _ f a          -> do f' <- exprS f; a' <- argS exprS a; return $ L [sym "app", f', a']
  A.WithApp _ e es     -> exprS e                                   -- 只在 with 里出现，with 自己有结构
  A.Lam _ (A.DomainFree _ b) e -> do
      let bn = A.binderName (namedArg b)
      e' <- exprS e
      case nameOf (unArg b) of
        Nothing -> return $ L [sym "lamT", L [sym "bind", hidingS (getHiding b), L [Str (bindNameS bn)], sym "meta"], e']
        Just _  -> return $ L [sym "lam", L [sym "arg", hidingS (getHiding b), labelS (nameOf (unArg b)), Str (bindNameS bn)], e']
  A.Lam _ (A.DomainFull tb) e -> do
      bs <- typedBindingS tb
      e' <- exprS e
      return $ foldr (\b acc -> L [sym "lamT", b, acc]) e' bs
  A.AbsurdLam _ h      -> return $ L [sym "absurdlam", hidingS h]
  A.ExtendedLam _ _ _ _ cs -> (\xs -> L (sym "lamcase" : xs)) <$> mapM clauseS (List1.toList cs)
  A.Pi _ tel t         -> do
      bs <- concat <$> mapM typedBindingS (List1.toList tel)
      t' <- exprS t
      return $ foldr (\b acc -> L [sym "pi", b, acc]) t' bs
  A.Generalized _ t    -> exprS t
  A.Fun _ a b          -> do
      a' <- exprS (unArg a)
      b' <- exprS b
      return $ L [sym "fun", L [sym "arg", hidingS (getHiding a), sym "_", a'], b']
  A.Let _ bs e         -> do
      bs' <- catMaybes <$> mapM letBindS (List1.toList bs)
      e' <- exprS e
      return $ L [sym "let", L bs', e']
  A.Rec _ as           -> (\fs -> L [sym "rec", L fs]) <$> recAssignsS as
  A.RecUpdate _ e as   -> do e' <- exprS e; fs <- mapM fieldAssignS as; return $ L [sym "recupd", e', L fs]
  A.ScopedExpr sc e    -> withScope_ sc (exprS e)
  A.Quote _            -> return $ sym "meta"
  A.QuoteTerm _        -> return $ sym "meta"
  A.Unquote _          -> return $ sym "meta"
  A.DontCare e         -> exprS e

recAssignsS :: A.RecordAssigns -> TCM [S]
recAssignsS = fmap catMaybes . mapM go
  where go (Left fa) = Just <$> fieldAssignS fa
        go (Right _) = return Nothing                                 -- record { …; M }：模块赋值，这版不认

fieldAssignS :: C.FieldAssignment' A.Expr -> TCM S
fieldAssignS (C.FieldAssignment n e) = do
  e' <- exprS e
  return $ L [sym "fld", Str (prettyShow n), e']

-- 一组绑定 (x y : A)。TLet 不认。
typedBindingS :: A.TypedBinding -> TCM [S]
typedBindingS (A.TBind _ _ bs t) = do
  t' <- exprS t
  let xs = List1.toList bs
      h  = case xs of (b : _) -> getHiding b; [] -> NotHidden
      names = [ Str (bindNameS (A.binderName (namedArg b))) | b <- xs ]
  return [L [sym "bind", hidingS h, L names, t']]
typedBindingS (A.TLet _ _) = return []

letBindS :: A.LetBinding -> TCM (Maybe S)
letBindS = \case
  A.LetBind _ _ n t e -> do t' <- exprS t; e' <- exprS e; return $ Just (L [sym "letbind", Str (bindNameS n), t', e'])
  A.LetPatBind _ p e  -> do p' <- patS p; e' <- exprS e; return $ Just (L [sym "letpat", p', e'])
  A.LetApply{}        -> return Nothing
  A.LetOpen{}         -> return Nothing
  A.LetDeclaredVariable _ -> return Nothing

------------------------------------------------------------------------
-- 模式与子句
------------------------------------------------------------------------

patS :: A.Pattern -> TCM S
patS = \case
  A.VarP n           -> return $ L [sym "varp", Str (bindNameS n)]
  A.ConP _ a ps      -> do a' <- ambS a; ps' <- mapM (argS patS) ps; return $ L (sym "conp" : a' : ps')
  A.ProjP _ _ a      -> (\x -> L [sym "projp", x]) <$> ambS a
  A.DefP _ a ps      -> do a' <- ambS a; ps' <- mapM (argS patS) ps; return $ L (sym "conp" : a' : ps')
  A.WildP _          -> return $ sym "wildp"
  A.AsP _ n p        -> (\p' -> L [sym "asp", Str (bindNameS n), p']) <$> patS p
  A.DotP _ e         -> (\e' -> L [sym "dotp", e']) <$> exprS e
  A.AbsurdP _        -> return $ sym "absurdp"
  A.LitP _ l         -> return $ L [sym "litp", litS l]
  A.PatternSynP _ a ps -> do a' <- ambS a; ps' <- mapM (argS patS) ps; return $ L (sym "conp" : a' : ps')
  A.RecP _ fs        -> do
      fs' <- forM fs $ \(C.FieldAssignment n p) -> do p' <- patS p; return $ L [sym "fld", Str (prettyShow n), p']
      return $ L [sym "recp", L fs']
  A.EqualP _ _       -> return $ sym "wildp"
  A.WithP _ p        -> patS p
  A.AnnP _ _ p       -> patS p

lhsS :: A.LHS -> TCM S
lhsS (A.LHS _ core) = coreS core

coreS :: A.LHSCore -> TCM S
coreS = \case
  A.LHSHead f ps      -> do f' <- qnameS f; ps' <- mapM (argS patS) ps; return $ L (sym "head" : f' : ps')
  A.LHSProj d c ps    -> do
      d' <- ambS d
      c' <- coreS (namedArg c)
      ps' <- mapM (argS patS) ps
      return $ L (sym "proj" : d' : c' : ps')
  A.LHSWith c ws ps   -> do
      c'  <- coreS c
      ws' <- forM ws $ \w -> do p <- patS (unArg w); return $ L [sym "arg", hidingS (getHiding w), sym "_", p]
      ps' <- mapM (argS patS) ps
      return $ L [sym "with", c', L ws', L ps']

rhsS :: A.RHS -> TCM S
rhsS = \case
  A.RHS e _          -> (\e' -> L [sym "rhs", e']) <$> exprS e
  A.AbsurdRHS        -> return $ sym "absurdrhs"
  A.WithRHS _ es cs  -> do
      es' <- mapM (exprS . unArg . namedThing) es
      cs' <- mapM clauseS cs
      return $ L [sym "withrhs", L es', L cs']
  A.RewriteRHS eqs _ r _ -> do
      es' <- concat <$> mapM rewriteEqnS eqs
      r'  <- rhsS r
      return $ L [sym "rewriterhs", L es', r']
  where
    rewriteEqnS (Rewrite xs) = mapM (exprS . snd) (List1.toList xs)
    rewriteEqnS (Invert _ _) = return []

clauseS :: A.Clause -> TCM S
clauseS (A.Clause lhs _ rhs wh _) = do
  l <- lhsS lhs
  r <- rhsS rhs
  w <- whereS wh
  return $ L [sym "clause", l, r, L (sym "where" : w)]

-- where 块：匿名的直接给里面的声明；命名的（f x = e module M where …）包成一个 module
whereS :: A.WhereDeclarations -> TCM [S]
whereS (A.WhereDecls _ _ Nothing) = return []
whereS (A.WhereDecls _ _ (Just d)) = case d of
  A.Section _ m _ ds
    | isAnonymousModuleName m -> declsS ds
    | otherwise -> do inner <- declsS ds
                      return [L (sym "module" : Str (lastSeg (fullOfM m)) : L [sym "params"] : inner)]
  _ -> declsS [d]

------------------------------------------------------------------------
-- 声明
------------------------------------------------------------------------

-- DataDefParams 里的参数名
paramNames :: A.DataDefParams -> [S]
paramNames (A.DataDefParams _ lbs) = concatMap go lbs
  where
    go (A.DomainFree _ b)                = [Str (bindNameS (A.binderName (namedArg b)))]
    go (A.DomainFull (A.TBind _ _ bs _)) = [Str (bindNameS (A.binderName (namedArg b))) | b <- List1.toList bs]
    go (A.DomainFull (A.TLet _ _))       = []

telS :: A.GeneralizeTelescope -> TCM S
telS (A.GeneralizeTel _ tel) = (\bs -> L (sym "params" : bs)) . concat <$> mapM typedBindingS tel

-- 构造子 / 字段：都是 Axiom / Field
conS :: A.Declaration -> TCM [S]
conS = \case
  A.Axiom _ di _ _ q t -> do t' <- exprS t; return $ L [sym "con", Str (localName q), t'] : fixityS (localName q) di
  A.Field di q t       -> do t' <- exprS (unArg t); return $ L [sym "field", Str (localName q), t'] : fixityS (localName q) di
  A.ScopedDecl sc ds   -> withScope_ sc (concat <$> mapM conS ds)
  A.Mutual _ ds        -> concat <$> mapM conS ds
  _                    -> return []

pragmaS :: A.Pragma -> TCM S
pragmaS p = do
  c <- abstractToConcrete_ (RangeAndPragma noRange p)
  let s = prettyShow c
      s1 = if "{-#" `isPrefixOf` s then drop 3 s else s
      s2 = if "#-}" `isSuffixOf` s1 then take (length s1 - 3) s1 else s1
  return $ L [sym "pragma", Str (trim s2)]
  where trim = reverse . dropWhile (== ' ') . reverse . dropWhile (== ' ')

-- Mutual 这层包装剥掉（它不是结构）；ScopedDecl 不剥：它带的作用域正是"这里面的名字该怎么写"，
-- 翻译它里面的东西时切到那个作用域（where 块里 import … as 的别名就靠这个）
declsS :: [A.Declaration] -> TCM [S]
declsS = declsSWith []

-- fl：从外层 Mutual 继承下来的标记（终止检查）。Mutual 里面的 sig / fun 还套着 ScopedDecl，所以要一路带下去
declsSWith :: [S] -> [A.Declaration] -> TCM [S]
declsSWith fl0 = declsS' . flattenDecls fl0
  where
    -- 剥 Mutual 的时候把它的终止检查标记记下来，贴到里面每个 sig / fun 上
    flattenDecls fl = concatMap $ \case
      A.Mutual mi xs    -> flattenDecls (fl ++ tcFlags mi) xs
      d                 -> [(fl, d)]

declsS' :: [([S], A.Declaration)] -> TCM [S]
declsS' [] = return []
-- 连续的 variable 声明合成一块
declsS' ds@((_, A.Generalize{}) : _) = do
  let (gs, rest) = span (isGen . snd) ds
  vs <- forM gs $ \case
    (_, A.Generalize _ _ _ q t) -> do t' <- exprS t; return $ L [sym "var", Str (localName q), t']
    _ -> return (sym "_")
  rest' <- declsS' rest
  return $ L (sym "variable" : vs) : rest'
  where isGen A.Generalize{} = True
        isGen _ = False
declsS' ((fl, d) : ds) = do
  x  <- declS fl d
  xs <- declsS' ds
  return (x ++ xs)

declS :: [S] -> A.Declaration -> TCM [S]
declS fl = \case
  A.Axiom _ di _ _ q t      -> do t' <- exprS t
                                  return $ fixityS (localName q) di ++ [L [sym "sig", modsS' fl di, Str (localName q), t']]
  A.Generalize _ di _ q t   -> do t' <- exprS t; return [L [sym "variable", L [sym "var", Str (localName q), t']]]
  A.Field di q t            -> do t' <- exprS (unArg t); return [L [sym "sig", modsS di, Str (localName q), t']]
  A.Primitive di q t        -> do t' <- exprS (unArg t); return [L [sym "sig", modsS di, Str (localName q), t']]
  A.Mutual mi ds            -> declsSWith (fl ++ tcFlags mi) ds
  A.Section _ m tel ds      -> do
      tel' <- telS tel
      ds'  <- declsS ds
      return [L (sym "module" : Str (lastSeg (fullOfM m)) : tel' : ds')]
  A.Apply _ m _ _ _         -> return [L [sym "unsupported", Str ("module application " ++ fullOfM m)]]
  A.Import mi m dir
    | isImplicitPrimitive m dir -> return []      -- scope checker 自己加的 open import Agda.Primitive using (Set; Prop)
    | otherwise -> do
      -- as 名：有就记下（2.6.3 里 minfoAsName 只在真写了 as 时才有；别再按"等于最后一段"过滤——
      -- open import Data.Char as Char 的 as 就等于最后一段，丢了它 Char.≟ 就没法解析）
      let asName = case I.minfoAsName mi of
            Just n -> Just (prettyShow n)
            _ -> Nothing
          shown = fromMaybe (fullOfM m) asName
          nm    = L [sym "q", Str (fullOfM m), Str shown]       -- 模块名总写成 (q full shown)：shown = full 表示没有 as
          op    = case I.minfoOpenShort mi of Just C.DoOpen -> sym "open"; _ -> sym "noopen"
      dir' <- maybe (directiveS dir) (return . cdirectiveS) (I.minfoDirective mi)
      return [L [sym "import", nm, op, dir', L [sym "assumes"]]]
  A.Pragma _ p              -> (: []) <$> pragmaS p
  A.Open mi m dir           -> do
      dir' <- maybe (directiveS dir) (return . cdirectiveS) (I.minfoDirective mi)
      return [L [sym "open", Str (fullOfM m), dir']]
  A.FunDef di q _ cs        -> do cs' <- mapM clauseS cs; return [L (sym "fun" : modsS' fl di : Str (localName q) : cs')]
  A.DataSig di q tel t      -> do
      tel' <- telS tel; t' <- exprS t
      return $ fixityS (localName q) di ++ [L [sym "datasig", modsS di, Str (localName q), tel', t']]
  A.DataDef di q _ ps cs    -> do
      cs' <- concat <$> mapM conS cs
      return [L (sym "datadef" : modsS di : Str (localName q) : L (paramNames ps) : cs')]
  A.RecSig di q tel t       -> do
      tel' <- telS tel; t' <- exprS t
      return $ fixityS (localName q) di ++ [L [sym "recsig", modsS di, Str (localName q), tel', t']]
  A.RecDef di q _ dirs ps _ ds -> do
      fs <- concat <$> mapM conS ds
      let RecordDirectives ind _ _ con = dirs
          coind = case fmap rangedThing ind of Just CoInductive -> sym "coinductive"; _ -> sym "inductive"
          conS' = maybe (sym "_") (Str . localName) con
      return [L (sym "recdef" : modsS di : Str (localName q) : L (paramNames ps) : L [sym "recdir", coind, conS'] : fs)]
  A.PatternSynDef q _ _     -> return [L [sym "unsupported", Str ("pattern synonym " ++ localName q)]]
  A.UnquoteDecl{}           -> return [L [sym "unsupported", Str "unquoteDecl"]]
  A.UnquoteDef{}            -> return [L [sym "unsupported", Str "unquoteDef"]]
  A.UnquoteData{}           -> return [L [sym "unsupported", Str "unquoteData"]]
  A.ScopedDecl sc ds        -> withScope_ sc (declsSWith fl ds)

isImplicitPrimitive :: ModuleName -> A.ImportDirective -> Bool
isImplicitPrimitive m dir = fullOfM m == "Agda.Primitive" && case using dir of
  Using xs -> map importedPlain xs == ["Set", "Prop"]
  _        -> False

------------------------------------------------------------------------
-- 顶层：文件 = 模块外面的几条（pragma）+ 一个 Section
------------------------------------------------------------------------

-- FOREIGN pragma 在 2.6.3 的 abstract 里不存在（scope checker 直接记进状态了），从 concrete 那边捞出来，
-- 放在模块体最前面（COMPILE 要用到它们，它们在前面总是对的）
foreignS :: [C.Declaration] -> [S]
foreignS = concatMap go
  where
    go (C.Pragma (C.ForeignPragma _ backend code)) =
      [L [sym "pragma", Str ("FOREIGN " ++ rangedThing backend ++ "\n" ++ code)]]
    go (C.Module _ _ _ ds) = foreignS ds
    go _ = []

topS :: [S] -> [S] -> [A.Declaration] -> TCM S
topS pragmas foreigns ds = do
  let (outside, sections) = span (not . isSection) (flatten ds)
  case sections of
    [A.Section _ m tel inner] -> do
      out  <- declsS outside
      tel' <- telS tel
      body <- declsS inner
      return $ L (sym "module" : Str (fullOfM m) : tel' : (pragmas ++ out ++ foreigns ++ body))
    _ -> do
      body <- declsS ds
      return $ L (sym "module" : Str "?" : L [sym "params"] : (pragmas ++ foreigns ++ body))
  where
    isSection A.Section{} = True
    isSection _ = False
    flatten = concatMap $ \case
      A.ScopedDecl _ xs -> flatten xs
      d -> [d]

------------------------------------------------------------------------
-- main
------------------------------------------------------------------------

main :: IO ()
main = do
  -- Agda reports dependency checks on stdout. Keep the wire stream exclusively
  -- S-expressions and send every compiler diagnostic to stderr instead.
  wire <- hDuplicate stdout
  hDuplicateTo stderr stdout
  args <- getArgs
  let (incs, files) = go args
      go ("-i" : d : rest) = let (is, fs) = go rest in (d : is, fs)
      go (f : rest)        = let (is, fs) = go rest in (is, f : fs)
      go []                = ([], [])
  case files of
    [f] -> runTCMPrettyErrors $ do
      setCommandLineOptions defaultOptions { optIncludePaths = if null incs then ["."] else incs
                                           , optDefaultLibs  = False }
      path <- liftIO (absolute f)
      src  <- parseSource (SourceFile path)
      -- Use Agda's public entry point to initialize primitive builtins before
      -- chasing imports. Direct scope translation alone leaves IONE unbound
      -- when an imported module must be rechecked instead of using its cache.
      -- ScopeCheck deliberately permits specification-only top-level code.
      initialScope <- useTC stScope
      void $ typeCheckMain ScopeCheck src
      setTCLens stScope initialScope
      setTCLens stCurrentModule Nothing
      -- 文件自己的 OPTIONS：infective flag 不设好，import 带 --guardedness 的模块会被拒
      -- 模块前面的 pragma（{-# OPTIONS … #-}）不在声明列表里，单独拿
      pragmas <- forM (C.modPragmas (srcModule src)) $ \case
        C.OptionsPragma _ opts -> do setOptionsFromPragma opts
                                     return $ L [sym "pragma", Str (unwords ("OPTIONS" : opts))]
        p -> return $ L [sym "pragma", Str (prettyShow p)]
      localTC (\e -> e { envCurrentPath = Just path }) $ do
        top <- concreteToAbstract_ (TopLevel path (srcModuleName src) (C.modDecls (srcModule src)))
        setTCLens stCurrentModule (Just (topLevelModuleName top, srcModuleName src))
        s   <- withScope_ (topLevelScope top) $ topS pragmas (foreignS (C.modDecls (srcModule src))) (topLevelDecls top)
        liftIO $ hPutStrLn wire (renderTop s) >> hFlush wire
    _ -> do
      hPutStrLn stderr "usage: dump [-i dir]... File.agda"
      exitFailure
