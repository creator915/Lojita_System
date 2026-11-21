------------------------------------------------------------------------
-- Dump.hs —— 用 Agda 自己的 parser + scope checker 把一个 .agda 文件导出成 s-expression
--
-- 这就是"现成的 parse"：我们不重写 Agda 的 parser，只把它的 abstract 语法树
-- 剥掉 Range / ScopeInfo / NameId / concrete 副本，打成结构化的 s-expr，
-- 由 agda 世界里的 Code/Parse.agda 读进 Code 类型。
--
-- 每个名字输出两份：full（规范路径，身份）和 shown（在这个文件的作用域里怎么写它，只给 render 用）。
--
-- 编译：ghc -O2 -threaded -package Agda Dump.hs -o dump      （Agda 2.6.3 的库）
-- 用法：./dump -i . -i /usr/share/agda-stdlib Foo.agda   > Foo.sexp
--
-- s-expr 的文法见 README_code.md §2。
------------------------------------------------------------------------
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE InterruptibleFFI #-}
{-# OPTIONS_GHC -Idump #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
module Main where

import qualified Control.Exception as E
import Control.Monad
import Control.Concurrent (myThreadId, throwTo, threadWaitRead)
import Control.Monad.Except (catchError)
import Data.Aeson (FromJSON(..), ToJSON(..), eitherDecodeStrict', encode, object, withObject, (.:), (.:?), (.!=), (.=))
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.IORef
import qualified Data.Map.Strict as Map
import qualified Data.Strict.Maybe as Strict
import qualified Data.Set as Set
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Builder as B
import Foreign.C.Error (throwErrnoIfMinus1Retry)
import Foreign.C.String (CString, withCString)
import Foreign.C.Types (CInt(..))
import Data.Time.Clock.POSIX (POSIXTime)
import Data.Void (absurd)
import Control.Monad.IO.Class
import Data.List (sortOn, intersperse, intercalate, isPrefixOf, isSuffixOf, nub)
import Data.Maybe
import qualified Data.Text as T
import System.Directory (canonicalizePath, makeAbsolute, removeFile)
import System.FilePath ((</>), addTrailingPathSeparator, takeDirectory)
import qualified System.Posix.Files as Posix
import System.Posix.IO (closeFd, fdToHandle, setFdOption, FdOption(NonBlockingRead))
import System.Posix.Signals (installHandler, Handler(Catch), sigTERM)
import System.Posix.Types (Fd(..), DeviceID, FileID, FileOffset)
import System.Environment
import System.Exit
import System.IO
import GHC.IO.Handle (hDuplicate, hDuplicateTo)

import Agda.Interaction.Library (getPrimitiveLibDir)
import qualified Agda.Interaction.Options.Lenses as Opt
import qualified Agda.Syntax.Parser as Parser
import qualified Agda.Syntax.Parser.Tokens as Tok
import qualified Agda.Syntax.TopLevelModuleName as TLN
import qualified Agda.TypeChecking.Monad as TC
import Agda.TypeChecking.Errors (prettyError, getAllWarnings, tcWarningsToError)
import Agda.TypeChecking.Warnings (WhichWarnings(ErrorWarnings))
import Agda.Interaction.Options
import Agda.Interaction.Imports (parseSource, Source(..), typeCheckMain, crModuleInfo, readInterface, pattern ScopeCheck)
import Agda.Interaction.FindFile (SourceFile(..), InterfaceFile, intFilePath, findFile, findInterfaceFile', checkModuleName)
import Agda.Utils.FileName (absolute, filePath)
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
import qualified Agda.Syntax.Scope.Base as Scope
import Agda.Syntax.Fixity
import Agda.Syntax.Position (noRange, mkRangeFile, rangeFile, rangeFileName)
import Agda.Utils.Pretty (prettyShow, Pretty)
import qualified Agda.Utils.List1 as List1

------------------------------------------------------------------------
-- s-expression
------------------------------------------------------------------------

data S = L [S] | Sym String | Str String | Num Integer

renderS :: S -> B.Builder
renderS (Sym s) = B.fromString s
renderS (Num n) = B.fromString (show n)
renderS (Str s) = "\"" <> B.fromString (concatMap esc s) <> "\""
  where esc '"'  = "\\\""
        esc '\\' = "\\\\"
        esc '\n' = "\\n"
        esc '\r' = "\\r"
        esc c    = [c]
renderS (L xs) = "(" <> mconcat (intersperse " " (map renderS xs)) <> ")"

renderTop :: S -> T.Text
renderTop = TL.toStrict . B.toLazyText . top
  where
    top (L (Sym "module" : nm : ps : ds)) =
      "(module " <> renderS nm <> " " <> renderS ps <> "\n" <>
      foldMap (\d -> "  " <> renderS d <> "\n") ds <> ")"
    top s = renderS s

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

-- Prefer the spelling already present on the abstract name. A qualified
-- occurrence can use the local alias of its defining module, such as B.tint
-- after "import Base as B". Validate the entire candidate set in this
-- occurrence's scope before choosing either spelling.
directSpelling :: Scope.ScopeInfo -> QName -> Set.Set QName -> Maybe C.QName
directSpelling sc q expected =
  let name = nameConcrete (qnameName q)
      bare = C.QName name
      resolves n = Set.fromList (map Scope.anameName (Scope.scopeLookup n sc)) == expected
      scopes = Scope._scopeModules sc
      enclosing = case Map.lookup (Scope._scopeCurrent sc) scopes of
        Nothing -> []
        Just s  -> s : mapMaybe (flip Map.lookup scopes) (Scope.scopeParents s)
      ancestor m = mnameToList m `isPrefixOf` mnameToList (qnameModule q)
      aliases s =
        [C.QName n | (_, ns) <- Scope.scopeNameSpaces s, (n, ms) <- Map.toList (Scope.nsModules ns),
                     any (ancestor . Scope.amodName) ms] ++
        [n | (n, m) <- Map.toList (Scope.scopeImports s), ancestor m]
  in if isNothing (lookup name (Scope._scopeLocals sc)) && resolves bare
     then Just bare
     else listToMaybe [n | s <- enclosing, alias <- aliases s, let n = C.qualify alias name, resolves n]

-- 在当前作用域里这个名字怎么写。算出来的东西经过匿名模块（_）就不可信，退回最后一段。
shownOfQ :: QName -> TCM String
shownOfQ q
  | anonymousPath = return (lastSeg f)            -- where 块 / 匿名模块里的名字：就用最后一段
  | otherwise = do
      sc <- TC.getScope
      c <- maybe (abstractToConcrete_ q) pure (directSpelling sc q (Set.singleton q))
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
  let cands = sortOn fullOfQ (List1.toList (unAmbQ a))
      here  = case cur of
        Just (m, _) -> filter (\q -> (fullOfM m ++ ".") `isPrefixOf` fullOfQ q) cands
        Nothing     -> []
      builtin = filter (\q -> "Agda.Builtin." `isPrefixOf` fullOfQ q) cands   -- 其次挑 builtin 的（[] 、_∷_ 这种）
  let primary = head (here ++ builtin ++ cands)
      full = fullOfQ primary
      alts = Set.toAscList (Set.delete full (Set.fromList (map fullOfQ cands)))
  sc <- TC.getScope
  -- Re-resolving the printed spelling must recover exactly the candidate
  -- set at this occurrence. Agda's normal pretty printer may shorten All.[]
  -- to [] even when that would introduce a new overload.
  let expected = Set.fromList cands
      resolves name = Set.fromList (map Scope.anameName (Scope.scopeLookup name sc)) == expected
      spellings = Scope.inverseScopeLookupName' Scope.AmbiguousAnything primary sc
  shown <- case maybe (filter resolves spellings) (:[]) (directSpelling sc primary expected) of
    c : _ -> pure (prettyShow c)
    [] -> shownOfQ primary
  return $ if null alts && shown == lastSeg full then Str full
           else L (sym "q" : Str full : Str shown : map Str alts)

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
  A.PatternSynDef q args p -> do
      pat <- patS (absurd <$> p)
      return [L [sym "patsyn", Str (localName q), L (map (Str . bindNameS . unArg) args), pat]]
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

-- Only immutable interfaces survive a request. The key includes the resolved
-- source path: a request-local module with the same name is never reused.
type FileStamp = (DeviceID, FileID, FileOffset, POSIXTime)
type LibraryVersion = (FileStamp, FileStamp)
data Worker = Worker [FilePath] (IORef (Map.Map FilePath (LibraryVersion, TC.ModuleInfo, [TLN.TopLevelModuleName]))) (IORef [CachedDump])

-- A reply cache contains wire text only. It cannot satisfy an Agda import.
-- Record every name-resolution edge plus the exact input text of every
-- source-scoped module, including implicit dependencies not present in deps.
data Input = Input TLN.TopLevelModuleName FilePath FilePath (Either LibraryVersion TL.Text)
data CachedDump = CachedDump [FilePath] [FilePath] [Input] Reply !Int
data Request = Request [FilePath] [FilePath] FilePath
data Reply = Success T.Text [T.Text] [String] | Failure String

data RPC = Dump Request | Headers [String]

instance FromJSON RPC where
  parseJSON = withObject "frontend request" $ \o -> do
    cmd <- o .: "cmd"
    case cmd :: String of
      "dump" -> Dump <$> (Request <$> o .:? "includes" .!= [] <*> o .:? "deps" .!= [] <*> o .: "main")
      "headers" -> Headers <$> o .: "sources"
      _ -> fail ("unknown frontend command " ++ cmd)

instance ToJSON Request where
  toJSON (Request incs deps mainFile) = object
    ["cmd" .= ("dump" :: String), "includes" .= incs, "deps" .= deps, "main" .= mainFile]

instance FromJSON Reply where
  parseJSON = withObject "dump reply" $ \o -> o .: "ok" >>= \case
    True  -> Success <$> o .: "sexpr" <*> o .: "dep_sexprs" <*> o .:? "check_errors" .!= []
    False -> Failure <$> o .: "error"

instance ToJSON Reply where
  toJSON (Success mainCode deps errors) = object
    ["ok" .= True, "sexpr" .= mainCode, "dep_sexprs" .= deps, "check_errors" .= errors]
  toJSON (Failure err) = object ["ok" .= False, "error" .= err]

newWorker :: IO Worker
newWorker = do
  exe <- getExecutablePath >>= canonicalizePath
  prim <- getPrimitiveLibDir
  roots <- mapM canonicalizePath [takeDirectory (takeDirectory exe) </> "Context", "/usr/share/agda-stdlib", prim]
  Worker (map addTrailingPathSeparator roots) <$> newIORef Map.empty <*> newIORef []

-- Agda's lexer recognizes imports everywhere, including private where/let
-- blocks, literate input, and comments between the keyword and module name.
importsOf :: Source -> TCM [TLN.TopLevelModuleName]
importsOf src = do
  let rf = mkRangeFile (srcFilePath (srcOrigin src)) (Just (srcModuleName src))
  (res, _) <- Parser.runPMIO $ Parser.parseFile Parser.tokensParser rf (TL.unpack (srcText src))
  ((tokens, _), _) <- either (TC.genericError . show) pure res
  mapM (TC.topLevelModuleName . TLN.RawTopLevelModuleName noRange . fmap T.pack)
    (importNames tokens)

importNames :: [Tok.Token] -> [List1.List1 String]
importNames = nub . names . filter relevant
  where
    relevant Tok.TokComment{} = False
    relevant Tok.TokMarkup{} = False
    relevant Tok.TokTeX{} = False
    relevant _ = True
    names (Tok.TokKeyword Tok.KwImport _ : Tok.TokId (_, n) : rest) = (n List1.:| []) : names rest
    names (Tok.TokKeyword Tok.KwImport _ : Tok.TokQId ((_, n):ns) : rest) =
      (n List1.:| map snd ns) : names rest
    names (_:rest) = names rest
    names [] = []

-- getInterface verifies in-memory decoded interfaces against .agdai hashes
-- unless the module is also *visited*. In particular, a disk-less scope-only
-- interface must be entered in both maps. Agda still performs its normal
-- infective/co-infective option checks on every visited import.
register :: TC.ModuleInfo -> TCM ()
register info = do
  TC.storeDecodedModule info
  TC.visitModule info
  let i = TC.miInterface info
  TC.modifyTCLens TC.stPatternSynImports (Map.union (TC.iPatternSyns i))
  let builtin (TC.Builtin t) = Just (TC.Builtin t)
      builtin (TC.BuiltinRewriteRelations qs) = Just (TC.BuiltinRewriteRelations qs)
      builtin TC.Prim{} = Nothing
  TC.modifyTCLens TC.stImportedBuiltins (Map.union (Map.mapMaybe builtin (TC.iBuiltin i)))

fileStamp :: FilePath -> IO FileStamp
fileStamp path = do
  st <- Posix.getFileStatus path
  return (Posix.deviceID st, Posix.fileID st, Posix.fileSize st, Posix.statusChangeTimeHiRes st)

libraryFile :: SourceFile -> TLN.TopLevelModuleName -> TCM (Maybe (InterfaceFile, LibraryVersion))
libraryFile file name = do
  let path = srcFilePath file
  -- The staged view's library controls the import's flags. Its empty
  -- options permit the installed interface, which lives next to the real
  -- immutable source rather than in the staging project's _build directory.
  options <- TC.getLibraryOptions path name
  real <- liftIO (canonicalizePath (filePath path) >>= absolute)
  if any (not . null) options then pure Nothing else findInterfaceFile' (SourceFile real) >>= \case
    Nothing -> pure Nothing
    Just iface -> do
      version <- liftIO $ (,) <$> fileStamp (filePath path) <*> fileStamp (filePath (intFilePath iface))
      return (Just (iface, version))

-- A public import can re-export another module's pattern synonym. Its name
-- lives in iScope here, but expansion uses iPatternSyns from its definition
-- site. Load just those defining interfaces before entering scope checking.
patternOwners :: TC.Interface -> [TLN.TopLevelModuleName]
patternOwners i = Set.toList $ Set.fromList
  [ owner
  | sc <- Map.elems (TC.iScope i), (_, ns) <- Scope.scopeNameSpaces sc
  , group <- Map.elems (Scope.nsNames ns), a <- group
  , Scope.anameKind a == Scope.PatternSynName
  , let q = Scope.anameName a
  , Map.notMember q (TC.iPatternSyns i)
  , Strict.Just rf <- [rangeFile (nameBindingSite (qnameName q))]
  , Just owner <- [rangeFileName rf]
  ]

loadLibrary :: Worker -> FilePath -> SourceFile -> TLN.TopLevelModuleName -> TCM (Maybe (LibraryVersion, [TLN.TopLevelModuleName]))
loadLibrary (Worker roots cache _) path file name
  | any (`isPrefixOf` path) roots = libraryFile file name >>= \case
    Nothing -> pure Nothing
    Just (ifile, version) -> do
      cached <- liftIO (Map.lookup path <$> readIORef cache)
      case cached of
        Just (was, info, owners) | was == version -> register info >> return (Just (version, owners))
        _ -> readInterface ifile >>= \case
          Just i | TC.iTopLevelModuleName i == name -> do
            let rf = mkRangeFile (srcFilePath file) (Just name)
            (source, _) <- Parser.runPMIO (Parser.readFilePM rf)
            if sourceMatches source i then do
              prim <- Opt.isPrimitiveModule path
              let info = TC.ModuleInfo i [] prim TC.ModuleTypeChecked
                  owners = patternOwners i
              liftIO $ modifyIORef' cache (Map.insert path (version, info, owners))
              register info
              return (Just (version, owners))
            else pure Nothing  -- edited Context source, interface predates the edit
          _ -> TC.genericError ("Invalid library interface for " ++ path)
  | otherwise = pure Nothing
  where
    sourceMatches (Right txt) i = txt == TC.iSource i && all null (TC.iDefaultPragmaOptions i)
    sourceMatches _ _ = False

sourcePragmas :: Source -> [S]
sourcePragmas src = map pragma (C.modPragmas (srcModule src))
  where
    pragma (C.OptionsPragma _ opts) = L [sym "pragma", Str (unwords ("OPTIONS" : opts))]
    pragma p = L [sym "pragma", Str (prettyShow p)]

codeFor :: Source -> TCM (T.Text, [String])
codeFor src = do
  let path = srcFilePath (srcOrigin src)
      name = srcModuleName src
      ds = C.modDecls (srcModule src)
  lib <- TC.getLibraryOptions path name
  mapM_ setOptionsFromPragma (lib ++ [opts | C.OptionsPragma _ opts <- C.modPragmas (srcModule src)])
  checkModuleName name (srcOrigin src) Nothing
  localTC (\e -> e { envCurrentPath = Just path }) $ do
    top <- concreteToAbstract_ (TopLevel path name ds)
    setTCLens stCurrentModule (Just (topLevelModuleName top, name))
    code <- withScope_ (topLevelScope top) $ topS (sourcePragmas src) (foreignS ds) (topLevelDecls top)
    errors <- getAllWarnings ErrorWarnings
    let wire = renderTop code
    wire `seq` return (wire, map (show . TC.tcWarningPrintedWarning) errors)

dumpBundle :: Worker -> [FilePath] -> Request -> TCM Reply
dumpBundle worker@(Worker _ _ replies) base (Request incs deps mainFile) = do
  let dirs = nub (incs ++ base)
  setCommandLineOptions defaultOptions { optIncludePaths = if null dirs then ["."] else dirs
                                       , optIgnoreInterfaces = True, optDefaultLibs = False }
  dirs' <- map filePath <$> TC.getIncludeDirs
  let args = deps ++ [mainFile]
  files <- liftIO $ mapM canonicalizePath args
  let key = args ++ files
  prior <- liftIO (readIORef replies)
  pristine <- TC.getTC
  let matching = [entry | entry@(CachedDump d a _ _ _) <- prior, d == dirs', a == key]
  fresh <- case matching of
    CachedDump _ _ inputs reply _ : _ -> do
      live <- validateInputs inputs `catchError` const (pure False)
      pure (if live then Just reply else Nothing)
    _ -> pure Nothing
  case fresh of
    Just reply -> pure reply
    Nothing -> do
      TC.putTC pristine
      inputs <- liftIO $ newIORef (Just Map.empty)
      let track name path actual content = liftIO $ modifyIORef' inputs (fmap (Map.insert name (Input name path actual content)))
          scoped path src = if null (srcProjectLibs src)
            then track (srcModuleName src) path (filePath (srcFilePath (srcOrigin src))) (Right (srcText src))
            else liftIO $ writeIORef inputs Nothing
      reply <- scopeBundle worker files args scoped track
      sources <- liftIO $ readIORef inputs
      case (sources, reply) of
        (Just m, Success mainCode depCodes errors) -> do
          let graph = Map.elems m
              -- Count bytes conservatively (four bytes per Unicode code point).
              weight = 4 * (sum (map length errors) + sum (map T.length (mainCode:depCodes)) +
                 sum [fromIntegral (TL.length txt) | Input _ _ _ (Right txt) <- graph])
              entry = CachedDump dirs' key graph reply weight
              keep n budget (e@(CachedDump _ _ _ _ w):es)
                | n > 0 && w <= budget = e : keep (n-1) (budget-w) es
              keep _ _ _ = []
          when (weight <= 32 * 1024 * 1024) $ liftIO $ modifyIORef' replies $ \entries -> keep (8 :: Int) (32 * 1024 * 1024)
            (entry : [e | e@(CachedDump d a _ _ _) <- entries, (d,a) /= (dirs',key)])
        _ -> pure ()
      pure reply

validateInputs :: [Input] -> TCM Bool
validateInputs [] = pure True
validateInputs (Input name previous actual source : rest) = do
  -- Agda searches the current include roots afresh. A new competing file,
  -- changed symlink or removed import invalidates the entire response.
  file <- findFile name
  let path = srcFilePath file
  real <- liftIO $ canonicalizePath (filePath path)
  if real /= previous then pure False else do
    same <- case source of
      Left version -> (== Just version) . fmap snd <$> libraryFile file name
      Right old -> do
        original <- liftIO (absolute actual)
        project <- TC.getAgdaLibFiles original name
        if not (null project) then pure False else do
          (txt, _) <- Parser.runPMIO $ Parser.readFilePM (mkRangeFile path (Just name))
          return $ either (const False) (== old) txt
    if same then validateInputs rest else pure False

scopeBundle :: Worker -> [FilePath] -> [FilePath] -> (FilePath -> Source -> TCM ()) ->
               (TLN.TopLevelModuleName -> FilePath -> FilePath -> Either LibraryVersion TL.Text -> TCM ()) -> TCM Reply
scopeBundle worker files args trackSource track = do
  let wanted = Set.fromList files
  outputs <- liftIO $ newIORef Map.empty
  let scope needsInterface active path file = do
        src <- parseSource file
        trackSource path src
        when (Set.member path active) $ TC.genericError ("Cyclic module dependency at " ++ path)
        imports <- importsOf src
        mapM_ (prepare (Set.insert path active)) imports
        -- Each module starts in the initial local scope, with precisely the
        -- already-prepared import interfaces and no predecessor's pragmas.
        initial <- TC.getTC
        -- A module visited through an import always needs a prepared interface,
        -- even when that module is also the nominated main of the bundle.
        when needsInterface $ do
          cr <- typeCheckMain ScopeCheck src
          let info = crModuleInfo cr
          tcWarningsToError (TC.miWarnings info)
          TC.putTC initial
          register info { TC.miMode = TC.ModuleTypeChecked }
        when (Set.member path wanted) $ do
          before <- TC.getTC
          c <- codeFor src
          liftIO $ modifyIORef' outputs (Map.insert path c)
          TC.putTC before
      prepare active name = do
        visited <- TC.getVisitedModule name
        when (isNothing visited) $ do
          child <- findFile name
          resolved <- liftIO $ canonicalizePath (filePath (srcFilePath child))
          cached <- if Set.member resolved wanted then pure Nothing else loadLibrary worker resolved child name
          case cached of
            Just (version, owners) -> do
              track name resolved (filePath (srcFilePath child)) (Left version)
              mapM_ (prepare active) owners
            Nothing -> scope True active resolved child
  -- Primitive sorts are implicit imports even in files without an import
  -- declaration. Make them available from the installed, read-only interfaces.
  primRoot <- liftIO getPrimitiveLibDir
  forM_ (Set.toList Opt.primitiveModules) $ \rel -> do
    path <- liftIO (absolute (primRoot </> rel))
    let file = SourceFile path
    src <- parseSource file
    loaded <- loadLibrary worker (filePath path) file (srcModuleName src)
    case loaded of
      Just (version, owners) -> do
        track (srcModuleName src) (filePath path) (filePath path) (Left version)
        mapM_ (prepare Set.empty) owners
      Nothing -> TC.genericError ("Missing primitive interface for " ++ rel)
  forM_ (zip files args) $ \(path, original) -> do
    done <- liftIO $ Map.member path <$> readIORef outputs
    unless done $ scope (path /= last files || path `elem` init files) Set.empty path . SourceFile =<< liftIO (absolute original)
  result <- liftIO (readIORef outputs)
  case reverse (map (result Map.!) files) of
    (mainCode, mainErrors) : reversedDeps -> do
      let deps = reverse reversedDeps
      pure $ Success mainCode (map fst deps) (concatMap snd deps ++ mainErrors)
    [] -> TC.genericError "missing main module"

runRequest :: Worker -> [FilePath] -> Request -> IO Reply
runRequest worker incs req = E.handle syncError $ do
  -- runTCMTop supplies a fresh TCState per request, even after a failing
  -- import. Mutable inputs survive solely as validated, bounded wire replies.
  result <- TC.runTCMTop $ dumpBundle worker incs req `catchError` (fmap Failure . prettyError)
  return $ either (Failure . show) id result
  where
    syncError (e :: E.SomeException) = case E.fromException e :: Maybe E.AsyncException of
      Just a -> E.throwIO a
      Nothing -> pure (Failure (E.displayException e))

-- A synthetic filename enables Agda's file/layout lexer without writing
-- user text to disk. Staging only needs the declared name and import closure.
headersReply :: [String] -> IO BL.ByteString
headersReply sources = do
  path <- absolute "Surface.agda"
  let rf = mkRangeFile path Nothing
      header source = do
        (parsed, _) <- Parser.runPMIO $ Parser.parseFile Parser.moduleParser rf source
        case parsed of
          Left err -> pure (Left (prettyShow err))
          Right ((m, _), _) -> do
            (lexed, _) <- Parser.runPMIO $ Parser.parseFile Parser.tokensParser rf source
            return $ do
              ((tokens, _), _) <- either (Left . prettyShow) Right lexed
              let name = TLN.rawTopLevelModuleNameToString (TLN.rawTopLevelModuleNameForModule m)
                  imports = map (intercalate "." . List1.toList) (importNames tokens)
              pure $ object ["name" .= name, "imports" .= imports]
  result <- sequence <$> mapM header sources
  return $ either (encode . Failure) (\hs -> encode (object ["ok" .= True, "headers" .= hs])) result

handleLine :: Worker -> [FilePath] -> Handle -> Handle -> IO ()
handleLine worker incs input wire = do
  line <- BS.hGetLine input
  reply <- case eitherDecodeStrict' line of
    Left err -> pure (encode (Failure err))
    Right (Dump req) -> encode <$> runRequest worker incs req
    Right (Headers sources) -> headersReply sources
  BL.hPutStrLn wire reply
  hFlush wire

serve :: Handle -> Worker -> [FilePath] -> IO ()
serve wire worker incs = loop
  where loop = hIsEOF stdin >>= \eof -> unless eof (handleLine worker incs stdin wire >> loop)

foreign import capi safe "dump_socket.h dump_unix_socket" unixSocket :: CString -> CInt -> IO CInt
foreign import capi interruptible "dump_socket.h dump_unix_accept" unixAccept :: CInt -> IO CInt

openSocket :: FilePath -> Bool -> IO Fd
openSocket path server = withCString path $ \cPath -> Fd <$> throwErrnoIfMinus1Retry path
  (unixSocket cPath (if server then 1 else 0))

serveSocket :: FilePath -> Worker -> [FilePath] -> IO ()
serveSocket path worker incs = E.bracket (openSocket path True)
  (\fd -> closeFd fd `E.finally` removeFile path) $ \(Fd socket) -> do
    tid <- myThreadId
    _ <- installHandler sigTERM (Catch (throwTo tid E.UserInterrupt)) Nothing
    setFdOption (Fd socket) NonBlockingRead True
    forever $ do
      threadWaitRead (Fd socket)
      E.bracket (fdToHandle . Fd =<< throwErrnoIfMinus1Retry "accept" (unixAccept socket)) hClose $ \conn ->
        handleLine worker incs conn conn `E.catch` \(_ :: IOError) -> pure ()

socketRequest :: FilePath -> Request -> IO Reply
socketRequest path req = E.bracket (openSocket path False >>= fdToHandle) hClose $ \conn -> do
  BL.hPutStrLn conn (encode req)
  hFlush conn
  either Failure id . eitherDecodeStrict' <$> BS.hGetLine conn

data CLI = CLI [FilePath] [FilePath] [FilePath] Bool (Maybe FilePath) (Maybe FilePath)

options :: [String] -> CLI
options = go (CLI [] [] [] False Nothing Nothing)
  where
    go opts [] = opts
    go (CLI i d f daemon socket client) args = case args of
      "-i":x:xs -> go (CLI (i ++ [x]) d f daemon socket client) xs
      "--dep":x:xs -> go (CLI i (d ++ [x]) f daemon socket client) xs
      "--daemon":xs -> go (CLI i d f True socket client) xs
      "--serve-socket":x:xs -> go (CLI i d f daemon (Just x) client) xs
      "--socket":x:xs -> go (CLI i d f daemon socket (Just x)) xs
      x:xs -> go (CLI i d (f ++ [x]) daemon socket client) xs

main :: IO ()
main = do
  args <- getArgs
  let complete = "--require-complete" `elem` args
      CLI incs deps files daemon server client = options (filter (/= "--require-complete") args)
  wire <- hDuplicate stdout
  hDuplicateTo stderr stdout
  case (server, daemon, files) of
    (Just path, _, []) -> newWorker >>= \worker -> serveSocket path worker incs
    (Nothing, True, []) -> newWorker >>= \worker -> serve wire worker incs
    (Nothing, False, [f]) -> do
      env <- lookupEnv "AGDA_DUMPD_SOCK"
      req <- Request <$> mapM makeAbsolute (if null incs then ["."] else incs) <*> mapM makeAbsolute deps <*> makeAbsolute f
      let standalone = newWorker >>= \w -> runRequest w [] req
      reply <- case (client, env) of
        (Just path, _) -> socketRequest path req
        (_, Just path) -> socketRequest path req `E.catch` \(_ :: IOError) -> standalone
        _ -> standalone
      case reply of
        Failure err -> hPutStrLn stderr err >> exitFailure
        Success _ _ errs | complete && not (null errs) -> die (unlines errs)
        Success code _ _ -> hPutStrLn wire (T.unpack code) >> hFlush wire
    _ -> die "usage: dump [--require-complete] [-i dir]... [--dep Dep.agda]... File.agda | --daemon | --serve-socket PATH"
