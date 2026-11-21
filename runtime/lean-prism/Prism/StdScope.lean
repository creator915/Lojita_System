import Prism.Outcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.StdScope`: Closed Whitelist Symbol Table (Bit-for-Bit Canonical `Dump.hs` Paths + `AgdaMirror` Targets)
-/

namespace Prism

private def mkSym (loc : String) (canon : String) (k : SymKind) (lean : String)
    (fx : FixLevel := defaultAgdaFixity) (ar : Nat := 0) : SymInfo :=
  { localName := loc
  , canonPath := canon.splitOn "."
  , kind      := k
  , fixity    := fx
  , leanName  := lean
  , conArity  := ar }

def builtinNatExports : List SymInfo :=
  [ mkSym "Nat"   "Agda.Builtin.Nat.Nat"   .typeSym "Nat"
  , mkSym "zero"  "Agda.Builtin.Nat.Nat.zero" .conSym "Nat.zero" .unrelated 0
  , mkSym "suc"   "Agda.Builtin.Nat.Nat.suc"  .conSym "Nat.succ" .unrelated 1
  , mkSym "_+_"   "Agda.Builtin.Nat._+_"   .defSym  "AgdaMirror.agdaAdd"   (.related 6 .infixL)
  , mkSym "_-_"   "Agda.Builtin.Nat._-_"   .defSym  "AgdaMirror.agdaSub"   (.related 6 .infixL)
  , mkSym "_*_"   "Agda.Builtin.Nat._*_"   .defSym  "AgdaMirror.agdaMul"   (.related 7 .infixL)
  , mkSym "_==_"       "Agda.Builtin.Nat._==_"       .defSym  "AgdaMirror.agdaNatEq"     (.related 4 .infixN)
  , mkSym "_<_"        "Agda.Builtin.Nat._<_"        .defSym  "AgdaMirror.agdaNatLt"     (.related 4 .infixN)
  , mkSym "div-helper" "Agda.Builtin.Nat.div-helper" .defSym  "AgdaMirror.agdaDivHelper"
  , mkSym "mod-helper" "Agda.Builtin.Nat.mod-helper" .defSym  "AgdaMirror.agdaModHelper"
  ]

def dataNatExports : List SymInfo :=
  [ mkSym "ℕ"     "Agda.Builtin.Nat.Nat"      .typeSym "Nat"
  , mkSym "zero"  "Agda.Builtin.Nat.Nat.zero" .conSym  "Nat.zero" .unrelated 0
  , mkSym "suc"   "Agda.Builtin.Nat.Nat.suc"  .conSym  "Nat.succ" .unrelated 1
  , mkSym "pred"  "Data.Nat.Base.pred"        .defSym  "AgdaMirror.agdaPred"
  , mkSym "_+_"   "Agda.Builtin.Nat._+_"      .defSym  "AgdaMirror.agdaAdd"   (.related 6 .infixL)
  , mkSym "_∸_"   "Agda.Builtin.Nat._-_"      .defSym  "AgdaMirror.agdaSub"   (.related 6 .infixL)
  , mkSym "_*_"   "Agda.Builtin.Nat._*_"      .defSym  "AgdaMirror.agdaMul"   (.related 7 .infixL)
  , mkSym "_≡ᵇ_"  "Agda.Builtin.Nat._==_"     .defSym  "AgdaMirror.agdaNatEq" (.related 4 .infixN)
  , mkSym "_<ᵇ_"  "Agda.Builtin.Nat._<_"      .defSym  "AgdaMirror.agdaNatLt" (.related 4 .infixN)
  , mkSym "_≤ᵇ_"  "Data.Nat.Base._≤ᵇ_"        .defSym  "AgdaMirror.agdaNatLe" (.related 4 .infixN)
  , mkSym "_≟_"   "Data.Nat.Properties._≟_"   .defSym  "AgdaMirror.agdaNatDecEq" (.related 4 .infixN)
  , mkSym "_≤?_"  "Data.Nat.Properties._≤?_"  .defSym  "AgdaMirror.agdaNatLeDec" (.related 4 .infixN)
  , mkSym "_≤_"   "Data.Nat.Base._≤_"         .typeSym "AgdaMirror.AgdaNatLeRel" (.related 4 .infixN)
  , mkSym "z≤n"   "Data.Nat.Base._≤_.z≤n"     .conSym  "AgdaMirror.AgdaNatLeRel.zLeN" .unrelated 0
  , mkSym "s≤s"   "Data.Nat.Base._≤_.s≤s"     .conSym  "AgdaMirror.AgdaNatLeRel.sLeS" .unrelated 1
  , mkSym "_<_"   "Data.Nat.Base._<_"         .typeSym "AgdaMirror.AgdaNatLtRel" (.related 4 .infixN)
  , mkSym "_⊓_"   "Data.Nat.Base._⊓_"         .defSym  "AgdaMirror.agdaMin"   (.related 7 .infixL)
  , mkSym "_⊔_"   "Data.Nat.Base._⊔_"         .defSym  "AgdaMirror.agdaMax"   (.related 6 .infixL)
  ]

def dataNatPropsExports : List SymInfo :=
  [ mkSym "_≟_"    "Data.Nat.Properties._≟_"    .defSym "AgdaMirror.agdaNatDecEq" (.related 4 .infixN)
  , mkSym "≡ᵇ⇒≡"        "Data.Nat.Properties.≡ᵇ⇒≡"        .defSym "AgdaMirror.agdaNatEqbToEq"
  , mkSym "+-identityʳ" "Data.Nat.Properties.+-identityʳ" .defSym "AgdaMirror.agdaAddIdentityR"
  , mkSym "+-assoc"     "Data.Nat.Properties.+-assoc"     .defSym "AgdaMirror.agdaAddAssoc"
  , mkSym "*-identityˡ" "Data.Nat.Properties.*-identityˡ" .defSym "AgdaMirror.agdaMulIdentityL"
  , mkSym "*-identityʳ" "Data.Nat.Properties.*-identityʳ" .defSym "AgdaMirror.agdaMulIdentityR"
  , mkSym "<ᵇ⇒<"        "Data.Nat.Properties.<ᵇ⇒<"        .defSym "AgdaMirror.agdaNatLtbToLt"
  , mkSym "≤-trans"     "Data.Nat.Properties.≤-trans"     .defSym "AgdaMirror.agdaNatLeTrans"
  , mkSym "<-irrefl"    "Data.Nat.Properties.<-irrefl"    .defSym "AgdaMirror.agdaNatLtIrrefl"
  , mkSym "_≤?_"   "Data.Nat.Properties._≤?_"   .defSym "AgdaMirror.agdaNatLeDec" (.related 4 .infixN)
  , mkSym "m≤n+m"  "Data.Nat.Properties.m≤n+m"  .defSym "AgdaMirror.agdaNatMLeNM" ]

def builtinIntExports : List SymInfo :=
  [ mkSym "Int"    "Agda.Builtin.Int.Int"        .typeSym "Int"
  , mkSym "pos"    "Agda.Builtin.Int.Int.pos"    .conSym  "Int.ofNat"   .unrelated 1
  , mkSym "negsuc" "Agda.Builtin.Int.Int.negsuc" .conSym  "Int.negSucc" .unrelated 1
  ]

def dataIntExports : List SymInfo :=
  [ mkSym "ℤ"       "Agda.Builtin.Int.Int"          .typeSym "Int"
  , mkSym "+_"      "Agda.Builtin.Int.Int.pos"      .conSym  "Int.ofNat"   defaultAgdaFixity 1
  , mkSym "-[1+_]"  "Agda.Builtin.Int.Int.negsuc"   .conSym  "Int.negSucc" defaultAgdaFixity 1
  , mkSym "0ℤ"      "Data.Integer.Base.0ℤ"          .defSym  "AgdaMirror.agdaIntZero"
  , mkSym "-1ℤ"     "Data.Integer.Base.-1ℤ"         .defSym  "AgdaMirror.agdaIntNegOne"
  , mkSym "1ℤ"      "Data.Integer.Base.1ℤ"          .defSym  "AgdaMirror.agdaIntOne"
  , mkSym "∣_∣"     "Data.Integer.Base.∣_∣"         .defSym  "AgdaMirror.agdaIntAbs"
  , mkSym "_≤_"     "Data.Integer.Base._≤_"         .typeSym "AgdaMirror.AgdaIntLeRel" (.related 4 .infixN)
  , mkSym "-≤-"     "Data.Integer.Base._≤_.-≤-"     .conSym  "AgdaMirror.AgdaIntLeRel.negLeNeg" .unrelated 1
  , mkSym "-≤+"     "Data.Integer.Base._≤_.-≤+"     .conSym  "AgdaMirror.AgdaIntLeRel.negLePos" .unrelated 0
  , mkSym "+≤+"     "Data.Integer.Base._≤_.+≤+"     .conSym  "AgdaMirror.AgdaIntLeRel.posLePos" .unrelated 1
  , mkSym "_≤ᵇ_"    "Data.Integer.Base._≤ᵇ_"        .defSym  "AgdaMirror.agdaIntLeB"   (.related 4 .infixN)
  , mkSym "-_"      "Data.Integer.Base.-_"          .defSym  "AgdaMirror.agdaIntNeg"   (.related 8 .infixN)
  , mkSym "_⊖_"     "Data.Integer.Base._⊖_"         .defSym  "AgdaMirror.agdaNatSubInt" (.related 6 .infixL)
  , mkSym "_+_"     "Data.Integer.Base._+_"         .defSym  "AgdaMirror.agdaIntAdd"   (.related 6 .infixL)
  , mkSym "_-_"     "Data.Integer.Base._-_"         .defSym  "AgdaMirror.agdaIntSub"   (.related 6 .infixL)
  , mkSym "suc"     "Data.Integer.Base.suc"         .defSym  "AgdaMirror.agdaIntSuc"
  , mkSym "pred"    "Data.Integer.Base.pred"        .defSym  "AgdaMirror.agdaIntPred"
  , mkSym "_*_"     "Data.Integer.Base._*_"         .defSym  "AgdaMirror.agdaIntMul"   (.related 7 .infixL)
  , mkSym "_⊔_"     "Data.Integer.Base._⊔_"         .defSym  "AgdaMirror.agdaIntMax"   (.related 6 .infixL)
  , mkSym "_⊓_"     "Data.Integer.Base._⊓_"         .defSym  "AgdaMirror.agdaIntMin"   (.related 7 .infixL)
  , mkSym "_≟_"     "Data.Integer.Properties._≟_"   .defSym  "AgdaMirror.agdaIntDecEq" (.related 4 .infixN)
  , mkSym "_≤?_"    "Data.Integer.Properties._≤?_"  .defSym  "AgdaMirror.agdaIntLeDec" (.related 4 .infixN)
  ]

def dataIntPropsExports : List SymInfo :=
  [ mkSym "_≟_"  "Data.Integer.Properties._≟_"  .defSym "AgdaMirror.agdaIntDecEq" (.related 4 .infixN)
  , mkSym "_≤?_" "Data.Integer.Properties._≤?_" .defSym "AgdaMirror.agdaIntLeDec" (.related 4 .infixN) ]

def dataNatShowExports : List SymInfo :=
  [ mkSym "show" "Data.Nat.Show.show" .defSym "AgdaMirror.agdaNatShow" ]

def dataNatDivModExports : List SymInfo :=
  [ mkSym "_/_"   "Data.Nat.DivMod._/_"   .defSym "AgdaMirror.agdaDiv"       (.related 7 .infixL)
  , mkSym "_%_"   "Data.Nat.DivMod._%_"   .defSym "AgdaMirror.agdaModNat"    (.related 7 .infixL)
  , mkSym "_mod_" "Data.Nat.DivMod._mod_" .defSym "AgdaMirror.agdaNatModFin" (.related 7 .infixL)
  ]

def dataBoolExports : List SymInfo :=
  [ mkSym "Bool"          "Agda.Builtin.Bool.Bool"       .typeSym "Bool"
  , mkSym "true"          "Agda.Builtin.Bool.Bool.true"  .conSym  "Bool.true"  .unrelated 0
  , mkSym "false"         "Agda.Builtin.Bool.Bool.false" .conSym  "Bool.false" .unrelated 0
  , mkSym "not"           "Data.Bool.Base.not"           .defSym  "AgdaMirror.agdaNot"
  , mkSym "_∧_"           "Data.Bool.Base._∧_"           .defSym  "AgdaMirror.agdaAnd" (.related 6 .infixR)
  , mkSym "_∨_"           "Data.Bool.Base._∨_"           .defSym  "AgdaMirror.agdaOr"  (.related 5 .infixR)
  , mkSym "_xor_"         "Data.Bool.Base._xor_"         .defSym  "AgdaMirror.agdaXor" (.related 5 .infixR)
  , mkSym "if_then_else_" "Data.Bool.Base.if_then_else_" .defSym  "AgdaMirror.agdaIte" (.related 0 .infixN)
  , mkSym "T"             "Data.Bool.Base.T"             .typeSym "AgdaMirror.AgdaT"
  , mkSym "T?"            "Data.Bool.Properties.T?"      .defSym  "AgdaMirror.agdaBoolTDec"
  ]

def dataBoolPropsExports : List SymInfo :=
  [ mkSym "T?" "Data.Bool.Properties.T?" .defSym "AgdaMirror.agdaBoolTDec" ]

def builtinBoolExports : List SymInfo :=
  [ mkSym "Bool"  "Agda.Builtin.Bool.Bool"       .typeSym "Bool"
  , mkSym "true"  "Agda.Builtin.Bool.Bool.true"  .conSym  "Bool.true"  .unrelated 0
  , mkSym "false" "Agda.Builtin.Bool.Bool.false" .conSym  "Bool.false" .unrelated 0
  ]

def dataListExports : List SymInfo :=
  [ mkSym "List"      "Agda.Builtin.List.List"     .typeSym "List"
  , mkSym "[]"        "Agda.Builtin.List.List.[]"  .conSym  "List.nil"  .unrelated 0
  , mkSym "_∷_"       "Agda.Builtin.List.List._∷_" .conSym  "List.cons" (.related 5 .infixR) 2
  , mkSym "[_]"       "Data.List.Base.[_]"         .defSym  "(fun x => List.cons x List.nil)"
  , mkSym "_++_"      "Data.List.Base._++_"        .defSym  "AgdaMirror.agdaAppend" (.related 5 .infixR)
  , mkSym "map"       "Data.List.Base.map"         .defSym  "AgdaMirror.agdaMap"
  , mkSym "mapMaybe"  "Data.List.Base.mapMaybe"    .defSym  "AgdaMirror.agdaMapMaybe"
  , mkSym "concatMap" "Data.List.Base.concatMap"   .defSym  "AgdaMirror.agdaConcatMap"
  , mkSym "foldr"     "Data.List.Base.foldr"       .defSym  "AgdaMirror.agdaFoldr"
  , mkSym "foldl"     "Data.List.Base.foldl"       .defSym  "AgdaMirror.agdaFoldl"
  , mkSym "length"    "Data.List.Base.length"      .defSym  "AgdaMirror.agdaLength"
  , mkSym "reverse"   "Data.List.Base.reverse"     .defSym  "AgdaMirror.agdaReverse"
  , mkSym "replicate" "Data.List.Base.replicate"   .defSym  "AgdaMirror.agdaReplicate"
  , mkSym "all"       "Data.List.Base.all"         .defSym  "AgdaMirror.agdaAllB"
  , mkSym "any"       "Data.List.Base.any"         .defSym  "AgdaMirror.agdaAnyB"
  , mkSym "take"      "Data.List.Base.take"        .defSym  "AgdaMirror.agdaTake"
  , mkSym "drop"      "Data.List.Base.drop"        .defSym  "AgdaMirror.agdaDrop"
  , mkSym "applyUpTo" "Data.List.Base.applyUpTo"   .defSym  "AgdaMirror.agdaApplyUpTo"
  , mkSym "upTo"      "Data.List.Base.upTo"        .defSym  "AgdaMirror.agdaUpTo"
  , mkSym "zip"       "Data.List.Base.zip"         .defSym  "AgdaMirror.agdaZip"
  , mkSym "tails"     "Data.List.Base.tails"       .defSym  "AgdaMirror.agdaTails"
  , mkSym "lookup"    "Data.List.Base.lookup"      .defSym  "AgdaMirror.agdaLookup"
  , mkSym "linesBy"   "Data.List.Base.linesBy"     .defSym  "AgdaMirror.agdaLinesBy"
  , mkSym "wordsBy"   "Data.List.Base.wordsBy"     .defSym  "AgdaMirror.agdaWordsByList"
  ]

def dataListAnyExports : List SymInfo :=
  [ mkSym "Any"   "Data.List.Relation.Unary.Any.Any"       .typeSym "AgdaMirror.AgdaAny"
  , mkSym "here"  "Data.List.Relation.Unary.Any.Any.here"  .conSym  "AgdaMirror.AgdaAny.here"  .unrelated 1
  , mkSym "there" "Data.List.Relation.Unary.Any.Any.there" .conSym  "AgdaMirror.AgdaAny.there" .unrelated 1
  ]

def dataListAllExports : List SymInfo :=
  [ mkSym "All" "Data.List.Relation.Unary.All.All"     .typeSym "AgdaMirror.AgdaAll"
  , mkSym "[]"  "Data.List.Relation.Unary.All.All.[]"  .conSym  "AgdaMirror.AgdaAll.nil"  .unrelated 0
  , mkSym "_∷_" "Data.List.Relation.Unary.All.All._∷_" .conSym  "AgdaMirror.AgdaAll.cons" (.related 5 .infixR) 2
  ]

def dataPermutationExports (modName : String) : List SymInfo :=
  let rel := modName ++ "._↭_"
  [ mkSym "_↭_" rel .typeSym "AgdaMirror.AgdaPermutation" (.related 3 .infixN)
  , mkSym "refl" (rel ++ ".refl") .conSym "AgdaMirror.AgdaPermutation.refl" .unrelated 0
  , mkSym "prep" (rel ++ ".prep") .conSym "AgdaMirror.AgdaPermutation.prep" .unrelated 2
  , mkSym "swap" (rel ++ ".swap") .conSym "AgdaMirror.AgdaPermutation.swap" .unrelated 3
  , mkSym "trans" (rel ++ ".trans") .conSym "AgdaMirror.AgdaPermutation.trans" .unrelated 2
  ]

def dataListPropsExports : List SymInfo :=
  [ mkSym "++-assoc"     "Data.List.Properties._.++-assoc"     .defSym "AgdaMirror.agdaAppendAssoc"
  , mkSym "++-identityˡ" "Data.List.Properties._.++-identityˡ" .defSym "AgdaMirror.agdaAppendIdentityL"
  , mkSym "++-identityʳ" "Data.List.Properties._.++-identityʳ" .defSym "AgdaMirror.agdaAppendIdentityR"
  ]

def builtinCharPropsExports : List SymInfo :=
  [ mkSym "primCharToNatInjective" "Agda.Builtin.Char.Properties.primCharToNatInjective" .defSym "AgdaMirror.agdaCharToNatInjective" ]

def builtinListExports : List SymInfo :=
  [ mkSym "List" "Agda.Builtin.List.List"     .typeSym "List"
  , mkSym "[]"   "Agda.Builtin.List.List.[]"  .conSym  "List.nil"  .unrelated 0
  , mkSym "_∷_"  "Agda.Builtin.List.List._∷_" .conSym  "List.cons" (.related 5 .infixR) 2
  ]

def dataMaybeExports : List SymInfo :=
  [ mkSym "Maybe"      "Agda.Builtin.Maybe.Maybe"         .typeSym "AgdaMirror.AgdaMaybe"
  , mkSym "just"       "Agda.Builtin.Maybe.Maybe.just"    .conSym  "AgdaMirror.AgdaMaybe.just"    .unrelated 1
  , mkSym "nothing"    "Agda.Builtin.Maybe.Maybe.nothing" .conSym  "AgdaMirror.AgdaMaybe.nothing" .unrelated 0
  , mkSym "map"        "Data.Maybe.Base.map"              .defSym  "AgdaMirror.maybeMap"
  , mkSym "_>>=_"      "Data.Maybe.Base._>>=_"            .defSym  "AgdaMirror.maybeBind" (.related 1 .infixL)
  , mkSym "maybe′"     "Data.Maybe.Base.maybe′"           .defSym  "AgdaMirror.maybePrime"
  , mkSym "fromMaybe"  "Data.Maybe.Base.fromMaybe"        .defSym  "AgdaMirror.fromMaybe"
  , mkSym "when"       "Data.Maybe.Base.when"             .defSym  "AgdaMirror.maybeWhen"
  , mkSym "is-just"    "Data.Maybe.Base.is-just"          .defSym  "AgdaMirror.maybeIsJust"
  , mkSym "is-nothing" "Data.Maybe.Base.is-nothing"       .defSym  "AgdaMirror.maybeIsNothing"
  , mkSym "zipWith"    "Data.Maybe.Base.zipWith"          .defSym  "AgdaMirror.maybeZipWith"
  ]

def builtinSigmaExports : List SymInfo :=
  [ mkSym "Σ"   "Agda.Builtin.Sigma.Σ"     .typeSym "AgdaMirror.AgdaSigma"
  , mkSym "_,_" "Agda.Builtin.Sigma._,_"   .conSym "AgdaMirror.AgdaSigma.mk" (.related 4 .infixR) 2
  , mkSym "fst" "Agda.Builtin.Sigma.Σ.fst" (.projSym 2) "AgdaMirror.AgdaSigma.proj₁"
  , mkSym "snd" "Agda.Builtin.Sigma.Σ.snd" (.projSym 2) "AgdaMirror.AgdaSigma.proj₂"
  ]

def dataProductExports : List SymInfo :=
  [ mkSym "Σ"     "Agda.Builtin.Sigma.Σ"     .typeSym "AgdaMirror.AgdaSigma"
  , mkSym "∃"     "Data.Product.∃"           .typeSym "AgdaMirror.AgdaExists"
  , mkSym "_×_"   "Data.Product._×_"         .typeSym "AgdaMirror.AgdaProd"      (.related 2 .infixR)
  , mkSym "_,_"   "Agda.Builtin.Sigma._,_"   .conSym  "AgdaMirror.AgdaSigma.mk"  (.related 4 .infixR) 2
  , mkSym "proj₁" "Agda.Builtin.Sigma.Σ.fst" (.projSym 2) "AgdaMirror.AgdaSigma.proj₁"
  , mkSym "proj₂" "Agda.Builtin.Sigma.Σ.snd" (.projSym 2) "AgdaMirror.AgdaSigma.proj₂"
  , mkSym "map₁"  "Data.Product.map₁"        .defSym  "AgdaMirror.prodMap1"
  , mkSym "map₂"  "Data.Product.map₂"        .defSym  "AgdaMirror.prodMap2"
  ]

def dataSumExports : List SymInfo :=
  [ mkSym "_⊎_"    "Data.Sum.Base._⊎_"       .typeSym "AgdaMirror.AgdaSum"      (.related 1 .infixR)
  , mkSym "inj₁"   "Data.Sum.Base._⊎_.inj₁"  .conSym  "AgdaMirror.AgdaSum.inj₁" .unrelated 1
  , mkSym "inj₂"   "Data.Sum.Base._⊎_.inj₂"  .conSym  "AgdaMirror.AgdaSum.inj₂" .unrelated 1
  , mkSym "[_,_]"  "Data.Sum.Base.[_,_]"     .defSym  "AgdaMirror.agdaSumElim"
  , mkSym "[_,_]′" "Data.Sum.Base.[_,_]′"    .defSym  "AgdaMirror.agdaSumElim"
  , mkSym "map"    "Data.Sum.Base.map"       .defSym  "AgdaMirror.agdaSumMap"
  , mkSym "map₁"   "Data.Sum.Base.map₁"      .defSym  "AgdaMirror.agdaSumMap₁"
  , mkSym "map₂"   "Data.Sum.Base.map₂"      .defSym  "AgdaMirror.agdaSumMap₂"
  ]

def dataFinExports : List SymInfo :=
  [ mkSym "Fin"   "Data.Fin.Base.Fin"      .typeSym "AgdaMirror.AgdaFin"
  , mkSym "zero"  "Data.Fin.Base.Fin.zero" .conSym  "AgdaMirror.AgdaFin.zero" .unrelated 0
  , mkSym "suc"   "Data.Fin.Base.Fin.suc"  .conSym  "AgdaMirror.AgdaFin.suc"  .unrelated 1
  , mkSym "toℕ"   "Data.Fin.Base.toℕ"      .defSym  "AgdaMirror.agdaFinToNat"
  ]

def dataCharExports : List SymInfo :=
  [ mkSym "Char"             "Agda.Builtin.Char.Char"             .typeSym "Char"
  , mkSym "primCharEquality" "Agda.Builtin.Char.primCharEquality" .defSym  "AgdaMirror.agdaCharEq"
  , mkSym "primToLower"      "Agda.Builtin.Char.primToLower"      .defSym  "AgdaMirror.agdaToLower"
  , mkSym "toLower"          "Agda.Builtin.Char.primToLower"      .defSym  "AgdaMirror.agdaToLower"
  , mkSym "toℕ"              "Agda.Builtin.Char.primCharToNat"    .defSym  "AgdaMirror.agdaCharToNat"
  , mkSym "primCharToNat"    "Agda.Builtin.Char.primCharToNat"    .defSym  "AgdaMirror.agdaCharToNat"
  , mkSym "primNatToChar"    "Agda.Builtin.Char.primNatToChar"    .defSym  "AgdaMirror.agdaCharFromNat"
  , mkSym "fromℕ"            "Agda.Builtin.Char.primNatToChar"    .defSym  "AgdaMirror.agdaCharFromNat"
  , mkSym "isSpace"          "Agda.Builtin.Char.primIsSpace"      .defSym  "AgdaMirror.agdaIsSpace"
  , mkSym "isPrint"          "Agda.Builtin.Char.primIsPrint"      .defSym  "AgdaMirror.agdaIsPrint"
  , mkSym "isDigit"          "Agda.Builtin.Char.primIsDigit"      .defSym  "AgdaMirror.agdaIsDigit"
  , mkSym "isAlpha"          "Agda.Builtin.Char.primIsAlpha"      .defSym  "AgdaMirror.agdaIsAlpha"
  , mkSym "_≟_"              "Data.Char.Properties._≟_"           .defSym  "AgdaMirror.agdaCharDecEq" (.related 4 .infixN)
  ]

def dataCharPropsExports : List SymInfo :=
  [ mkSym "_≟_" "Data.Char.Properties._≟_" .defSym "AgdaMirror.agdaCharDecEq" (.related 4 .infixN)
  , mkSym "_==_" "Data.Char.Properties._==_" .defSym "AgdaMirror.agdaCharEqDecides" (.related 4 .infixN)
  , mkSym "toℕ-injective" "Agda.Builtin.Char.Properties.primCharToNatInjective" .defSym "AgdaMirror.agdaCharToNatInjective"
  ]

def builtinStringExports : List SymInfo :=
  [ mkSym "String"             "Agda.Builtin.String.String"             .typeSym "String"
  , mkSym "primStringEquality" "Agda.Builtin.String.primStringEquality" .defSym  "AgdaMirror.agdaStrEq"
  -- Agda and Lean escape control characters differently. Resolve the name for native Agda checking.
  , mkSym "primShowString"     "Agda.Builtin.String.primShowString"     .defSym  ""
  , mkSym "primShowNat"        "Agda.Builtin.String.primShowNat"        .defSym  "AgdaMirror.agdaPrimShowNat"
  , mkSym "primStringToList"   "Agda.Builtin.String.primStringToList"   .defSym  "AgdaMirror.agdaToList"
  , mkSym "primStringFromList" "Agda.Builtin.String.primStringFromList" .defSym  "AgdaMirror.agdaFromList"
  , mkSym "primStringAppend"   "Agda.Builtin.String.primStringAppend"   .defSym  "AgdaMirror.agdaStrAppend"
  ]

def dataStringBaseExports : List SymInfo :=
  [ mkSym "String"             "Agda.Builtin.String.String"             .typeSym "String"
  , mkSym "show"               "Agda.Builtin.String.primShowString"     .defSym  ""
  , mkSym "_++_"               "Data.String.Base._++_"                  .defSym  "AgdaMirror.agdaStrAppend" (.related 5 .infixR)
  , mkSym "toList"             "Agda.Builtin.String.primStringToList"   .defSym  "AgdaMirror.agdaToList"
  , mkSym "fromList"           "Agda.Builtin.String.primStringFromList" .defSym  "AgdaMirror.agdaFromList"
  , mkSym "concat"             "Data.String.Base.concat"                .defSym  "AgdaMirror.agdaStrConcat"
  , mkSym "intersperse"        "Data.String.Base.intersperse"           .defSym  "AgdaMirror.agdaIntersperse"
  , mkSym "unlines"            "Data.String.Base.unlines"               .defSym  "AgdaMirror.agdaUnlines"
  ]

def dataStringExports : List SymInfo := dataStringBaseExports ++
  [ mkSym "wordsBy"            "Data.String.wordsBy"                    .defSym  "AgdaMirror.agdaWordsBy"
  , mkSym "words"              "Data.String.words"                      .defSym  "AgdaMirror.agdaWords"
  , mkSym "linesBy"            "Data.String.linesBy"                    .defSym  "AgdaMirror.agdaLinesByStr"
  , mkSym "lines"              "Data.String.lines"                      .defSym  "AgdaMirror.agdaLines"
  , mkSym "_≟_"                "Data.String.Properties._≟_"             .defSym  "AgdaMirror.agdaStrDecEq" (.related 4 .infixN)
  ]

def builtinStringPropsExports : List SymInfo :=
  [ mkSym "primStringToListInjective" "Agda.Builtin.String.Properties.primStringToListInjective" .defSym "AgdaMirror.agdaStrToListInjective"
  , mkSym "primStringFromListInjective" "Agda.Builtin.String.Properties.primStringFromListInjective" .defSym "AgdaMirror.agdaStrFromListInjective"
  ]

def dataStringPropsExports : List SymInfo :=
  [ mkSym "_≟_" "Data.String.Properties._≟_" .defSym "AgdaMirror.agdaStrDecEq" (.related 4 .infixN)
  , mkSym "_==_" "Data.String.Properties._==_" .defSym "AgdaMirror.agdaStrEqDecides" (.related 4 .infixN)
  , mkSym "toList-injective" "Agda.Builtin.String.Properties.primStringToListInjective" .defSym "AgdaMirror.agdaStrToListInjective"
  , mkSym "primStringFromListInjective" "Agda.Builtin.String.Properties.primStringFromListInjective" .defSym "AgdaMirror.agdaStrFromListInjective"
  ]

def dataUnitExports : List SymInfo :=
  [ mkSym "⊤"  "Agda.Builtin.Unit.⊤"    .typeSym "AgdaMirror.AgdaTop"
  , mkSym "tt" "Agda.Builtin.Unit.tt"   .conSym  "AgdaMirror.AgdaTop.tt" .unrelated 0
  ]

def dataPolyUnitExports : List SymInfo :=
  [ mkSym "⊤"  "Data.Unit.Polymorphic.Base.⊤"  .typeSym "AgdaMirror.PolyTop"
  , mkSym "tt" "Data.Unit.Polymorphic.Base.tt" .defSym  "AgdaMirror.PolyTop.tt"
  ]

def dataEmptyExports : List SymInfo :=
  [ mkSym "⊥"      "Data.Empty.⊥"      .typeSym "AgdaMirror.AgdaBot"
  , mkSym "⊥-elim" "Data.Empty.⊥-elim" .defSym  "AgdaMirror.botElim"
  ]

def relNullaryExports : List SymInfo :=
  [ mkSym "Dec"  "Relation.Nullary.Dec"       .typeSym "AgdaMirror.AgdaDec"
  , mkSym "yes"  "Relation.Nullary.yes"   .conSym  "AgdaMirror.AgdaDec.yes" .unrelated 1
  , mkSym "no"   "Relation.Nullary.no"    .conSym  "AgdaMirror.AgdaDec.no"  .unrelated 1
  , mkSym "¬_"   "Relation.Nullary.¬_"        .typeSym "AgdaMirror.AgdaNeg"     (.related 3 .infixN)
  , mkSym "does" "Relation.Nullary.Dec.does" .defSym "AgdaMirror.agdaDoes"
  ]

def decidableCoreExports : List SymInfo :=
  [ mkSym "isYes" "Relation.Nullary.Decidable.Core.isYes" .defSym "AgdaMirror.agdaIsYes"
  , mkSym "⌊_⌋" "Relation.Nullary.Decidable.Core.⌊_⌋" .defSym "AgdaMirror.agdaIsYes"
  , mkSym "isYes≗does" "Relation.Nullary.Decidable.Core.isYes≗does" .defSym "AgdaMirror.agdaIsYesDoes"
  , mkSym "map′" "Relation.Nullary.Decidable.Core.map′" .defSym "AgdaMirror.agdaMapDec"
  , mkSym "dec-true" "Relation.Nullary.Decidable.Core.dec-true" .defSym "AgdaMirror.agdaDecTrue"
  , mkSym "dec-false" "Relation.Nullary.Decidable.Core.dec-false" .defSym "AgdaMirror.agdaDecFalse"
  , mkSym "True" "Relation.Nullary.Decidable.Core.True" .defSym "AgdaMirror.agdaDecIsTrue"
  , mkSym "False" "Relation.Nullary.Decidable.Core.False" .defSym "AgdaMirror.agdaDecIsFalse"
  , mkSym "toWitness" "Relation.Nullary.Decidable.Core.toWitness" .defSym "AgdaMirror.agdaToWitness"
  , mkSym "toWitnessFalse" "Relation.Nullary.Decidable.Core.toWitnessFalse" .defSym "AgdaMirror.agdaToWitnessFalse"
  ]

def propEqExports : List SymInfo :=
  [ mkSym "_≡_"   "Agda.Builtin.Equality._≡_"                     .typeSym "AgdaMirror.AgdaId"      (.related 4 .infixN)
  , mkSym "_≢_"   "Relation.Binary.PropositionalEquality.Core._≢_" .typeSym "AgdaMirror.AgdaNotEq"   (.related 4 .infixN)
  , mkSym "refl"  "Agda.Builtin.Equality._≡_.refl"                .conSym  "AgdaMirror.AgdaId.refl" .unrelated 0
  , mkSym "sym"   "Relation.Binary.PropositionalEquality.Core.sym"   .defSym "AgdaMirror.idSym"
  , mkSym "trans" "Relation.Binary.PropositionalEquality.Core.trans" .defSym "AgdaMirror.idTrans"
  , mkSym "cong"  "Relation.Binary.PropositionalEquality.Core.cong"  .defSym "AgdaMirror.idCong"
  , mkSym "cong₂" "Relation.Binary.PropositionalEquality.Core.cong₂" .defSym "AgdaMirror.idCong2"
  , mkSym "subst" "Relation.Binary.PropositionalEquality.Core.subst" .defSym "AgdaMirror.idSubst"
  ]

def functionExports : List SymInfo :=
  [ mkSym "id"       "Function.Base.id"       .defSym "AgdaMirror.agdaIdFn"
  , mkSym "const"    "Function.Base.const"    .defSym "AgdaMirror.agdaConst"
  , mkSym "_∘_"      "Function.Base._∘_"      .defSym "AgdaMirror.agdaComp" (.related 9 .infixR)
  , mkSym "_$_"      "Function.Base._$_"      .defSym "AgdaMirror.agdaApp"  (.related (-1) .infixR)
  , mkSym "case_of_" "Function.Base.case_of_" .defSym "(fun x f => f x)"    (.related 0 .infixN)
  ]

def tabooExports : List SymInfo :=
  let ctor (agda lean : String) :=
    mkSym agda ("Context.Taboo.SafeTaboo." ++ agda) .conSym ("AgdaMirror.Context.SafeTaboo." ++ lean) .unrelated 1
  [ mkSym "SafeTaboo" "Context.Taboo.SafeTaboo" .typeSym "AgdaMirror.Context.SafeTaboo"
  , ctor "taboo-⊥" "bottom"
  , ctor "taboo-primStrRefl" "primStrRefl"
  , ctor "taboo-primCharRefl" "primCharRefl"
  , ctor "taboo-strRoundtrip" "strRoundtrip"
  , ctor "taboo-listRoundtrip" "listRoundtrip"
  , ctor "taboo-funExtBool" "funExtBool"
  , ctor "taboo-wlpo" "wlpo"
  , ctor "taboo-markov" "markov"
  ]

def blueprintExports : List SymInfo :=
  [ mkSym "PortLift"    "Context.Blueprint.PortLift"         .typeSym "AgdaMirror.Context.PortLift"
  , mkSym "portLift"    "Context.Blueprint.portLift"         .conSym  "AgdaMirror.Context.PortLift.portLift" .unrelated 1
  , mkSym "project"     "Context.Blueprint.PortLift.project" (.projSym 2) "AgdaMirror.Context.PortLift.project"
  , mkSym "keepPort"    "Context.Blueprint.keepPort"         .defSym  "AgdaMirror.Context.keepPort"
  , mkSym "fromEl"      "Context.Blueprint.fromEl"           .defSym  "AgdaMirror.Context.fromEl"
  , mkSym "FiberOf"     "Context.Blueprint.FiberOf"          .typeSym "AgdaMirror.Context.FiberOf"
  , mkSym "composeLift" "Context.Blueprint.composeLift"      .defSym  "AgdaMirror.Context.composeLift"
  , mkSym "Commutes₁"   "Context.Blueprint.Commutes₁"        .typeSym "AgdaMirror.Context.Commutes₁"
  , mkSym "Commutes₂"   "Context.Blueprint.Commutes₂"        .typeSym "AgdaMirror.Context.Commutes₂"
  , mkSym "Commutes₃"   "Context.Blueprint.Commutes₃"        .typeSym "AgdaMirror.Context.Commutes₃"
  ]

def polyTransportExports : List SymInfo :=
  [ mkSym "PortRel"              "Context.PolyTransport.PortRel"              .typeSym "AgdaMirror.Context.PortRel"
  , mkSym "portRel"              "Context.PolyTransport.portRel"              .conSym  "AgdaMirror.Context.PortRel.portRel" .unrelated 1
  , mkSym "rel"                  "Context.PolyTransport.PortRel.rel"          (.projSym 2) "AgdaMirror.Context.PortRel.rel"
  , mkSym "idPort"               "Context.PolyTransport.idPort"               .defSym  "AgdaMirror.Context.idPort"
  , mkSym "equivPort"            "Context.PolyTransport.equivPort"            .defSym  "AgdaMirror.Context.equivPort"
  , mkSym "graphPort"            "Context.PolyTransport.graphPort"            .defSym  "AgdaMirror.Context.graphPort"
  , mkSym "cographPort"          "Context.PolyTransport.cographPort"          .defSym  "AgdaMirror.Context.cographPort"
  , mkSym "tensorPort"           "Context.PolyTransport.tensorPort"           .defSym  "AgdaMirror.Context.tensorPort"
  , mkSym "splitPort"            "Context.PolyTransport.splitPort"            .defSym  "AgdaMirror.Context.splitPort"
  , mkSym "mergePort"            "Context.PolyTransport.mergePort"            .defSym  "AgdaMirror.Context.mergePort"
  , mkSym "introPort"            "Context.PolyTransport.introPort"            .defSym  "AgdaMirror.Context.introPort"
  , mkSym "elimPort"             "Context.PolyTransport.elimPort"             .defSym  "AgdaMirror.Context.elimPort"
  , mkSym "compPort"             "Context.PolyTransport.compPort"             .defSym  "AgdaMirror.Context.compPort"
  , mkSym "cut₁"                 "Context.PolyTransport.cut₁"                 .defSym  "AgdaMirror.Context.cut₁"
  , mkSym "cutRel"               "Context.PolyTransport.cutRel"               .defSym  "AgdaMirror.Context.cutRel"
  , mkSym "TransportsPoly"       "Context.PolyTransport.TransportsPoly"       .typeSym "AgdaMirror.Context.TransportsPoly"
  , mkSym "Transports₁"          "Context.PolyTransport.Transports₁"          .typeSym "AgdaMirror.Context.Transports₁"
  , mkSym "Transports₂"          "Context.PolyTransport.Transports₂"          .typeSym "AgdaMirror.Context.Transports₂"
  , mkSym "composeTransportsCut" "Context.PolyTransport.composeTransportsCut" .defSym  "AgdaMirror.Context.composeTransportsCut"
  , mkSym "transportLiftCube"    "Context.PolyTransport.transportLiftCube"    .defSym  "AgdaMirror.Context.transportLiftCube"
  ]

def terminalExports : List SymInfo :=
  [ mkSym "Byte"             "Context.Terminal.Byte"                     .typeSym     "AgdaMirror.Context.Byte"
  , mkSym "Bytes"            "Context.Terminal.Bytes"                    .typeSym     "AgdaMirror.Context.Bytes"
  , mkSym "byte"             "Context.Terminal.byte"                     .defSym      "AgdaMirror.Context.byte"
  , mkSym "utf8Char"         "Context.Terminal.utf8Char"                 .defSym      "AgdaMirror.Context.utf8Char"
  , mkSym "bytes"            "Context.Terminal.bytes"                    .defSym      "AgdaMirror.Context.bytes"
  , mkSym "Key"              "Context.Terminal.Key"                      .typeSym     "AgdaMirror.Context.Key"
  , mkSym "textKey"          "Context.Terminal.Key.textKey"              .conSym      "AgdaMirror.Context.Key.textKey"   .unrelated 1
  , mkSym "enter"            "Context.Terminal.Key.enter"                .conSym      "AgdaMirror.Context.Key.enter"     .unrelated 0
  , mkSym "escape"           "Context.Terminal.Key.escape"               .conSym      "AgdaMirror.Context.Key.escape"    .unrelated 0
  , mkSym "backspace"        "Context.Terminal.Key.backspace"            .conSym      "AgdaMirror.Context.Key.backspace" .unrelated 0
  , mkSym "tab"              "Context.Terminal.Key.tab"                  .conSym      "AgdaMirror.Context.Key.tab"       .unrelated 0
  , mkSym "up"               "Context.Terminal.Key.up"                   .conSym      "AgdaMirror.Context.Key.up"        .unrelated 0
  , mkSym "down"             "Context.Terminal.Key.down"                 .conSym      "AgdaMirror.Context.Key.down"      .unrelated 0
  , mkSym "right"            "Context.Terminal.Key.right"                .conSym      "AgdaMirror.Context.Key.right"     .unrelated 0
  , mkSym "left"             "Context.Terminal.Key.left"                 .conSym      "AgdaMirror.Context.Key.left"      .unrelated 0
  , mkSym "home"             "Context.Terminal.Key.home"                 .conSym      "AgdaMirror.Context.Key.home"      .unrelated 0
  , mkSym "end"              "Context.Terminal.Key.end"                  .conSym      "AgdaMirror.Context.Key.end"       .unrelated 0
  , mkSym "delete"           "Context.Terminal.Key.delete"               .conSym      "AgdaMirror.Context.Key.delete"    .unrelated 0
  , mkSym "ctrl"             "Context.Terminal.Key.ctrl"                 .conSym      "AgdaMirror.Context.Key.ctrl"      .unrelated 1
  , mkSym "encodeKey"        "Context.Terminal.encodeKey"                .defSym      "AgdaMirror.Context.encodeKey"
  , mkSym "TermTopology"     "Context.Terminal.TermTopology"             .typeSym     "AgdaMirror.Context.TermTopology"
  , mkSym "allTTY"           "Context.Terminal.TermTopology.allTTY"      .conSym      "AgdaMirror.Context.TermTopology.allTTY"           .unrelated 0
  , mkSym "pipeStdioWithTTY" "Context.Terminal.TermTopology.pipeStdioWithTTY" .conSym "AgdaMirror.Context.TermTopology.pipeStdioWithTTY" .unrelated 0
  , mkSym "SandboxTarget"    "Context.Terminal.SandboxTarget"            .typeSym     "AgdaMirror.Context.SandboxTarget"
  , mkSym "localSandbox"     "Context.Terminal.SandboxTarget.localSandbox"  .conSym   "AgdaMirror.Context.SandboxTarget.localSandbox"    .unrelated 0
  , mkSym "dockerSandbox"    "Context.Terminal.SandboxTarget.dockerSandbox" .conSym   "AgdaMirror.Context.SandboxTarget.dockerSandbox"   .unrelated 1
  , mkSym "TermConfig"       "Context.Terminal.TermConfig"               .typeSym     "AgdaMirror.Context.TermConfig"
  , mkSym "termConfig"       "Context.Terminal.termConfig"               .conSym      "AgdaMirror.Context.TermConfig.termConfig" .unrelated 8
  , mkSym "target"           "Context.Terminal.TermConfig.target"        (.projSym 0) "AgdaMirror.Context.TermConfig.target"
  , mkSym "topology"         "Context.Terminal.TermConfig.topology"      (.projSym 0) "AgdaMirror.Context.TermConfig.topology"
  , mkSym "executable"       "Context.Terminal.TermConfig.executable"    (.projSym 0) "AgdaMirror.Context.TermConfig.executable"
  , mkSym "arguments"        "Context.Terminal.TermConfig.arguments"     (.projSym 0) "AgdaMirror.Context.TermConfig.arguments"
  , mkSym "envVars"          "Context.Terminal.TermConfig.envVars"       (.projSym 0) "AgdaMirror.Context.TermConfig.envVars"
  , mkSym "rows"             "Context.Terminal.TermConfig.rows"          (.projSym 0) "AgdaMirror.Context.TermConfig.rows"
  , mkSym "cols"             "Context.Terminal.TermConfig.cols"          (.projSym 0) "AgdaMirror.Context.TermConfig.cols"
  , mkSym "files"            "Context.Terminal.TermConfig.files"         (.projSym 0) "AgdaMirror.Context.TermConfig.files"
  , mkSym "Signal"           "Context.Terminal.Signal"                   .typeSym     "AgdaMirror.Context.TermSignal"
  , mkSym "sigINT"           "Context.Terminal.Signal.sigINT"            .conSym      "AgdaMirror.Context.TermSignal.sigINT"  .unrelated 0
  , mkSym "sigTERM"          "Context.Terminal.Signal.sigTERM"           .conSym      "AgdaMirror.Context.TermSignal.sigTERM" .unrelated 0
  , mkSym "sigHUP"           "Context.Terminal.Signal.sigHUP"            .conSym      "AgdaMirror.Context.TermSignal.sigHUP"  .unrelated 0
  , mkSym "sigQUIT"          "Context.Terminal.Signal.sigQUIT"           .conSym      "AgdaMirror.Context.TermSignal.sigQUIT" .unrelated 0
  , mkSym "sigKILL"          "Context.Terminal.Signal.sigKILL"           .conSym      "AgdaMirror.Context.TermSignal.sigKILL" .unrelated 0
  , mkSym "TermStep"         "Context.Terminal.TermStep"                 .typeSym     "AgdaMirror.Context.TermStep"
  , mkSym "writeStdin"       "Context.Terminal.TermStep.writeStdin"      .conSym      "AgdaMirror.Context.TermStep.writeStdin" .unrelated 1
  , mkSym "writeTTY"         "Context.Terminal.TermStep.writeTTY"        .conSym      "AgdaMirror.Context.TermStep.writeTTY"   .unrelated 1
  , mkSym "closeStdin"       "Context.Terminal.TermStep.closeStdin"      .conSym      "AgdaMirror.Context.TermStep.closeStdin" .unrelated 0
  , mkSym "sleepMs"          "Context.Terminal.TermStep.sleepMs"         .conSym      "AgdaMirror.Context.TermStep.sleepMs"    .unrelated 1
  , mkSym "resizeTTY"        "Context.Terminal.TermStep.resizeTTY"       .conSym      "AgdaMirror.Context.TermStep.resizeTTY"  .unrelated 2
  , mkSym "sendSignal"       "Context.Terminal.TermStep.sendSignal"      .conSym      "AgdaMirror.Context.TermStep.sendSignal" .unrelated 1
  , mkSym "drainRaw"         "Context.Terminal.TermStep.drainRaw"        .conSym      "AgdaMirror.Context.TermStep.drainRaw"   .unrelated 0
  , mkSym "RawTermObs"       "Context.Terminal.RawTermObs"               .typeSym     "AgdaMirror.Context.RawTermObs"
  , mkSym "rawObs"           "Context.Terminal.rawObs"                   .conSym      "AgdaMirror.Context.RawTermObs.rawObs"   .unrelated 4
  , mkSym "ttyOut"           "Context.Terminal.RawTermObs.ttyOut"        (.projSym 0) "AgdaMirror.Context.RawTermObs.ttyOut"
  , mkSym "stdoutOut"        "Context.Terminal.RawTermObs.stdoutOut"     (.projSym 0) "AgdaMirror.Context.RawTermObs.stdoutOut"
  , mkSym "stderrOut"        "Context.Terminal.RawTermObs.stderrOut"     (.projSym 0) "AgdaMirror.Context.RawTermObs.stderrOut"
  , mkSym "exitStatus"       "Context.Terminal.RawTermObs.exitStatus"    (.projSym 0) "AgdaMirror.Context.RawTermObs.exitStatus"
  , mkSym "emptyObs"         "Context.Terminal.emptyObs"                 .defSym      "AgdaMirror.Context.emptyObs"
  , mkSym "latest"           "Context.Terminal.latest"                   .defSym      "AgdaMirror.Context.latest"
  , mkSym "appendObs"        "Context.Terminal.appendObs"                .defSym      "AgdaMirror.Context.appendObs"
  , mkSym "TimerEdit"        "Context.Terminal.TimerEdit"                .typeSym     "AgdaMirror.Context.TimerEdit"
  , mkSym "arm"              "Context.Terminal.TimerEdit.arm"            .conSym      "AgdaMirror.Context.TimerEdit.arm"    .unrelated 3
  , mkSym "cancel"           "Context.Terminal.TimerEdit.cancel"         .conSym      "AgdaMirror.Context.TimerEdit.cancel" .unrelated 1
  , mkSym "Timer"            "Context.Terminal.Timer"                    .typeSym     "AgdaMirror.Context.Timer"
  , mkSym "timer"            "Context.Terminal.timer"                    .conSym      "AgdaMirror.Context.Timer.timer" .unrelated 3
  , mkSym "slot"             "Context.Terminal.Timer.slot"               (.projSym 1) "AgdaMirror.Context.Timer.slot"
  , mkSym "deadline"         "Context.Terminal.Timer.deadline"           (.projSym 1) "AgdaMirror.Context.Timer.deadline"
  , mkSym "payload"          "Context.Terminal.Timer.payload"            (.projSym 1) "AgdaMirror.Context.Timer.payload"
  , mkSym "Event"            "Context.Terminal.Event"                    .typeSym     "AgdaMirror.Context.TermEvent"
  , mkSym "input"            "Context.Terminal.Event.input"              .conSym      "AgdaMirror.Context.TermEvent.input"   .unrelated 1
  , mkSym "timeout"          "Context.Terminal.Event.timeout"            .conSym      "AgdaMirror.Context.TermEvent.timeout" .unrelated 1
  , mkSym "Effect"           "Context.Terminal.Effect"                   .typeSym     "AgdaMirror.Context.Effect"
  , mkSym "effect"           "Context.Terminal.effect"                   .conSym      "AgdaMirror.Context.Effect.effect" .unrelated 3
  , mkSym "nextState"        "Context.Terminal.Effect.nextState"         (.projSym 2) "AgdaMirror.Context.Effect.nextState"
  , mkSym "output"           "Context.Terminal.Effect.output"            (.projSym 2) "AgdaMirror.Context.Effect.output"
  , mkSym "edits"            "Context.Terminal.Effect.edits"             (.projSym 2) "AgdaMirror.Context.Effect.edits"
  , mkSym "TimedMachine"     "Context.Terminal.TimedMachine"             .typeSym     "AgdaMirror.Context.TimedMachine"
  , mkSym "timed"            "Context.Terminal.timed"                    .conSym      "AgdaMirror.Context.TimedMachine.timed" .unrelated 4
  , mkSym "now"              "Context.Terminal.TimedMachine.now"         (.projSym 2) "AgdaMirror.Context.TimedMachine.now"
  , mkSym "state"            "Context.Terminal.TimedMachine.state"       (.projSym 2) "AgdaMirror.Context.TimedMachine.state"
  , mkSym "timers"           "Context.Terminal.TimedMachine.timers"      (.projSym 2) "AgdaMirror.Context.TimedMachine.timers"
  , mkSym "pending"          "Context.Terminal.TimedMachine.pending"     (.projSym 2) "AgdaMirror.Context.TimedMachine.pending"
  , mkSym "Handler"          "Context.Terminal.Handler"                  .typeSym     "AgdaMirror.Context.Handler"
  , mkSym "removeTimer"      "Context.Terminal.removeTimer"              .defSym      "AgdaMirror.Context.removeTimer"
  , mkSym "insertTimer"      "Context.Terminal.insertTimer"              .defSym      "AgdaMirror.Context.insertTimer"
  , mkSym "editTimers"       "Context.Terminal.editTimers"               .defSym      "AgdaMirror.Context.editTimers"
  , mkSym "applyEffect"      "Context.Terminal.applyEffect"              .defSym      "AgdaMirror.Context.applyEffect"
  , mkSym "fireDue"          "Context.Terminal.fireDue"                  .defSym      "AgdaMirror.Context.fireDue"
  , mkSym "advance"          "Context.Terminal.advance"                  .defSym      "AgdaMirror.Context.advance"
  , mkSym "perform"          "Context.Terminal.perform"                  .defSym      "AgdaMirror.Context.perform"
  , mkSym "observe"          "Context.Terminal.observe"                  .defSym      "AgdaMirror.Context.observe"
  , mkSym "stepTimed"        "Context.Terminal.stepTimed"                .defSym      "AgdaMirror.Context.stepTimed"
  , mkSym "traceTimed"       "Context.Terminal.traceTimed"               .defSym      "AgdaMirror.Context.traceTimed"
  , mkSym "Colour"           "Context.Terminal.Colour"                   .typeSym     "AgdaMirror.Context.Colour"
  , mkSym "defaultColour"    "Context.Terminal.Colour.defaultColour"     .conSym      "AgdaMirror.Context.Colour.defaultColour" .unrelated 0
  , mkSym "indexed"          "Context.Terminal.Colour.indexed"           .conSym      "AgdaMirror.Context.Colour.indexed"       .unrelated 1
  , mkSym "rgb"              "Context.Terminal.Colour.rgb"               .conSym      "AgdaMirror.Context.Colour.rgb"           .unrelated 3
  , mkSym "Rendition"        "Context.Terminal.Rendition"                .typeSym     "AgdaMirror.Context.Rendition"
  , mkSym "rendition"        "Context.Terminal.rendition"                .conSym      "AgdaMirror.Context.Rendition.rendition"  .unrelated 5
  , mkSym "foreground"       "Context.Terminal.Rendition.foreground"     (.projSym 0) "AgdaMirror.Context.Rendition.foreground"
  , mkSym "background"       "Context.Terminal.Rendition.background"     (.projSym 0) "AgdaMirror.Context.Rendition.background"
  , mkSym "bold"             "Context.Terminal.Rendition.bold"           (.projSym 0) "AgdaMirror.Context.Rendition.bold"
  , mkSym "underline"        "Context.Terminal.Rendition.underline"      (.projSym 0) "AgdaMirror.Context.Rendition.underline"
  , mkSym "inverse"          "Context.Terminal.Rendition.inverse"        (.projSym 0) "AgdaMirror.Context.Rendition.inverse"
  , mkSym "plain"            "Context.Terminal.plain"                    .defSym      "AgdaMirror.Context.plain"
  , mkSym "Cell"             "Context.Terminal.Cell"                     .typeSym     "AgdaMirror.Context.Cell"
  , mkSym "cell"             "Context.Terminal.cell"                     .conSym      "AgdaMirror.Context.Cell.cell" .unrelated 2
  , mkSym "glyph"            "Context.Terminal.Cell.glyph"               (.projSym 0) "AgdaMirror.Context.Cell.glyph"
  , mkSym "style"            "Context.Terminal.Cell.style"               (.projSym 0) "AgdaMirror.Context.Cell.style"
  , mkSym "Surface"          "Context.Terminal.Surface"                  .typeSym     "AgdaMirror.Context.Surface"
  , mkSym "surface"          "Context.Terminal.surface"                  .conSym      "AgdaMirror.Context.Surface.surface" .unrelated 5
  , mkSym "grid"             "Context.Terminal.Surface.grid"             (.projSym 0) "AgdaMirror.Context.Surface.grid"
  , mkSym "row"              "Context.Terminal.Surface.row"              (.projSym 0) "AgdaMirror.Context.Surface.row"
  , mkSym "col"              "Context.Terminal.Surface.col"              (.projSym 0) "AgdaMirror.Context.Surface.col"
  , mkSym "ink"              "Context.Terminal.Surface.ink"              (.projSym 0) "AgdaMirror.Context.Surface.ink"
  , mkSym "wrapPending"      "Context.Terminal.Surface.wrapPending"      (.projSym 0) "AgdaMirror.Context.Surface.wrapPending"
  , mkSym "Parser"           "Context.Terminal.Parser"                   .typeSym     "AgdaMirror.Context.TermParser"
  , mkSym "ground"           "Context.Terminal.Parser.ground"            .conSym      "AgdaMirror.Context.TermParser.ground"    .unrelated 0
  , mkSym "escaped"          "Context.Terminal.Parser.escaped"           .conSym      "AgdaMirror.Context.TermParser.escaped"   .unrelated 0
  , mkSym "osc"              "Context.Terminal.Parser.osc"               .conSym      "AgdaMirror.Context.TermParser.osc"       .unrelated 0
  , mkSym "oscEscape"        "Context.Terminal.Parser.oscEscape"         .conSym      "AgdaMirror.Context.TermParser.oscEscape" .unrelated 0
  , mkSym "csi"              "Context.Terminal.Parser.csi"               .conSym      "AgdaMirror.Context.TermParser.csi"       .unrelated 3
  , mkSym "utf"              "Context.Terminal.Parser.utf"               .conSym      "AgdaMirror.Context.TermParser.utf"       .unrelated 2
  , mkSym "Screen"           "Context.Terminal.Screen"                   .typeSym     "AgdaMirror.Context.Screen"
  , mkSym "screen"           "Context.Terminal.screen"                   .conSym      "AgdaMirror.Context.Screen.screen" .unrelated 5
  , mkSym "height"           "Context.Terminal.Screen.height"            (.projSym 0) "AgdaMirror.Context.Screen.height"
  , mkSym "width"            "Context.Terminal.Screen.width"             (.projSym 0) "AgdaMirror.Context.Screen.width"
  , mkSym "active"           "Context.Terminal.Screen.active"            (.projSym 0) "AgdaMirror.Context.Screen.active"
  , mkSym "primary"          "Context.Terminal.Screen.primary"           (.projSym 0) "AgdaMirror.Context.Screen.primary"
  , mkSym "parser"           "Context.Terminal.Screen.parser"            (.projSym 0) "AgdaMirror.Context.Screen.parser"
  , mkSym "blankSurface"     "Context.Terminal.blankSurface"             .defSym      "AgdaMirror.Context.blankSurface"
  , mkSym "blankScreen"      "Context.Terminal.blankScreen"              .defSym      "AgdaMirror.Context.blankScreen"
  , mkSym "putAt"            "Context.Terminal.putAt"                    .defSym      "AgdaMirror.Context.putAt"
  , mkSym "getAt"            "Context.Terminal.getAt"                    .defSym      "AgdaMirror.Context.getAt"
  , mkSym "move"             "Context.Terminal.move"                     .defSym      "AgdaMirror.Context.move"
  , mkSym "lineFeed"         "Context.Terminal.lineFeed"                 .defSym      "AgdaMirror.Context.lineFeed"
  , mkSym "printGlyph"       "Context.Terminal.printGlyph"               .defSym      "AgdaMirror.Context.printGlyph"
  , mkSym "mapIndexed"       "Context.Terminal.mapIndexed"               .defSym      "AgdaMirror.Context.mapIndexed"
  , mkSym "erase"            "Context.Terminal.erase"                    .defSym      "AgdaMirror.Context.erase"
  , mkSym "sgrOne"           "Context.Terminal.sgrOne"                   .defSym      "AgdaMirror.Context.sgrOne"
  , mkSym "setColour"        "Context.Terminal.setColour"                .defSym      "AgdaMirror.Context.setColour"
  , mkSym "sgrFuel"          "Context.Terminal.sgrFuel"                  .defSym      "AgdaMirror.Context.sgrFuel"
  , mkSym "sgr"              "Context.Terminal.sgr"                      .defSym      "AgdaMirror.Context.sgr"
  , mkSym "altScreen"        "Context.Terminal.altScreen"                .defSym      "AgdaMirror.Context.altScreen"
  , mkSym "dispatchCSI"      "Context.Terminal.dispatchCSI"              .defSym      "AgdaMirror.Context.dispatchCSI"
  , mkSym "groundByte"       "Context.Terminal.groundByte"               .defSym      "AgdaMirror.Context.groundByte"
  , mkSym "ansiByte"         "Context.Terminal.ansiByte"                 .defSym      "AgdaMirror.Context.ansiByte"
  , mkSym "stepANSI"         "Context.Terminal.stepANSI"                 .defSym      "AgdaMirror.Context.stepANSI"
  , mkSym "screenLines"      "Context.Terminal.screenLines"              .defSym      "AgdaMirror.Context.screenLines"
  ]

def filterExports : List SymInfo :=
  [ mkSym "Mode"        "Context.Filter.Mode"             .typeSym "AgdaMirror.Context.Filter.Mode"
  , mkSym "sensitive"   "Context.Filter.Mode.sensitive"   .conSym  "AgdaMirror.Context.Filter.Mode.sensitive"   .unrelated 0
  , mkSym "insensitive" "Context.Filter.Mode.insensitive" .conSym  "AgdaMirror.Context.Filter.Mode.insensitive" .unrelated 0
  , mkSym "Kind"        "Context.Filter.Kind"             .typeSym "AgdaMirror.Context.Filter.Kind"
  , mkSym "prefix"      "Context.Filter.Kind.prefix"      .conSym  "AgdaMirror.Context.Filter.Kind.prefix"      .unrelated 0
  , mkSym "suffix"      "Context.Filter.Kind.suffix"      .conSym  "AgdaMirror.Context.Filter.Kind.suffix"      .unrelated 0
  , mkSym "exclude"     "Context.Filter.Kind.exclude"     .conSym  "AgdaMirror.Context.Filter.Kind.exclude"     .unrelated 0
  , mkSym "Signal"      "Context.Filter.Signal"           .typeSym "AgdaMirror.Context.Filter.Signal"
  , mkSym "signal"      "Context.Filter.signal"           .conSym  "AgdaMirror.Context.Filter.Signal.signal"    .unrelated 3
  , mkSym "kind"        "Context.Filter.Signal.kind"      (.projSym 0) "AgdaMirror.Context.Filter.Signal.kind"
  , mkSym "exact"       "Context.Filter.Signal.exact"     (.projSym 0) "AgdaMirror.Context.Filter.Signal.exact"
  , mkSym "folded"      "Context.Filter.Signal.folded"    (.projSym 0) "AgdaMirror.Context.Filter.Signal.folded"
  , mkSym "Input"       "Context.Filter.Input"            .typeSym "AgdaMirror.Context.Filter.Input"
  , mkSym "input"       "Context.Filter.input"            .conSym  "AgdaMirror.Context.Filter.Input.input"      .unrelated 3
  , mkSym "operation"   "Context.Filter.Input.operation"  (.projSym 0) "AgdaMirror.Context.Filter.Input.operation"
  , mkSym "needle"      "Context.Filter.Input.needle"     (.projSym 0) "AgdaMirror.Context.Filter.Input.needle"
  , mkSym "text"        "Context.Filter.Input.text"       (.projSym 0) "AgdaMirror.Context.Filter.Input.text"
  , mkSym "starts"      "Context.Filter.starts"           .defSym  "AgdaMirror.Context.Filter.starts"
  , mkSym "contains"    "Context.Filter.contains"         .defSym  "AgdaMirror.Context.Filter.contains"
  , mkSym "hit"         "Context.Filter.hit"              .defSym  "AgdaMirror.Context.Filter.hit"
  , mkSym "classify"    "Context.Filter.classify"         .defSym  "AgdaMirror.Context.Filter.classify"
  , mkSym "choose"      "Context.Filter.choose"           .defSym  "AgdaMirror.Context.Filter.choose"
  , mkSym "combine"     "Context.Filter.combine"          .defSym  "AgdaMirror.Context.Filter.combine"
  , mkSym "expected0"   "Context.Filter.expected0"        .defSym  "AgdaMirror.Context.Filter.expected0"
  , mkSym "expected1"   "Context.Filter.expected1"        .defSym  "AgdaMirror.Context.Filter.expected1"
  , mkSym "inputPort"   "Context.Filter.inputPort"        .defSym  "AgdaMirror.Context.Filter.inputPort"
  ]

def ioExports : List SymInfo :=
  [ mkSym "IO"             "IO.Base.IO"               .typeSym "AgdaMirror.AgdaIO"
  , mkSym "Main"           "IO.Base.Main"             .typeSym "(AgdaMirror.AgdaIO AgdaMirror.PolyTop)"
  , mkSym "run"            "IO.Base.run"              .defSym  "(fun x => x)"
  , mkSym "lift"           "IO.Base.IO.lift"          .conSym  "(fun x => x)" .unrelated 1
  , mkSym "putStr"         "IO.Finite.putStr"         .defSym  "AgdaMirror.agdaPutStr"
  , mkSym "putStrLn"       "IO.Finite.putStrLn"       .defSym  "AgdaMirror.agdaPutStrLn"
  , mkSym "readFiniteFile" "IO.Finite.readFile"        .defSym  "AgdaMirror.agdaReadFiniteFile"
  , mkSym "pure"           "IO.Base.pure"              .defSym  "AgdaMirror.agdaIOPure"
  , mkSym "_>>=_"          "IO.Base._._>>=_"           .defSym  "AgdaMirror.agdaIOBind" (.related 1 .infixL)
  , mkSym "_>>_"           "IO.Base._._>>_"            .defSym  "AgdaMirror.agdaIOSeq"  (.related 1 .infixL)
  ]

def primIOExports : List SymInfo :=
  [ mkSym "IO"     "Agda.Builtin.IO.IO"  .typeSym "AgdaMirror.AgdaIO"
  , mkSym "return" "IO.Primitive.return" .defSym  "AgdaMirror.agdaIOPure"
  , mkSym "_>>=_"  "IO.Primitive._>>=_"  .defSym  "AgdaMirror.agdaIOBind" (.related 1 .infixL)
  ]

def primFiniteIOExports : List SymInfo :=
  [ mkSym "putStr"    "IO.Primitive.Finite.putStr"    .defSym "AgdaMirror.agdaPutStr0"
  , mkSym "putStrLn"  "IO.Primitive.Finite.putStrLn"  .defSym "AgdaMirror.agdaPutStrLn0"
  , mkSym "readFile"  "IO.Primitive.Finite.readFile"  .defSym "AgdaMirror.agdaReadFiniteFile"
  , mkSym "writeFile" "IO.Primitive.Finite.writeFile" .defSym "AgdaMirror.agdaWriteFile"
  ]

def sysEnvExports : List SymInfo :=
  [ mkSym "getArgs"   "System.Environment.getArgs"   .defSym "AgdaMirror.agdaGetArgs"
  , mkSym "lookupEnv" "System.Environment.lookupEnv" .defSym "AgdaMirror.agdaLookupEnv"
  ]

def primSysEnvExports : List SymInfo :=
  [ mkSym "getArgs"   "System.Environment.Primitive.getArgs"   .defSym "AgdaMirror.agdaGetArgs"
  , mkSym "lookupEnv" "System.Environment.Primitive.lookupEnv" .defSym "AgdaMirror.agdaLookupEnv"
  ]

def ffiSafeExports : List SymInfo :=
  [ mkSym "readStdin"           "OwnershipIO.FFI.readStdin"           .defSym "AgdaMirror.agdaReadStdin"
  , mkSym "exitFailure"         "OwnershipIO.FFI.exitFailure"         .defSym "AgdaMirror.agdaExitFailure0"
  , mkSym "runPrismCatSelfChecks" "OwnershipIO.FFI.runPrismCatSelfChecks" .defSym "AgdaMirror.agdaRunPrismCatSelfChecks"
  , mkSym "enableLineBuffering" "OwnershipIO.FFI.enableLineBuffering" .defSym "AgdaMirror.agdaEnableLineBuffering"
  ]

def worldRunnerExports : List SymInfo :=
  [ mkSym "runWorldIO"    "OwnershipIO.WorldRunner.runWorldIO"    .defSym "AgdaMirror.WorldRunner.runWorldIO"
  , mkSym "runCliIO"      "OwnershipIO.WorldRunner.runCliIO"      .defSym "AgdaMirror.WorldRunner.runCliIO"
  , mkSym "runReactiveIO" "OwnershipIO.WorldRunner.runReactiveIO" .defSym "AgdaMirror.WorldRunner.runReactiveIO"
  ]

def clockExports : List SymInfo :=
  [ mkSym "SimClock"          "Context.Tools.Clock.SimClock"                    .typeSym     "AgdaMirror.Clock.SimClock"
  , mkSym "simClock"          "Context.Tools.Clock.simClock"                    .conSym      "AgdaMirror.Clock.SimClock.simClock" .unrelated 3
  , mkSym "monoMs"            "Context.Tools.Clock.SimClock.monoMs"             (.projSym 0) "AgdaMirror.Clock.SimClock.monoMs"
  , mkSym "wallEpochMs"       "Context.Tools.Clock.SimClock.wallEpochMs"        (.projSym 0) "AgdaMirror.Clock.SimClock.wallEpochMs"
  , mkSym "autoTicks"         "Context.Tools.Clock.SimClock.autoTicks"          (.projSym 0) "AgdaMirror.Clock.SimClock.autoTicks"
  , mkSym "initClock"         "Context.Tools.Clock.initClock"                   .defSym      "AgdaMirror.Clock.initClock"
  , mkSym "zeroClock"         "Context.Tools.Clock.zeroClock"                   .defSym      "AgdaMirror.Clock.zeroClock"
  , mkSym "fixedStepClock"    "Context.Tools.Clock.fixedStepClock"              .defSym      "AgdaMirror.Clock.fixedStepClock"
  , mkSym "popTick"           "Context.Tools.Clock.popTick"                     .defSym      "AgdaMirror.Clock.popTick"
  , mkSym "advanceClock"      "Context.Tools.Clock.advanceClock"                .defSym      "AgdaMirror.Clock.advanceClock"
  , mkSym "tickClock"         "Context.Tools.Clock.tickClock"                   .defSym      "AgdaMirror.Clock.tickClock"
  , mkSym "readMonoMs"        "Context.Tools.Clock.readMonoMs"                  .defSym      "AgdaMirror.Clock.readMonoMs"
  , mkSym "readWallMs"        "Context.Tools.Clock.readWallMs"                  .defSym      "AgdaMirror.Clock.readWallMs"
  , mkSym "sleepClockMs"      "Context.Tools.Clock.sleepClockMs"                .defSym      "AgdaMirror.Clock.sleepClockMs"
  , mkSym "deadlineReached"   "Context.Tools.Clock.deadlineReached"             .defSym      "AgdaMirror.Clock.deadlineReached"
  , mkSym "remainingMs"       "Context.Tools.Clock.remainingMs"                 .defSym      "AgdaMirror.Clock.remainingMs"
  , mkSym "withTimeoutClock"  "Context.Tools.Clock.withTimeoutClock"            .defSym      "AgdaMirror.Clock.withTimeoutClock"
  , mkSym "ClockStep"         "Context.Tools.Clock.ClockStep"                   .typeSym     "AgdaMirror.Clock.ClockStep"
  , mkSym "stepNowMono"       "Context.Tools.Clock.ClockStep.stepNowMono"       .conSym      "AgdaMirror.Clock.ClockStep.stepNowMono"       .unrelated 0
  , mkSym "stepNowWall"       "Context.Tools.Clock.ClockStep.stepNowWall"       .conSym      "AgdaMirror.Clock.ClockStep.stepNowWall"       .unrelated 0
  , mkSym "stepSleepMs"       "Context.Tools.Clock.ClockStep.stepSleepMs"       .conSym      "AgdaMirror.Clock.ClockStep.stepSleepMs"       .unrelated 1
  , mkSym "stepCheckDeadline" "Context.Tools.Clock.ClockStep.stepCheckDeadline" .conSym      "AgdaMirror.Clock.ClockStep.stepCheckDeadline" .unrelated 1
  , mkSym "RawClockObs"       "Context.Tools.Clock.RawClockObs"                 .typeSym     "AgdaMirror.Clock.RawClockObs"
  , mkSym "rawClockObs"       "Context.Tools.Clock.rawClockObs"                 .conSym      "AgdaMirror.Clock.RawClockObs.rawClockObs" .unrelated 2
  , mkSym "observedMs"        "Context.Tools.Clock.RawClockObs.observedMs"      (.projSym 0) "AgdaMirror.Clock.RawClockObs.observedMs"
  , mkSym "expired"           "Context.Tools.Clock.RawClockObs.expired"         (.projSym 0) "AgdaMirror.Clock.RawClockObs.expired"
  , mkSym "stepSimClock"      "Context.Tools.Clock.stepSimClock"                .defSym      "AgdaMirror.Clock.stepSimClock"
  , mkSym "traceSimClock"     "Context.Tools.Clock.traceSimClock"               .defSym      "AgdaMirror.Clock.traceSimClock"
  ]

def clockLawsExports : List SymInfo :=
  [ mkSym "advanceClock-zero"  "Context.Tools.ClockLaws.advanceClock-zero"  .defSym "AgdaMirror.Clock.advanceClockZero"
  , mkSym "advanceClock-add"   "Context.Tools.ClockLaws.advanceClock-add"   .defSym "AgdaMirror.Clock.advanceClockAdd"
  , mkSym "advanceClock-comm"  "Context.Tools.ClockLaws.advanceClock-comm"  .defSym "AgdaMirror.Clock.advanceClockComm"
  , mkSym "advanceClock-mono≤" "Context.Tools.ClockLaws.advanceClock-mono≤" .defSym "AgdaMirror.Clock.advanceClockMonoLe"
  , mkSym "advanceClock-wall≤" "Context.Tools.ClockLaws.advanceClock-wall≤" .defSym "AgdaMirror.Clock.advanceClockWallLe"
  , mkSym "advanceClock-ticks" "Context.Tools.ClockLaws.advanceClock-ticks" .defSym "AgdaMirror.Clock.advanceClockTicks"
  , mkSym "readMono-monotonic" "Context.Tools.ClockLaws.readMono-monotonic" .defSym "AgdaMirror.Clock.readMonoMonotonic"
  , mkSym "readWall-monotonic" "Context.Tools.ClockLaws.readWall-monotonic" .defSym "AgdaMirror.Clock.readWallMonotonic"
  , mkSym "readMono-idle"      "Context.Tools.ClockLaws.readMono-idle"      .defSym "AgdaMirror.Clock.readMonoIdle"
  , mkSym "sleepClock-zero"    "Context.Tools.ClockLaws.sleepClock-zero"    .defSym "AgdaMirror.Clock.sleepClockZero"
  , mkSym "sleepClock-add"     "Context.Tools.ClockLaws.sleepClock-add"     .defSym "AgdaMirror.Clock.sleepClockAdd"
  , mkSym "foldClockSteps"     "Context.Tools.ClockLaws.foldClockSteps"     .defSym "AgdaMirror.Clock.foldClockSteps"
  , mkSym "traceSimClock-++"   "Context.Tools.ClockLaws.traceSimClock-++"   .defSym "AgdaMirror.Clock.traceSimClockAppend"
  ]

def termLawsExports : List SymInfo :=
  [ mkSym "foldl-++"               "Context.Tools.TermLaws.foldl-++"               .defSym "AgdaMirror.TermLaws.foldlAppend"
  , mkSym "stepANSI-[]"            "Context.Tools.TermLaws.stepANSI-[]"            .defSym "AgdaMirror.TermLaws.stepANSINil"
  , mkSym "stepANSI-∷"             "Context.Tools.TermLaws.stepANSI-∷"             .defSym "AgdaMirror.TermLaws.stepANSICons"
  , mkSym "stepANSI-++"            "Context.Tools.TermLaws.stepANSI-++"            .defSym "AgdaMirror.TermLaws.stepANSIAppend"
  , mkSym "latest-nothing-left"    "Context.Tools.TermLaws.latest-nothing-left"    .defSym "AgdaMirror.TermLaws.latestNothingLeft"
  , mkSym "latest-nothing-right"   "Context.Tools.TermLaws.latest-nothing-right"   .defSym "AgdaMirror.TermLaws.latestNothingRight"
  , mkSym "latest-assoc"           "Context.Tools.TermLaws.latest-assoc"           .defSym "AgdaMirror.TermLaws.latestAssoc"
  , mkSym "appendObs-empty-left"   "Context.Tools.TermLaws.appendObs-empty-left"   .defSym "AgdaMirror.TermLaws.appendObsEmptyLeft"
  , mkSym "appendObs-empty-right"  "Context.Tools.TermLaws.appendObs-empty-right"  .defSym "AgdaMirror.TermLaws.appendObsEmptyRight"
  , mkSym "appendObs-assoc"        "Context.Tools.TermLaws.appendObs-assoc"        .defSym "AgdaMirror.TermLaws.appendObsAssoc"
  , mkSym "advance-zero"           "Context.Tools.TermLaws.advance-zero"           .defSym "AgdaMirror.TermLaws.advanceZero"
  , mkSym "advance-+"              "Context.Tools.TermLaws.advance-+"              .defSym "AgdaMirror.TermLaws.advanceAdd"
  , mkSym "altScreen-roundtrip"    "Context.Tools.TermLaws.altScreen-roundtrip"    .defSym "AgdaMirror.TermLaws.altScreenRoundtrip"
  ]

def fuzzGenExports : List SymInfo :=
  [ mkSym "Seed"         "Context.Tools.FuzzGen.Seed"        .typeSym     "AgdaMirror.FuzzGen.Seed"
  , mkSym "seed"         "Context.Tools.FuzzGen.seed"        .conSym      "AgdaMirror.FuzzGen.Seed.seed" .unrelated 1
  , mkSym "state"        "Context.Tools.FuzzGen.Seed.state"  (.projSym 0) "AgdaMirror.FuzzGen.Seed.state"
  , mkSym "mkSeed"       "Context.Tools.FuzzGen.mkSeed"      .defSym      "AgdaMirror.FuzzGen.mkSeed"
  , mkSym "nextNat"      "Context.Tools.FuzzGen.nextNat"     .defSym      "AgdaMirror.FuzzGen.nextNat"
  , mkSym "Gen"          "Context.Tools.FuzzGen.Gen"         .typeSym     "AgdaMirror.FuzzGen.Gen"
  , mkSym "runGen"       "Context.Tools.FuzzGen.runGen"      .defSym      "AgdaMirror.FuzzGen.runGen"
  , mkSym "genPure"      "Context.Tools.FuzzGen.genPure"     .defSym      "AgdaMirror.FuzzGen.genPure"
  , mkSym "genMap"       "Context.Tools.FuzzGen.genMap"      .defSym      "AgdaMirror.FuzzGen.genMap"
  , mkSym "genBind"      "Context.Tools.FuzzGen.genBind"     .defSym      "AgdaMirror.FuzzGen.genBind"
  , mkSym "genPair"      "Context.Tools.FuzzGen.genPair"     .defSym      "AgdaMirror.FuzzGen.genPair"
  , mkSym "genBounded"   "Context.Tools.FuzzGen.genBounded"  .defSym      "AgdaMirror.FuzzGen.genBounded"
  , mkSym "genBool"      "Context.Tools.FuzzGen.genBool"     .defSym      "AgdaMirror.FuzzGen.genBool"
  , mkSym "genByte"      "Context.Tools.FuzzGen.genByte"     .defSym      "AgdaMirror.FuzzGen.genByte"
  , mkSym "genList"      "Context.Tools.FuzzGen.genList"     .defSym      "AgdaMirror.FuzzGen.genList"
  , mkSym "genBytes"     "Context.Tools.FuzzGen.genBytes"    .defSym      "AgdaMirror.FuzzGen.genBytes"
  , mkSym "chooseAt"     "Context.Tools.FuzzGen.chooseAt"    .defSym      "AgdaMirror.FuzzGen.chooseAt"
  , mkSym "genChoose"    "Context.Tools.FuzzGen.genChoose"   .defSym      "AgdaMirror.FuzzGen.genChoose"
  , mkSym "sampleMany"   "Context.Tools.FuzzGen.sampleMany"  .defSym      "AgdaMirror.FuzzGen.sampleMany"
  , mkSym "Shrinker"     "Context.Tools.FuzzGen.Shrinker"    .typeSym     "AgdaMirror.FuzzGen.Shrinker"
  , mkSym "shrinkNat"    "Context.Tools.FuzzGen.shrinkNat"   .defSym      "AgdaMirror.FuzzGen.shrinkNat"
  , mkSym "shrinkByte"   "Context.Tools.FuzzGen.shrinkByte"  .defSym      "AgdaMirror.FuzzGen.shrinkByte"
  , mkSym "shrinkList"   "Context.Tools.FuzzGen.shrinkList"  .defSym      "AgdaMirror.FuzzGen.shrinkList"
  , mkSym "shrinkBytes"  "Context.Tools.FuzzGen.shrinkBytes" .defSym      "AgdaMirror.FuzzGen.shrinkBytes"
  , mkSym "firstFailure" "Context.Tools.FuzzGen.firstFailure" .defSym     "AgdaMirror.FuzzGen.firstFailure"
  , mkSym "minimize"     "Context.Tools.FuzzGen.minimize"    .defSym      "AgdaMirror.FuzzGen.minimize"
  , mkSym "fuzzCheck"    "Context.Tools.FuzzGen.fuzzCheck"   .defSym      "AgdaMirror.FuzzGen.fuzzCheck"
  ]

def fsSandboxExports : List SymInfo :=
  [ mkSym "eqChars"           "Context.Tools.FsSandbox.eqChars"                  .defSym      "AgdaMirror.FsSandbox.eqChars"
  , mkSym "eqStr"             "Context.Tools.FsSandbox.eqStr"                    .defSym      "AgdaMirror.FsSandbox.eqStr"
  , mkSym "splitSegmentChars" "Context.Tools.FsSandbox.splitSegmentChars"        .defSym      "AgdaMirror.FsSandbox.splitSegmentChars"
  , mkSym "segments"          "Context.Tools.FsSandbox.segments"                 .defSym      "AgdaMirror.FsSandbox.segments"
  , mkSym "all"               "Context.Tools.FsSandbox.all"                      .defSym      "AgdaMirror.FsSandbox.all"
  , mkSym "validSegChars"     "Context.Tools.FsSandbox.validSegChars"            .defSym      "AgdaMirror.FsSandbox.validSegChars"
  , mkSym "validSegment"      "Context.Tools.FsSandbox.validSegment"             .defSym      "AgdaMirror.FsSandbox.validSegment"
  , mkSym "validRelPath"      "Context.Tools.FsSandbox.validRelPath"             .defSym      "AgdaMirror.FsSandbox.validRelPath"
  , mkSym "eqBytes"           "Context.Tools.FsSandbox.eqBytes"                  .defSym      "AgdaMirror.FsSandbox.eqBytes"
  , mkSym "ltBytes"           "Context.Tools.FsSandbox.ltBytes"                  .defSym      "AgdaMirror.FsSandbox.ltBytes"
  , mkSym "prefixBytes"       "Context.Tools.FsSandbox.prefixBytes"              .defSym      "AgdaMirror.FsSandbox.prefixBytes"
  , mkSym "isParent"          "Context.Tools.FsSandbox.isParent"                 .defSym      "AgdaMirror.FsSandbox.isParent"
  , mkSym "collide"           "Context.Tools.FsSandbox.collide"                  .defSym      "AgdaMirror.FsSandbox.collide"
  , mkSym "noPathCollisions"  "Context.Tools.FsSandbox.noPathCollisions"         .defSym      "AgdaMirror.FsSandbox.noPathCollisions"
  , mkSym "maskMode"          "Context.Tools.FsSandbox.maskMode"                 .defSym      "AgdaMirror.FsSandbox.maskMode"
  , mkSym "FsNodeKind"        "Context.Tools.FsSandbox.FsNodeKind"               .typeSym     "AgdaMirror.FsSandbox.FsNodeKind"
  , mkSym "regularNode"       "Context.Tools.FsSandbox.FsNodeKind.regularNode"   .conSym      "AgdaMirror.FsSandbox.FsNodeKind.regularNode" .unrelated 0
  , mkSym "dirNode"           "Context.Tools.FsSandbox.FsNodeKind.dirNode"       .conSym      "AgdaMirror.FsSandbox.FsNodeKind.dirNode"     .unrelated 0
  , mkSym "symlinkNode"       "Context.Tools.FsSandbox.FsNodeKind.symlinkNode"   .conSym      "AgdaMirror.FsSandbox.FsNodeKind.symlinkNode" .unrelated 0
  , mkSym "FsFixture"         "Context.Tools.FsSandbox.FsFixture"                .typeSym     "AgdaMirror.FsSandbox.FsFixture"
  , mkSym "fixDir"            "Context.Tools.FsSandbox.FsFixture.fixDir"         .conSym      "AgdaMirror.FsSandbox.FsFixture.fixDir"     .unrelated 2
  , mkSym "fixFile"           "Context.Tools.FsSandbox.FsFixture.fixFile"        .conSym      "AgdaMirror.FsSandbox.FsFixture.fixFile"    .unrelated 3
  , mkSym "fixSymlink"        "Context.Tools.FsSandbox.FsFixture.fixSymlink"     .conSym      "AgdaMirror.FsSandbox.FsFixture.fixSymlink" .unrelated 2
  , mkSym "FsConfig"          "Context.Tools.FsSandbox.FsConfig"                 .typeSym     "AgdaMirror.FsSandbox.FsConfig"
  , mkSym "fsConfig"          "Context.Tools.FsSandbox.fsConfig"                 .conSym      "AgdaMirror.FsSandbox.FsConfig.fsConfig" .unrelated 4
  , mkSym "target"            "Context.Tools.FsSandbox.FsConfig.target"          (.projSym 0) "AgdaMirror.FsSandbox.FsConfig.target"
  , mkSym "envVars"           "Context.Tools.FsSandbox.FsConfig.envVars"         (.projSym 0) "AgdaMirror.FsSandbox.FsConfig.envVars"
  , mkSym "ownedFiles"        "Context.Tools.FsSandbox.FsConfig.ownedFiles"      (.projSym 0) "AgdaMirror.FsSandbox.FsConfig.ownedFiles"
  , mkSym "fixtures"          "Context.Tools.FsSandbox.FsConfig.fixtures"        (.projSym 0) "AgdaMirror.FsSandbox.FsConfig.fixtures"
  , mkSym "FsStep"            "Context.Tools.FsSandbox.FsStep"                   .typeSym     "AgdaMirror.FsSandbox.FsStep"
  , mkSym "runCmd"            "Context.Tools.FsSandbox.FsStep.runCmd"            .conSym      "AgdaMirror.FsSandbox.FsStep.runCmd"        .unrelated 4
  , mkSym "writeFileStep"     "Context.Tools.FsSandbox.FsStep.writeFileStep"     .conSym      "AgdaMirror.FsSandbox.FsStep.writeFileStep" .unrelated 2
  , mkSym "mkdirStep"         "Context.Tools.FsSandbox.FsStep.mkdirStep"         .conSym      "AgdaMirror.FsSandbox.FsStep.mkdirStep"     .unrelated 2
  , mkSym "symlinkStep"       "Context.Tools.FsSandbox.FsStep.symlinkStep"       .conSym      "AgdaMirror.FsSandbox.FsStep.symlinkStep"   .unrelated 2
  , mkSym "chmodStep"         "Context.Tools.FsSandbox.FsStep.chmodStep"         .conSym      "AgdaMirror.FsSandbox.FsStep.chmodStep"     .unrelated 2
  , mkSym "unlinkStep"        "Context.Tools.FsSandbox.FsStep.unlinkStep"        .conSym      "AgdaMirror.FsSandbox.FsStep.unlinkStep"    .unrelated 1
  , mkSym "snapshotStep"      "Context.Tools.FsSandbox.FsStep.snapshotStep"      .conSym      "AgdaMirror.FsSandbox.FsStep.snapshotStep"  .unrelated 0
  , mkSym "FsEntryObs"        "Context.Tools.FsSandbox.FsEntryObs"               .typeSym     "AgdaMirror.FsSandbox.FsEntryObs"
  , mkSym "fsEntry"           "Context.Tools.FsSandbox.fsEntry"                  .conSym      "AgdaMirror.FsSandbox.FsEntryObs.fsEntry" .unrelated 4
  , mkSym "entryPath"         "Context.Tools.FsSandbox.FsEntryObs.entryPath"     (.projSym 0) "AgdaMirror.FsSandbox.FsEntryObs.entryPath"
  , mkSym "entryKind"         "Context.Tools.FsSandbox.FsEntryObs.entryKind"     (.projSym 0) "AgdaMirror.FsSandbox.FsEntryObs.entryKind"
  , mkSym "entryMode"         "Context.Tools.FsSandbox.FsEntryObs.entryMode"     (.projSym 0) "AgdaMirror.FsSandbox.FsEntryObs.entryMode"
  , mkSym "entryBytes"        "Context.Tools.FsSandbox.FsEntryObs.entryBytes"    (.projSym 0) "AgdaMirror.FsSandbox.FsEntryObs.entryBytes"
  , mkSym "RawFsObs"          "Context.Tools.FsSandbox.RawFsObs"                 .typeSym     "AgdaMirror.FsSandbox.RawFsObs"
  , mkSym "rawFsObs"          "Context.Tools.FsSandbox.rawFsObs"                 .conSym      "AgdaMirror.FsSandbox.RawFsObs.rawFsObs" .unrelated 5
  , mkSym "stdoutOut"         "Context.Tools.FsSandbox.RawFsObs.stdoutOut"       (.projSym 0) "AgdaMirror.FsSandbox.RawFsObs.stdoutOut"
  , mkSym "stderrOut"         "Context.Tools.FsSandbox.RawFsObs.stderrOut"       (.projSym 0) "AgdaMirror.FsSandbox.RawFsObs.stderrOut"
  , mkSym "exitStatus"        "Context.Tools.FsSandbox.RawFsObs.exitStatus"      (.projSym 0) "AgdaMirror.FsSandbox.RawFsObs.exitStatus"
  , mkSym "timedOut"          "Context.Tools.FsSandbox.RawFsObs.timedOut"        (.projSym 0) "AgdaMirror.FsSandbox.RawFsObs.timedOut"
  , mkSym "entries"           "Context.Tools.FsSandbox.RawFsObs.entries"         (.projSym 0) "AgdaMirror.FsSandbox.RawFsObs.entries"
  , mkSym "emptyFsObs"        "Context.Tools.FsSandbox.emptyFsObs"               .defSym      "AgdaMirror.FsSandbox.emptyFsObs"
  , mkSym "rejectedFsObs"     "Context.Tools.FsSandbox.rejectedFsObs"            .defSym      "AgdaMirror.FsSandbox.rejectedFsObs"
  , mkSym "eqKind"            "Context.Tools.FsSandbox.eqKind"                   .defSym      "AgdaMirror.FsSandbox.eqKind"
  , mkSym "eqEntry"           "Context.Tools.FsSandbox.eqEntry"                  .defSym      "AgdaMirror.FsSandbox.eqEntry"
  , mkSym "eqEntries"         "Context.Tools.FsSandbox.eqEntries"                .defSym      "AgdaMirror.FsSandbox.eqEntries"
  , mkSym "eqExit"            "Context.Tools.FsSandbox.eqExit"                   .defSym      "AgdaMirror.FsSandbox.eqExit"
  , mkSym "eqBool"            "Context.Tools.FsSandbox.eqBool"                   .defSym      "AgdaMirror.FsSandbox.eqBool"
  , mkSym "eqObs"             "Context.Tools.FsSandbox.eqObs"                    .defSym      "AgdaMirror.FsSandbox.eqObs"
  , mkSym "eqTrace"           "Context.Tools.FsSandbox.eqTrace"                  .defSym      "AgdaMirror.FsSandbox.eqTrace"
  , mkSym "VirtualFs"         "Context.Tools.FsSandbox.VirtualFs"                .typeSym     "AgdaMirror.FsSandbox.VirtualFs"
  , mkSym "virtualFs"         "Context.Tools.FsSandbox.virtualFs"                .conSym      "AgdaMirror.FsSandbox.VirtualFs.virtualFs" .unrelated 1
  , mkSym "fsEntries"         "Context.Tools.FsSandbox.VirtualFs.fsEntries"      (.projSym 0) "AgdaMirror.FsSandbox.VirtualFs.fsEntries"
  , mkSym "lookupEntry"       "Context.Tools.FsSandbox.lookupEntry"              .defSym      "AgdaMirror.FsSandbox.lookupEntry"
  , mkSym "insertEntry"       "Context.Tools.FsSandbox.insertEntry"              .defSym      "AgdaMirror.FsSandbox.insertEntry"
  , mkSym "removeEntry"       "Context.Tools.FsSandbox.removeEntry"              .defSym      "AgdaMirror.FsSandbox.removeEntry"
  , mkSym "putEntry"          "Context.Tools.FsSandbox.putEntry"                 .defSym      "AgdaMirror.FsSandbox.putEntry"
  , mkSym "joinPart"          "Context.Tools.FsSandbox.joinPart"                 .defSym      "AgdaMirror.FsSandbox.joinPart"
  , mkSym "parentsFrom"       "Context.Tools.FsSandbox.parentsFrom"              .defSym      "AgdaMirror.FsSandbox.parentsFrom"
  , mkSym "parentPaths"       "Context.Tools.FsSandbox.parentPaths"              .defSym      "AgdaMirror.FsSandbox.parentPaths"
  , mkSym "ensureParents"     "Context.Tools.FsSandbox.ensureParents"            .defSym      "AgdaMirror.FsSandbox.ensureParents"
  , mkSym "prepare"           "Context.Tools.FsSandbox.prepare"                  .defSym      "AgdaMirror.FsSandbox.prepare"
  , mkSym "writeLeaf"         "Context.Tools.FsSandbox.writeLeaf"                .defSym      "AgdaMirror.FsSandbox.writeLeaf"
  , mkSym "mkdirLeaf"         "Context.Tools.FsSandbox.mkdirLeaf"                .defSym      "AgdaMirror.FsSandbox.mkdirLeaf"
  , mkSym "linkLeaf"          "Context.Tools.FsSandbox.linkLeaf"                 .defSym      "AgdaMirror.FsSandbox.linkLeaf"
  , mkSym "chmodLeaf"         "Context.Tools.FsSandbox.chmodLeaf"                .defSym      "AgdaMirror.FsSandbox.chmodLeaf"
  , mkSym "unlinkLeaf"        "Context.Tools.FsSandbox.unlinkLeaf"               .defSym      "AgdaMirror.FsSandbox.unlinkLeaf"
  , mkSym "bindMaybe"         "Context.Tools.FsSandbox.bindMaybe"                .defSym      "AgdaMirror.FsSandbox.bindMaybe"
  , mkSym "applyFs"           "Context.Tools.FsSandbox.applyFs"                  .defSym      "AgdaMirror.FsSandbox.applyFs"
  , mkSym "CmdSemantics"      "Context.Tools.FsSandbox.CmdSemantics"             .typeSym     "AgdaMirror.FsSandbox.CmdSemantics"
  , mkSym "noopCmd"           "Context.Tools.FsSandbox.noopCmd"                  .defSym      "AgdaMirror.FsSandbox.noopCmd"
  , mkSym "finishFs"          "Context.Tools.FsSandbox.finishFs"                 .defSym      "AgdaMirror.FsSandbox.finishFs"
  , mkSym "stepVirtualFs"     "Context.Tools.FsSandbox.stepVirtualFs"            .defSym      "AgdaMirror.FsSandbox.stepVirtualFs"
  , mkSym "traceVirtualFs"    "Context.Tools.FsSandbox.traceVirtualFs"           .defSym      "AgdaMirror.FsSandbox.traceVirtualFs"
  , mkSym "retain"            "Context.Tools.FsSandbox.retain"                   .defSym      "AgdaMirror.FsSandbox.retain"
  , mkSym "initOwned"         "Context.Tools.FsSandbox.initOwned"                .defSym      "AgdaMirror.FsSandbox.initOwned"
  , mkSym "initDirs"          "Context.Tools.FsSandbox.initDirs"                 .defSym      "AgdaMirror.FsSandbox.initDirs"
  , mkSym "initFixtures"      "Context.Tools.FsSandbox.initFixtures"             .defSym      "AgdaMirror.FsSandbox.initFixtures"
  , mkSym "initVirtualFs"     "Context.Tools.FsSandbox.initVirtualFs"            .defSym      "AgdaMirror.FsSandbox.initVirtualFs"
  , mkSym "FsDiff"            "Context.Tools.FsSandbox.FsDiff"                   .typeSym     "AgdaMirror.FsSandbox.FsDiff"
  , mkSym "added"             "Context.Tools.FsSandbox.FsDiff.added"             .conSym      "AgdaMirror.FsSandbox.FsDiff.added"    .unrelated 1
  , mkSym "modified"          "Context.Tools.FsSandbox.FsDiff.modified"          .conSym      "AgdaMirror.FsSandbox.FsDiff.modified" .unrelated 1
  , mkSym "removed"           "Context.Tools.FsSandbox.FsDiff.removed"           .conSym      "AgdaMirror.FsSandbox.FsDiff.removed"  .unrelated 1
  , mkSym "diffSnapshot"      "Context.Tools.FsSandbox.diffSnapshot"             .defSym      "AgdaMirror.FsSandbox.diffSnapshot"
  ]

def fsLawsExports : List SymInfo :=
  [ mkSym "≡ᵇ-refl"                "Context.Tools.FsLaws.≡ᵇ-refl"                .defSym "AgdaMirror.FsLaws.eqbRefl"
  , mkSym "≡ᵇ⇒≡"                  "Context.Tools.FsLaws.≡ᵇ⇒≡"                  .defSym "AgdaMirror.FsLaws.eqbToId"
  , mkSym "≢⇒≡ᵇ≡false"            "Context.Tools.FsLaws.≢⇒≡ᵇ≡false"            .defSym "AgdaMirror.FsLaws.neqToEqbFalse"
  , mkSym "eqBytes-refl"           "Context.Tools.FsLaws.eqBytes-refl"           .defSym "AgdaMirror.FsLaws.eqBytesRefl"
  , mkSym "eqBytes⇒≡"             "Context.Tools.FsLaws.eqBytes⇒≡"             .defSym "AgdaMirror.FsLaws.eqBytesToId"
  , mkSym "eqChars-refl"           "Context.Tools.FsLaws.eqChars-refl"           .defSym "AgdaMirror.FsLaws.eqCharsRefl"
  , mkSym "eqChars⇒≡"             "Context.Tools.FsLaws.eqChars⇒≡"             .defSym "AgdaMirror.FsLaws.eqCharsToId"
  , mkSym "eqStr-refl"             "Context.Tools.FsLaws.eqStr-refl"             .defSym "AgdaMirror.FsLaws.eqStrRefl"
  , mkSym "eqStr⇒≡"               "Context.Tools.FsLaws.eqStr⇒≡"               .defSym "AgdaMirror.FsLaws.eqStrToId"
  , mkSym "≢Str⇒eqStr≡false"      "Context.Tools.FsLaws.≢Str⇒eqStr≡false"      .defSym "AgdaMirror.FsLaws.neqStrToEqStrFalse"
  , mkSym "≢⇒eqStr≡false"         "Context.Tools.FsLaws.≢⇒eqStr≡false"         .defSym "AgdaMirror.FsLaws.neqToEqStrFalse"
  , mkSym "eqStr-sym"              "Context.Tools.FsLaws.eqStr-sym"              .defSym "AgdaMirror.FsLaws.eqStrSym"
  , mkSym "lookup-insert-same"     "Context.Tools.FsLaws.lookup-insert-same"     .defSym "AgdaMirror.FsLaws.lookupInsertSame"
  , mkSym "lookup-insert-other"    "Context.Tools.FsLaws.lookup-insert-other"    .defSym "AgdaMirror.FsLaws.lookupInsertOther"
  , mkSym "insert-insert-same"     "Context.Tools.FsLaws.insert-insert-same"     .defSym "AgdaMirror.FsLaws.insertInsertSame"
  , mkSym "noSlashOrNull"          "Context.Tools.FsLaws.noSlashOrNull"          .defSym "AgdaMirror.FsLaws.noSlashOrNull"
  , mkSym "ValidFlatFile"          "Context.Tools.FsLaws.ValidFlatFile"          .defSym "AgdaMirror.FsLaws.ValidFlatFile"
  , mkSym "isWritableEntry"        "Context.Tools.FsLaws.isWritableEntry"        .defSym "AgdaMirror.FsLaws.isWritableEntry"
  , mkSym "CanWriteReg"            "Context.Tools.FsLaws.CanWriteReg"            .defSym "AgdaMirror.FsLaws.CanWriteReg"
  , mkSym "isNotSymlinkEntry"      "Context.Tools.FsLaws.isNotSymlinkEntry"      .defSym "AgdaMirror.FsLaws.isNotSymlinkEntry"
  , mkSym "NotSymlink"             "Context.Tools.FsLaws.NotSymlink"             .defSym "AgdaMirror.FsLaws.NotSymlink"
  , mkSym "read-after-write-same"  "Context.Tools.FsLaws.read-after-write-same"  .defSym "AgdaMirror.FsLaws.readAfterWriteSame"
  , mkSym "read-after-write-other" "Context.Tools.FsLaws.read-after-write-other" .defSym "AgdaMirror.FsLaws.readAfterWriteOther"
  ]

def netSandboxExports : List SymInfo :=
  [ mkSym "digitChar"            "Context.Tools.NetSandbox.digitChar"                         .defSym      "AgdaMirror.NetSandbox.digitChar"
  , mkSym "decCharsFuel"         "Context.Tools.NetSandbox.decCharsFuel"                      .defSym      "AgdaMirror.NetSandbox.decCharsFuel"
  , mkSym "showDec"              "Context.Tools.NetSandbox.showDec"                           .defSym      "AgdaMirror.NetSandbox.showDec"
  , mkSym "HttpRoute"            "Context.Tools.NetSandbox.HttpRoute"                         .typeSym     "AgdaMirror.NetSandbox.HttpRoute"
  , mkSym "httpRoute"            "Context.Tools.NetSandbox.httpRoute"                         .conSym      "AgdaMirror.NetSandbox.HttpRoute.httpRoute" .unrelated 6
  , mkSym "routeMethod"          "Context.Tools.NetSandbox.HttpRoute.routeMethod"             (.projSym 0) "AgdaMirror.NetSandbox.HttpRoute.routeMethod"
  , mkSym "routePath"            "Context.Tools.NetSandbox.HttpRoute.routePath"               (.projSym 0) "AgdaMirror.NetSandbox.HttpRoute.routePath"
  , mkSym "routeStatus"          "Context.Tools.NetSandbox.HttpRoute.routeStatus"             (.projSym 0) "AgdaMirror.NetSandbox.HttpRoute.routeStatus"
  , mkSym "routeReason"          "Context.Tools.NetSandbox.HttpRoute.routeReason"             (.projSym 0) "AgdaMirror.NetSandbox.HttpRoute.routeReason"
  , mkSym "routeHeaders"         "Context.Tools.NetSandbox.HttpRoute.routeHeaders"            (.projSym 0) "AgdaMirror.NetSandbox.HttpRoute.routeHeaders"
  , mkSym "routeBody"            "Context.Tools.NetSandbox.HttpRoute.routeBody"               (.projSym 0) "AgdaMirror.NetSandbox.HttpRoute.routeBody"
  , mkSym "RawStubRule"          "Context.Tools.NetSandbox.RawStubRule"                       .typeSym     "AgdaMirror.NetSandbox.RawStubRule"
  , mkSym "rawStubRule"          "Context.Tools.NetSandbox.rawStubRule"                       .conSym      "AgdaMirror.NetSandbox.RawStubRule.rawStubRule" .unrelated 2
  , mkSym "matchPrefix"          "Context.Tools.NetSandbox.RawStubRule.matchPrefix"           (.projSym 0) "AgdaMirror.NetSandbox.RawStubRule.matchPrefix"
  , mkSym "replyPayload"         "Context.Tools.NetSandbox.RawStubRule.replyPayload"          (.projSym 0) "AgdaMirror.NetSandbox.RawStubRule.replyPayload"
  , mkSym "NetTopology"          "Context.Tools.NetSandbox.NetTopology"                       .typeSym     "AgdaMirror.NetSandbox.NetTopology"
  , mkSym "httpStubMode"         "Context.Tools.NetSandbox.NetTopology.httpStubMode"          .conSym      "AgdaMirror.NetSandbox.NetTopology.httpStubMode"        .unrelated 1
  , mkSym "tcpStubMode"          "Context.Tools.NetSandbox.NetTopology.tcpStubMode"           .conSym      "AgdaMirror.NetSandbox.NetTopology.tcpStubMode"         .unrelated 1
  , mkSym "udpStubMode"          "Context.Tools.NetSandbox.NetTopology.udpStubMode"           .conSym      "AgdaMirror.NetSandbox.NetTopology.udpStubMode"         .unrelated 1
  , mkSym "daemonProbeMode"      "Context.Tools.NetSandbox.NetTopology.daemonProbeMode"       .conSym      "AgdaMirror.NetSandbox.NetTopology.daemonProbeMode"     .unrelated 2
  , mkSym "httpDelayedStubMode"  "Context.Tools.NetSandbox.NetTopology.httpDelayedStubMode"   .conSym      "AgdaMirror.NetSandbox.NetTopology.httpDelayedStubMode" .unrelated 2
  , mkSym "tcpDelayedStubMode"   "Context.Tools.NetSandbox.NetTopology.tcpDelayedStubMode"    .conSym      "AgdaMirror.NetSandbox.NetTopology.tcpDelayedStubMode"  .unrelated 2
  , mkSym "NetConfig"            "Context.Tools.NetSandbox.NetConfig"                         .typeSym     "AgdaMirror.NetSandbox.NetConfig"
  , mkSym "netConfig"            "Context.Tools.NetSandbox.netConfig"                         .conSym      "AgdaMirror.NetSandbox.NetConfig.netConfig" .unrelated 4
  , mkSym "target"               "Context.Tools.NetSandbox.NetConfig.target"                  (.projSym 0) "AgdaMirror.NetSandbox.NetConfig.target"
  , mkSym "topology"             "Context.Tools.NetSandbox.NetConfig.topology"                (.projSym 0) "AgdaMirror.NetSandbox.NetConfig.topology"
  , mkSym "envVars"              "Context.Tools.NetSandbox.NetConfig.envVars"                 (.projSym 0) "AgdaMirror.NetSandbox.NetConfig.envVars"
  , mkSym "ownedFiles"           "Context.Tools.NetSandbox.NetConfig.ownedFiles"              (.projSym 0) "AgdaMirror.NetSandbox.NetConfig.ownedFiles"
  , mkSym "eqBytes"              "Context.Tools.NetSandbox.eqBytes"                           .defSym      "AgdaMirror.NetSandbox.eqBytes"
  , mkSym "eqByteLists"          "Context.Tools.NetSandbox.eqByteLists"                       .defSym      "AgdaMirror.NetSandbox.eqByteLists"
  , mkSym "prefixBytes"          "Context.Tools.NetSandbox.prefixBytes"                       .defSym      "AgdaMirror.NetSandbox.prefixBytes"
  , mkSym "lower"                "Context.Tools.NetSandbox.lower"                             .defSym      "AgdaMirror.NetSandbox.lower"
  , mkSym "hasHeader"            "Context.Tools.NetSandbox.hasHeader"                         .defSym      "AgdaMirror.NetSandbox.hasHeader"
  , mkSym "headerLines"          "Context.Tools.NetSandbox.headerLines"                       .defSym      "AgdaMirror.NetSandbox.headerLines"
  , mkSym "autoHeader"           "Context.Tools.NetSandbox.autoHeader"                        .defSym      "AgdaMirror.NetSandbox.autoHeader"
  , mkSym "headerBytes"          "Context.Tools.NetSandbox.headerBytes"                       .defSym      "AgdaMirror.NetSandbox.headerBytes"
  , mkSym "autoHeaderBytes"      "Context.Tools.NetSandbox.autoHeaderBytes"                   .defSym      "AgdaMirror.NetSandbox.autoHeaderBytes"
  , mkSym "decBytes"             "Context.Tools.NetSandbox.decBytes"                          .defSym      "AgdaMirror.NetSandbox.decBytes"
  , mkSym "encodeHttpReq"        "Context.Tools.NetSandbox.encodeHttpReq"                     .defSym      "AgdaMirror.NetSandbox.encodeHttpReq"
  , mkSym "encodeHttpResp"       "Context.Tools.NetSandbox.encodeHttpResp"                    .defSym      "AgdaMirror.NetSandbox.encodeHttpResp"
  , mkSym "HttpReqView"          "Context.Tools.NetSandbox.HttpReqView"                       .typeSym     "AgdaMirror.NetSandbox.HttpReqView"
  , mkSym "httpReqView"          "Context.Tools.NetSandbox.httpReqView"                       .conSym      "AgdaMirror.NetSandbox.HttpReqView.httpReqView" .unrelated 3
  , mkSym "reqMethod"            "Context.Tools.NetSandbox.HttpReqView.reqMethod"             (.projSym 0) "AgdaMirror.NetSandbox.HttpReqView.reqMethod"
  , mkSym "reqTarget"            "Context.Tools.NetSandbox.HttpReqView.reqTarget"             (.projSym 0) "AgdaMirror.NetSandbox.HttpReqView.reqTarget"
  , mkSym "reqBody"              "Context.Tools.NetSandbox.HttpReqView.reqBody"               (.projSym 0) "AgdaMirror.NetSandbox.HttpReqView.reqBody"
  , mkSym "HttpRespView"         "Context.Tools.NetSandbox.HttpRespView"                      .typeSym     "AgdaMirror.NetSandbox.HttpRespView"
  , mkSym "httpRespView"         "Context.Tools.NetSandbox.httpRespView"                      .conSym      "AgdaMirror.NetSandbox.HttpRespView.httpRespView" .unrelated 2
  , mkSym "respCode"             "Context.Tools.NetSandbox.HttpRespView.respCode"             (.projSym 0) "AgdaMirror.NetSandbox.HttpRespView.respCode"
  , mkSym "respBody"             "Context.Tools.NetSandbox.HttpRespView.respBody"             (.projSym 0) "AgdaMirror.NetSandbox.HttpRespView.respBody"
  , mkSym "splitMarkGo"          "Context.Tools.NetSandbox.splitMarkGo"                       .defSym      "AgdaMirror.NetSandbox.splitMarkGo"
  , mkSym "splitMark"            "Context.Tools.NetSandbox.splitMark"                         .defSym      "AgdaMirror.NetSandbox.splitMark"
  , mkSym "isAsciiSpaceByte"     "Context.Tools.NetSandbox.isAsciiSpaceByte"                  .defSym      "AgdaMirror.NetSandbox.isAsciiSpaceByte"
  , mkSym "flushWordAcc"         "Context.Tools.NetSandbox.flushWordAcc"                      .defSym      "AgdaMirror.NetSandbox.flushWordAcc"
  , mkSym "wordsBytesGo"         "Context.Tools.NetSandbox.wordsBytesGo"                      .defSym      "AgdaMirror.NetSandbox.wordsBytesGo"
  , mkSym "wordsBytes"           "Context.Tools.NetSandbox.wordsBytes"                        .defSym      "AgdaMirror.NetSandbox.wordsBytes"
  , mkSym "wireText"             "Context.Tools.NetSandbox.wireText"                          .defSym      "AgdaMirror.NetSandbox.wireText"
  , mkSym "httpVersion"          "Context.Tools.NetSandbox.httpVersion"                       .defSym      "AgdaMirror.NetSandbox.httpVersion"
  , mkSym "httpVersionBytes"     "Context.Tools.NetSandbox.httpVersionBytes"                  .defSym      "AgdaMirror.NetSandbox.httpVersionBytes"
  , mkSym "requestLineBytes"     "Context.Tools.NetSandbox.requestLineBytes"                  .defSym      "AgdaMirror.NetSandbox.requestLineBytes"
  , mkSym "requestLine"          "Context.Tools.NetSandbox.requestLine"                       .defSym      "AgdaMirror.NetSandbox.requestLine"
  , mkSym "parseHttpReq"         "Context.Tools.NetSandbox.parseHttpReq"                      .defSym      "AgdaMirror.NetSandbox.parseHttpReq"
  , mkSym "digitValue"           "Context.Tools.NetSandbox.digitValue"                        .defSym      "AgdaMirror.NetSandbox.digitValue"
  , mkSym "statusValue"          "Context.Tools.NetSandbox.statusValue"                       .defSym      "AgdaMirror.NetSandbox.statusValue"
  , mkSym "statusView"           "Context.Tools.NetSandbox.statusView"                        .defSym      "AgdaMirror.NetSandbox.statusView"
  , mkSym "responseLineBytes"    "Context.Tools.NetSandbox.responseLineBytes"                 .defSym      "AgdaMirror.NetSandbox.responseLineBytes"
  , mkSym "responseLine"         "Context.Tools.NetSandbox.responseLine"                      .defSym      "AgdaMirror.NetSandbox.responseLine"
  , mkSym "parseHttpResp"        "Context.Tools.NetSandbox.parseHttpResp"                     .defSym      "AgdaMirror.NetSandbox.parseHttpResp"
  , mkSym "routeMatch"           "Context.Tools.NetSandbox.routeMatch"                        .defSym      "AgdaMirror.NetSandbox.routeMatch"
  , mkSym "matchHttpRoute"       "Context.Tools.NetSandbox.matchHttpRoute"                    .defSym      "AgdaMirror.NetSandbox.matchHttpRoute"
  , mkSym "matchRawRule"         "Context.Tools.NetSandbox.matchRawRule"                      .defSym      "AgdaMirror.NetSandbox.matchRawRule"
  , mkSym "NetStep"              "Context.Tools.NetSandbox.NetStep"                           .typeSym     "AgdaMirror.NetSandbox.NetStep"
  , mkSym "runClient"            "Context.Tools.NetSandbox.NetStep.runClient"                 .conSym      "AgdaMirror.NetSandbox.NetStep.runClient"     .unrelated 4
  , mkSym "waitPortReady"        "Context.Tools.NetSandbox.NetStep.waitPortReady"             .conSym      "AgdaMirror.NetSandbox.NetStep.waitPortReady" .unrelated 1
  , mkSym "tcpProbe"             "Context.Tools.NetSandbox.NetStep.tcpProbe"                  .conSym      "AgdaMirror.NetSandbox.NetStep.tcpProbe"      .unrelated 2
  , mkSym "httpProbe"            "Context.Tools.NetSandbox.NetStep.httpProbe"                 .conSym      "AgdaMirror.NetSandbox.NetStep.httpProbe"     .unrelated 5
  , mkSym "udpProbe"             "Context.Tools.NetSandbox.NetStep.udpProbe"                  .conSym      "AgdaMirror.NetSandbox.NetStep.udpProbe"      .unrelated 2
  , mkSym "sleepNetMs"           "Context.Tools.NetSandbox.NetStep.sleepNetMs"                .conSym      "AgdaMirror.NetSandbox.NetStep.sleepNetMs"    .unrelated 1
  , mkSym "drainNet"             "Context.Tools.NetSandbox.NetStep.drainNet"                  .conSym      "AgdaMirror.NetSandbox.NetStep.drainNet"      .unrelated 0
  , mkSym "RawNetObs"            "Context.Tools.NetSandbox.RawNetObs"                         .typeSym     "AgdaMirror.NetSandbox.RawNetObs"
  , mkSym "rawNetObs"            "Context.Tools.NetSandbox.rawNetObs"                         .conSym      "AgdaMirror.NetSandbox.RawNetObs.rawNetObs" .unrelated 6
  , mkSym "stdoutOut"            "Context.Tools.NetSandbox.RawNetObs.stdoutOut"               (.projSym 0) "AgdaMirror.NetSandbox.RawNetObs.stdoutOut"
  , mkSym "stderrOut"            "Context.Tools.NetSandbox.RawNetObs.stderrOut"               (.projSym 0) "AgdaMirror.NetSandbox.RawNetObs.stderrOut"
  , mkSym "wireReply"            "Context.Tools.NetSandbox.RawNetObs.wireReply"               (.projSym 0) "AgdaMirror.NetSandbox.RawNetObs.wireReply"
  , mkSym "capturedReqs"         "Context.Tools.NetSandbox.RawNetObs.capturedReqs"            (.projSym 0) "AgdaMirror.NetSandbox.RawNetObs.capturedReqs"
  , mkSym "exitStatus"           "Context.Tools.NetSandbox.RawNetObs.exitStatus"              (.projSym 0) "AgdaMirror.NetSandbox.RawNetObs.exitStatus"
  , mkSym "timedOut"             "Context.Tools.NetSandbox.RawNetObs.timedOut"                (.projSym 0) "AgdaMirror.NetSandbox.RawNetObs.timedOut"
  , mkSym "emptyNetObs"          "Context.Tools.NetSandbox.emptyNetObs"                       .defSym      "AgdaMirror.NetSandbox.emptyNetObs"
  , mkSym "eqExit"               "Context.Tools.NetSandbox.eqExit"                            .defSym      "AgdaMirror.NetSandbox.eqExit"
  , mkSym "eqBool"               "Context.Tools.NetSandbox.eqBool"                            .defSym      "AgdaMirror.NetSandbox.eqBool"
  , mkSym "eqObs"                "Context.Tools.NetSandbox.eqObs"                             .defSym      "AgdaMirror.NetSandbox.eqObs"
  , mkSym "eqReqView"            "Context.Tools.NetSandbox.eqReqView"                         .defSym      "AgdaMirror.NetSandbox.eqReqView"
  , mkSym "eqReqViews"           "Context.Tools.NetSandbox.eqReqViews"                        .defSym      "AgdaMirror.NetSandbox.eqReqViews"
  , mkSym "httpExchange"         "Context.Tools.NetSandbox.httpExchange"                      .defSym      "AgdaMirror.NetSandbox.httpExchange"
  , mkSym "stubReply"            "Context.Tools.NetSandbox.stubReply"                         .defSym      "AgdaMirror.NetSandbox.stubReply"
  , mkSym "evalStubExchange"     "Context.Tools.NetSandbox.evalStubExchange"                  .defSym      "AgdaMirror.NetSandbox.evalStubExchange"
  , mkSym "DaemonModel"          "Context.Tools.NetSandbox.DaemonModel"                       .typeSym     "AgdaMirror.NetSandbox.DaemonModel"
  , mkSym "daemonModel"          "Context.Tools.NetSandbox.daemonModel"                       .conSym      "AgdaMirror.NetSandbox.DaemonModel.daemonModel" .unrelated 5
  , mkSym "daemonReady"          "Context.Tools.NetSandbox.DaemonModel.daemonReady"           (.projSym 0) "AgdaMirror.NetSandbox.DaemonModel.daemonReady"
  , mkSym "daemonHandler"        "Context.Tools.NetSandbox.DaemonModel.daemonHandler"         (.projSym 0) "AgdaMirror.NetSandbox.DaemonModel.daemonHandler"
  , mkSym "daemonOut"            "Context.Tools.NetSandbox.DaemonModel.daemonOut"             (.projSym 0) "AgdaMirror.NetSandbox.DaemonModel.daemonOut"
  , mkSym "daemonErr"            "Context.Tools.NetSandbox.DaemonModel.daemonErr"             (.projSym 0) "AgdaMirror.NetSandbox.DaemonModel.daemonErr"
  , mkSym "daemonExit"           "Context.Tools.NetSandbox.DaemonModel.daemonExit"            (.projSym 0) "AgdaMirror.NetSandbox.DaemonModel.daemonExit"
  , mkSym "modelWire"            "Context.Tools.NetSandbox.modelWire"                         .defSym      "AgdaMirror.NetSandbox.modelWire"
  , mkSym "modelTimeout"         "Context.Tools.NetSandbox.modelTimeout"                      .defSym      "AgdaMirror.NetSandbox.modelTimeout"
  , mkSym "stepDaemonModel"      "Context.Tools.NetSandbox.stepDaemonModel"                   .defSym      "AgdaMirror.NetSandbox.stepDaemonModel"
  , mkSym "traceDaemonModel"     "Context.Tools.NetSandbox.traceDaemonModel"                  .defSym      "AgdaMirror.NetSandbox.traceDaemonModel"
  ]

def netLawsExports : List SymInfo :=
  [ mkSym "prefixBytes-refl"              "Context.Tools.NetLaws.prefixBytes-refl"              .defSym "AgdaMirror.NetLaws.prefixBytesRefl"
  , mkSym "prefixBytes-++"                "Context.Tools.NetLaws.prefixBytes-++"                .defSym "AgdaMirror.NetLaws.prefixBytesAppend"
  , mkSym "drop-length-++"                "Context.Tools.NetLaws.drop-length-++"                .defSym "AgdaMirror.NetLaws.dropLengthAppend"
  , mkSym "NoCR"                          "Context.Tools.NetLaws.NoCR"                          .defSym "AgdaMirror.NetLaws.NoCR"
  , mkSym "NoCRLF"                        "Context.Tools.NetLaws.NoCRLF"                        .defSym "AgdaMirror.NetLaws.NoCRLF"
  , mkSym "TokenByte"                     "Context.Tools.NetLaws.TokenByte"                     .defSym "AgdaMirror.NetLaws.TokenByte"
  , mkSym "NonEmptyBytes"                 "Context.Tools.NetLaws.NonEmptyBytes"                 .defSym "AgdaMirror.NetLaws.NonEmptyBytes"
  , mkSym "ValidTokenBytes"               "Context.Tools.NetLaws.ValidTokenBytes"               .defSym "AgdaMirror.NetLaws.ValidTokenBytes"
  , mkSym "ValidHttpToken"                "Context.Tools.NetLaws.ValidHttpToken"                .defSym "AgdaMirror.NetLaws.ValidHttpToken"
  , mkSym "parseHttpReq-encode-roundtrip"  "Context.Tools.NetLaws.parseHttpReq-encode-roundtrip"  .defSym "AgdaMirror.NetLaws.parseHttpReqEncodeRoundtrip"
  , mkSym "parseHttpReq-body-roundtrip"    "Context.Tools.NetLaws.parseHttpReq-body-roundtrip"    .defSym "AgdaMirror.NetLaws.parseHttpReqBodyRoundtrip"
  , mkSym "parseHttpResp-encode-roundtrip" "Context.Tools.NetLaws.parseHttpResp-encode-roundtrip" .defSym "AgdaMirror.NetLaws.parseHttpRespEncodeRoundtrip"
  , mkSym "evalStubExchange-reqs"         "Context.Tools.NetLaws.evalStubExchange-reqs"         .defSym "AgdaMirror.NetLaws.evalStubExchangeReqs"
  , mkSym "evalStubExchange-++"           "Context.Tools.NetLaws.evalStubExchange-++"           .defSym "AgdaMirror.NetLaws.evalStubExchangeAppend"
  ]

def gitSandboxExports : List SymInfo :=
  [ mkSym "GitConfig"          "Context.Tools.GitSandbox.GitConfig"                      .typeSym     "AgdaMirror.GitSandbox.GitConfig"
  , mkSym "gitConfig"          "Context.Tools.GitSandbox.gitConfig"                      .conSym      "AgdaMirror.GitSandbox.GitConfig.gitConfig" .unrelated 7
  , mkSym "target"             "Context.Tools.GitSandbox.GitConfig.target"               (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.target"
  , mkSym "defaultBranch"      "Context.Tools.GitSandbox.GitConfig.defaultBranch"        (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.defaultBranch"
  , mkSym "authorName"         "Context.Tools.GitSandbox.GitConfig.authorName"           (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.authorName"
  , mkSym "authorEmail"        "Context.Tools.GitSandbox.GitConfig.authorEmail"          (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.authorEmail"
  , mkSym "baseEpochSec"       "Context.Tools.GitSandbox.GitConfig.baseEpochSec"         (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.baseEpochSec"
  , mkSym "envVars"            "Context.Tools.GitSandbox.GitConfig.envVars"              (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.envVars"
  , mkSym "ownedFiles"         "Context.Tools.GitSandbox.GitConfig.ownedFiles"           (.projSym 0) "AgdaMirror.GitSandbox.GitConfig.ownedFiles"
  , mkSym "GitStep"            "Context.Tools.GitSandbox.GitStep"                        .typeSym     "AgdaMirror.GitSandbox.GitStep"
  , mkSym "gitWriteFile"       "Context.Tools.GitSandbox.GitStep.gitWriteFile"           .conSym      "AgdaMirror.GitSandbox.GitStep.gitWriteFile"    .unrelated 2
  , mkSym "gitRemoveFile"      "Context.Tools.GitSandbox.GitStep.gitRemoveFile"          .conSym      "AgdaMirror.GitSandbox.GitStep.gitRemoveFile"   .unrelated 1
  , mkSym "gitStageAll"        "Context.Tools.GitSandbox.GitStep.gitStageAll"            .conSym      "AgdaMirror.GitSandbox.GitStep.gitStageAll"     .unrelated 0
  , mkSym "gitStagePaths"      "Context.Tools.GitSandbox.GitStep.gitStagePaths"          .conSym      "AgdaMirror.GitSandbox.GitStep.gitStagePaths"   .unrelated 1
  , mkSym "gitCommit"          "Context.Tools.GitSandbox.GitStep.gitCommit"              .conSym      "AgdaMirror.GitSandbox.GitStep.gitCommit"       .unrelated 2
  , mkSym "gitSwitchBranch"    "Context.Tools.GitSandbox.GitStep.gitSwitchBranch"        .conSym      "AgdaMirror.GitSandbox.GitStep.gitSwitchBranch" .unrelated 2
  , mkSym "gitCreateTag"       "Context.Tools.GitSandbox.GitStep.gitCreateTag"           .conSym      "AgdaMirror.GitSandbox.GitStep.gitCreateTag"    .unrelated 1
  , mkSym "gitStatus"          "Context.Tools.GitSandbox.GitStep.gitStatus"              .conSym      "AgdaMirror.GitSandbox.GitStep.gitStatus"       .unrelated 0
  , mkSym "gitRunTarget"       "Context.Tools.GitSandbox.GitStep.gitRunTarget"           .conSym      "AgdaMirror.GitSandbox.GitStep.gitRunTarget"    .unrelated 4
  , mkSym "GitRepoSummary"     "Context.Tools.GitSandbox.GitRepoSummary"                 .typeSym     "AgdaMirror.GitSandbox.GitRepoSummary"
  , mkSym "gitSummary"         "Context.Tools.GitSandbox.gitSummary"                     .conSym      "AgdaMirror.GitSandbox.GitRepoSummary.gitSummary" .unrelated 7
  , mkSym "currentBranch"      "Context.Tools.GitSandbox.GitRepoSummary.currentBranch"   (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.currentBranch"
  , mkSym "commitCount"        "Context.Tools.GitSandbox.GitRepoSummary.commitCount"     (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.commitCount"
  , mkSym "branchNames"        "Context.Tools.GitSandbox.GitRepoSummary.branchNames"     (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.branchNames"
  , mkSym "tagNames"           "Context.Tools.GitSandbox.GitRepoSummary.tagNames"        (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.tagNames"
  , mkSym "stagedPaths"        "Context.Tools.GitSandbox.GitRepoSummary.stagedPaths"     (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.stagedPaths"
  , mkSym "modifiedPaths"      "Context.Tools.GitSandbox.GitRepoSummary.modifiedPaths"   (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.modifiedPaths"
  , mkSym "untrackedPaths"     "Context.Tools.GitSandbox.GitRepoSummary.untrackedPaths"  (.projSym 0) "AgdaMirror.GitSandbox.GitRepoSummary.untrackedPaths"
  , mkSym "RawGitObs"          "Context.Tools.GitSandbox.RawGitObs"                      .typeSym     "AgdaMirror.GitSandbox.RawGitObs"
  , mkSym "rawGitObs"          "Context.Tools.GitSandbox.rawGitObs"                      .conSym      "AgdaMirror.GitSandbox.RawGitObs.rawGitObs" .unrelated 6
  , mkSym "stdoutOut"          "Context.Tools.GitSandbox.RawGitObs.stdoutOut"            (.projSym 0) "AgdaMirror.GitSandbox.RawGitObs.stdoutOut"
  , mkSym "stderrOut"          "Context.Tools.GitSandbox.RawGitObs.stderrOut"            (.projSym 0) "AgdaMirror.GitSandbox.RawGitObs.stderrOut"
  , mkSym "commitHash"         "Context.Tools.GitSandbox.RawGitObs.commitHash"           (.projSym 0) "AgdaMirror.GitSandbox.RawGitObs.commitHash"
  , mkSym "exitStatus"         "Context.Tools.GitSandbox.RawGitObs.exitStatus"           (.projSym 0) "AgdaMirror.GitSandbox.RawGitObs.exitStatus"
  , mkSym "timedOut"           "Context.Tools.GitSandbox.RawGitObs.timedOut"             (.projSym 0) "AgdaMirror.GitSandbox.RawGitObs.timedOut"
  , mkSym "summary"            "Context.Tools.GitSandbox.RawGitObs.summary"              (.projSym 0) "AgdaMirror.GitSandbox.RawGitObs.summary"
  , mkSym "validGitPath"       "Context.Tools.GitSandbox.validGitPath"                   .defSym      "AgdaMirror.GitSandbox.validGitPath"
  , mkSym "refChar"            "Context.Tools.GitSandbox.refChar"                        .defSym      "AgdaMirror.GitSandbox.refChar"
  , mkSym "noDoubleDot"        "Context.Tools.GitSandbox.noDoubleDot"                    .defSym      "AgdaMirror.GitSandbox.noDoubleDot"
  , mkSym "validRefPart"       "Context.Tools.GitSandbox.validRefPart"                   .defSym      "AgdaMirror.GitSandbox.validRefPart"
  , mkSym "validRefName"       "Context.Tools.GitSandbox.validRefName"                   .defSym      "AgdaMirror.GitSandbox.validRefName"
  , mkSym "validBranch"        "Context.Tools.GitSandbox.validBranch"                    .defSym      "AgdaMirror.GitSandbox.validBranch"
  , mkSym "GitTree"            "Context.Tools.GitSandbox.GitTree"                        .typeSym     "AgdaMirror.GitSandbox.GitTree"
  , mkSym "PureCommit"         "Context.Tools.GitSandbox.PureCommit"                     .typeSym     "AgdaMirror.GitSandbox.PureCommit"
  , mkSym "pureCommit"         "Context.Tools.GitSandbox.pureCommit"                     .conSym      "AgdaMirror.GitSandbox.PureCommit.pureCommit" .unrelated 4
  , mkSym "parentIndex"        "Context.Tools.GitSandbox.PureCommit.parentIndex"         (.projSym 0) "AgdaMirror.GitSandbox.PureCommit.parentIndex"
  , mkSym "treeSnapshot"       "Context.Tools.GitSandbox.PureCommit.treeSnapshot"        (.projSym 0) "AgdaMirror.GitSandbox.PureCommit.treeSnapshot"
  , mkSym "commitMessage"      "Context.Tools.GitSandbox.PureCommit.commitMessage"       (.projSym 0) "AgdaMirror.GitSandbox.PureCommit.commitMessage"
  , mkSym "timestamp"          "Context.Tools.GitSandbox.PureCommit.timestamp"           (.projSym 0) "AgdaMirror.GitSandbox.PureCommit.timestamp"
  , mkSym "PureGitRepo"        "Context.Tools.GitSandbox.PureGitRepo"                    .typeSym     "AgdaMirror.GitSandbox.PureGitRepo"
  , mkSym "pureGitRepo"        "Context.Tools.GitSandbox.pureGitRepo"                    .conSym      "AgdaMirror.GitSandbox.PureGitRepo.pureGitRepo" .unrelated 7
  , mkSym "config"             "Context.Tools.GitSandbox.PureGitRepo.config"             (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.config"
  , mkSym "worktree"           "Context.Tools.GitSandbox.PureGitRepo.worktree"           (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.worktree"
  , mkSym "index"              "Context.Tools.GitSandbox.PureGitRepo.index"              (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.index"
  , mkSym "commits"            "Context.Tools.GitSandbox.PureGitRepo.commits"            (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.commits"
  , mkSym "branchMap"          "Context.Tools.GitSandbox.PureGitRepo.branchMap"          (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.branchMap"
  , mkSym "headBranch"         "Context.Tools.GitSandbox.PureGitRepo.headBranch"         (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.headBranch"
  , mkSym "tagMap"             "Context.Tools.GitSandbox.PureGitRepo.tagMap"             (.projSym 0) "AgdaMirror.GitSandbox.PureGitRepo.tagMap"
  , mkSym "lookupName"         "Context.Tools.GitSandbox.lookupName"                     .defSym      "AgdaMirror.GitSandbox.lookupName"
  , mkSym "putName"            "Context.Tools.GitSandbox.putName"                        .defSym      "AgdaMirror.GitSandbox.putName"
  , mkSym "removeName"         "Context.Tools.GitSandbox.removeName"                     .defSym      "AgdaMirror.GitSandbox.removeName"
  , mkSym "present"            "Context.Tools.GitSandbox.present"                        .defSym      "AgdaMirror.GitSandbox.present"
  , mkSym "eqMaybeBytes"       "Context.Tools.GitSandbox.eqMaybeBytes"                   .defSym      "AgdaMirror.GitSandbox.eqMaybeBytes"
  , mkSym "insertPath"         "Context.Tools.GitSandbox.insertPath"                     .defSym      "AgdaMirror.GitSandbox.insertPath"
  , mkSym "sortPaths"          "Context.Tools.GitSandbox.sortPaths"                      .defSym      "AgdaMirror.GitSandbox.sortPaths"
  , mkSym "choosePaths"        "Context.Tools.GitSandbox.choosePaths"                    .defSym      "AgdaMirror.GitSandbox.choosePaths"
  , mkSym "nthCommit"          "Context.Tools.GitSandbox.nthCommit"                      .defSym      "AgdaMirror.GitSandbox.nthCommit"
  , mkSym "headIndex"          "Context.Tools.GitSandbox.headIndex"                      .defSym      "AgdaMirror.GitSandbox.headIndex"
  , mkSym "treeAt"             "Context.Tools.GitSandbox.treeAt"                         .defSym      "AgdaMirror.GitSandbox.treeAt"
  , mkSym "headTree"           "Context.Tools.GitSandbox.headTree"                       .defSym      "AgdaMirror.GitSandbox.headTree"
  , mkSym "countParents"       "Context.Tools.GitSandbox.countParents"                   .defSym      "AgdaMirror.GitSandbox.countParents"
  , mkSym "changedPaths"       "Context.Tools.GitSandbox.changedPaths"                   .defSym      "AgdaMirror.GitSandbox.changedPaths"
  , mkSym "liveBranches"       "Context.Tools.GitSandbox.liveBranches"                   .defSym      "AgdaMirror.GitSandbox.liveBranches"
  , mkSym "projectSummary"     "Context.Tools.GitSandbox.projectSummary"                 .defSym      "AgdaMirror.GitSandbox.projectSummary"
  , mkSym "initTree"           "Context.Tools.GitSandbox.initTree"                       .defSym      "AgdaMirror.GitSandbox.initTree"
  , mkSym "initPureGit"        "Context.Tools.GitSandbox.initPureGit"                    .defSym      "AgdaMirror.GitSandbox.initPureGit"
  , mkSym "writeTree"          "Context.Tools.GitSandbox.writeTree"                      .defSym      "AgdaMirror.GitSandbox.writeTree"
  , mkSym "pathSelected"       "Context.Tools.GitSandbox.pathSelected"                   .defSym      "AgdaMirror.GitSandbox.pathSelected"
  , mkSym "stageSelected"      "Context.Tools.GitSandbox.stageSelected"                  .defSym      "AgdaMirror.GitSandbox.stageSelected"
  , mkSym "allStagePathsExist" "Context.Tools.GitSandbox.allStagePathsExist"             .defSym      "AgdaMirror.GitSandbox.allStagePathsExist"
  , mkSym "checkoutSafe"       "Context.Tools.GitSandbox.checkoutSafe"                   .defSym      "AgdaMirror.GitSandbox.checkoutSafe"
  , mkSym "carryTree"          "Context.Tools.GitSandbox.carryTree"                      .defSym      "AgdaMirror.GitSandbox.carryTree"
  , mkSym "checkoutExisting"   "Context.Tools.GitSandbox.checkoutExisting"               .defSym      "AgdaMirror.GitSandbox.checkoutExisting"
  , mkSym "newBranchMap"       "Context.Tools.GitSandbox.newBranchMap"                   .defSym      "AgdaMirror.GitSandbox.newBranchMap"
  , mkSym "switchBranch"       "Context.Tools.GitSandbox.switchBranch"                   .defSym      "AgdaMirror.GitSandbox.switchBranch"
  , mkSym "createTag"          "Context.Tools.GitSandbox.createTag"                      .defSym      "AgdaMirror.GitSandbox.createTag"
  , mkSym "commitTree"         "Context.Tools.GitSandbox.commitTree"                     .defSym      "AgdaMirror.GitSandbox.commitTree"
  , mkSym "stepPureGit"        "Context.Tools.GitSandbox.stepPureGit"                    .defSym      "AgdaMirror.GitSandbox.stepPureGit"
  , mkSym "runPureGit"         "Context.Tools.GitSandbox.runPureGit"                     .defSym      "AgdaMirror.GitSandbox.runPureGit"
  , mkSym "eqStrings"          "Context.Tools.GitSandbox.eqStrings"                      .defSym      "AgdaMirror.GitSandbox.eqStrings"
  , mkSym "eqGitSummary"       "Context.Tools.GitSandbox.eqGitSummary"                   .defSym      "AgdaMirror.GitSandbox.eqGitSummary"
  ]

def gitLawsExports : List SymInfo :=
  [ mkSym "lookupName-putName-same"          "Context.Tools.GitLaws.lookupName-putName-same"          .defSym "AgdaMirror.GitLaws.lookupNamePutNameSame"
  , mkSym "lookupName-putName-other"         "Context.Tools.GitLaws.lookupName-putName-other"         .defSym "AgdaMirror.GitLaws.lookupNamePutNameOther"
  , mkSym "stepPureGit-status-id"            "Context.Tools.GitLaws.stepPureGit-status-id"            .defSym "AgdaMirror.GitLaws.stepPureGitStatusId"
  , mkSym "stepPureGit-stageAll-index"       "Context.Tools.GitLaws.stepPureGit-stageAll-index"       .defSym "AgdaMirror.GitLaws.stepPureGitStageAllIndex"
  , mkSym "stepPureGit-stageAll-head"        "Context.Tools.GitLaws.stepPureGit-stageAll-head"        .defSym "AgdaMirror.GitLaws.stepPureGitStageAllHead"
  , mkSym "eqMaybeBytes-refl"                "Context.Tools.GitLaws.eqMaybeBytes-refl"                .defSym "AgdaMirror.GitLaws.eqMaybeBytesRefl"
  , mkSym "choosePaths-all-false"            "Context.Tools.GitLaws.choosePaths-all-false"            .defSym "AgdaMirror.GitLaws.choosePathsAllFalse"
  , mkSym "stepPureGit-stageAll-modified-empty" "Context.Tools.GitLaws.stepPureGit-stageAll-modified-empty" .defSym "AgdaMirror.GitLaws.stepPureGitStageAllModifiedEmpty"
  , mkSym "runPureGit-[]"                    "Context.Tools.GitLaws.runPureGit-[]"                    .defSym "AgdaMirror.GitLaws.runPureGitNil"
  , mkSym "runPureGit-++"                    "Context.Tools.GitLaws.runPureGit-++"                    .defSym "AgdaMirror.GitLaws.runPureGitAppend"
  ]

def webOperadExports : List SymInfo :=
  [ mkSym "Colour"                "Context.Terminal.Colour"                        .typeSym     "AgdaMirror.Context.Colour"
  , mkSym "defaultColour"         "Context.Terminal.Colour.defaultColour"          .conSym      "AgdaMirror.Context.Colour.defaultColour" .unrelated 0
  , mkSym "indexed"               "Context.Terminal.Colour.indexed"                .conSym      "AgdaMirror.Context.Colour.indexed"       .unrelated 1
  , mkSym "rgb"                   "Context.Terminal.Colour.rgb"                    .conSym      "AgdaMirror.Context.Colour.rgb"           .unrelated 3
  , mkSym "Key"                   "Context.Terminal.Key"                           .typeSym     "AgdaMirror.Context.Key"
  , mkSym "TimedMachine"          "Context.Terminal.TimedMachine"                  .typeSym     "AgdaMirror.Context.TimedMachine"
  , mkSym "Point"                 "Context.Tools.WebOperad.Point"                  .typeSym     "AgdaMirror.WebOperad.Point"
  , mkSym "pt"                    "Context.Tools.WebOperad.pt"                     .conSym      "AgdaMirror.WebOperad.Point.pt" .unrelated 2
  , mkSym "px"                    "Context.Tools.WebOperad.Point.px"               (.projSym 0) "AgdaMirror.WebOperad.Point.px"
  , mkSym "py"                    "Context.Tools.WebOperad.Point.py"               (.projSym 0) "AgdaMirror.WebOperad.Point.py"
  , mkSym "Size"                  "Context.Tools.WebOperad.Size"                   .typeSym     "AgdaMirror.WebOperad.Size"
  , mkSym "size"                  "Context.Tools.WebOperad.size"                   .conSym      "AgdaMirror.WebOperad.Size.size" .unrelated 2
  , mkSym "w"                     "Context.Tools.WebOperad.Size.w"                 (.projSym 0) "AgdaMirror.WebOperad.Size.w"
  , mkSym "h"                     "Context.Tools.WebOperad.Size.h"                 (.projSym 0) "AgdaMirror.WebOperad.Size.h"
  , mkSym "Rect"                  "Context.Tools.WebOperad.Rect"                   .typeSym     "AgdaMirror.WebOperad.Rect"
  , mkSym "rect"                  "Context.Tools.WebOperad.rect"                   .conSym      "AgdaMirror.WebOperad.Rect.rect" .unrelated 4
  , mkSym "rx"                    "Context.Tools.WebOperad.Rect.rx"                (.projSym 0) "AgdaMirror.WebOperad.Rect.rx"
  , mkSym "ry"                    "Context.Tools.WebOperad.Rect.ry"                (.projSym 0) "AgdaMirror.WebOperad.Rect.ry"
  , mkSym "rw"                    "Context.Tools.WebOperad.Rect.rw"                (.projSym 0) "AgdaMirror.WebOperad.Rect.rw"
  , mkSym "rh"                    "Context.Tools.WebOperad.Rect.rh"                (.projSym 0) "AgdaMirror.WebOperad.Rect.rh"
  , mkSym "QPoint"                "Context.Tools.WebOperad.QPoint"                 .typeSym     "AgdaMirror.WebOperad.QPoint"
  , mkSym "qpt"                   "Context.Tools.WebOperad.qpt"                    .conSym      "AgdaMirror.WebOperad.QPoint.qpt" .unrelated 3
  , mkSym "qx"                    "Context.Tools.WebOperad.QPoint.qx"              (.projSym 0) "AgdaMirror.WebOperad.QPoint.qx"
  , mkSym "qy"                    "Context.Tools.WebOperad.QPoint.qy"              (.projSym 0) "AgdaMirror.WebOperad.QPoint.qy"
  , mkSym "qdenMinus1"            "Context.Tools.WebOperad.QPoint.qdenMinus1"      (.projSym 0) "AgdaMirror.WebOperad.QPoint.qdenMinus1"
  , mkSym "den"                   "Context.Tools.WebOperad.den"                    .defSym      "AgdaMirror.WebOperad.den"
  , mkSym "fromPixel"             "Context.Tools.WebOperad.fromPixel"              .defSym      "AgdaMirror.WebOperad.fromPixel"
  , mkSym "rightEdge"             "Context.Tools.WebOperad.rightEdge"              .defSym      "AgdaMirror.WebOperad.rightEdge"
  , mkSym "bottomEdge"            "Context.Tools.WebOperad.bottomEdge"             .defSym      "AgdaMirror.WebOperad.bottomEdge"
  , mkSym "inRectQ"               "Context.Tools.WebOperad.inRectQ"                .defSym      "AgdaMirror.WebOperad.inRectQ"
  , mkSym "inRect"                "Context.Tools.WebOperad.inRect"                 .defSym      "AgdaMirror.WebOperad.inRect"
  , mkSym "subRect"               "Context.Tools.WebOperad.subRect"                .defSym      "AgdaMirror.WebOperad.subRect"
  , mkSym "disjointRect"          "Context.Tools.WebOperad.disjointRect"           .defSym      "AgdaMirror.WebOperad.disjointRect"
  , mkSym "Affine2D"              "Context.Tools.WebOperad.Affine2D"               .typeSym     "AgdaMirror.WebOperad.Affine2D"
  , mkSym "matrix"                "Context.Tools.WebOperad.matrix"                 .conSym      "AgdaMirror.WebOperad.Affine2D.matrix" .unrelated 4
  , mkSym "num-1"                 "Context.Tools.WebOperad.Affine2D.num-1"         (.projSym 0) "AgdaMirror.WebOperad.Affine2D.num_1"
  , mkSym "den-1"                 "Context.Tools.WebOperad.Affine2D.den-1"         (.projSym 0) "AgdaMirror.WebOperad.Affine2D.den_1"
  , mkSym "tx"                    "Context.Tools.WebOperad.Affine2D.tx"            (.projSym 0) "AgdaMirror.WebOperad.Affine2D.tx"
  , mkSym "ty"                    "Context.Tools.WebOperad.Affine2D.ty"            (.projSym 0) "AgdaMirror.WebOperad.Affine2D.ty"
  , mkSym "affine"                "Context.Tools.WebOperad.affine"                 .defSym      "AgdaMirror.WebOperad.affine"
  , mkSym "idAffine"              "Context.Tools.WebOperad.idAffine"               .defSym      "AgdaMirror.WebOperad.idAffine"
  , mkSym "compAffine"            "Context.Tools.WebOperad.compAffine"             .defSym      "AgdaMirror.WebOperad.compAffine"
  , mkSym "invAffine"             "Context.Tools.WebOperad.invAffine"              .defSym      "AgdaMirror.WebOperad.invAffine"
  , mkSym "applyFwd"              "Context.Tools.WebOperad.applyFwd"               .defSym      "AgdaMirror.WebOperad.applyFwd"
  , mkSym "applyInv"              "Context.Tools.WebOperad.applyInv"               .defSym      "AgdaMirror.WebOperad.applyInv"
  , mkSym "VisualStyle"           "Context.Tools.WebOperad.VisualStyle"            .typeSym     "AgdaMirror.WebOperad.VisualStyle"
  , mkSym "fill"                  "Context.Tools.WebOperad.VisualStyle.fill"       .conSym      "AgdaMirror.WebOperad.VisualStyle.fill"   .unrelated 1
  , mkSym "stroke"                "Context.Tools.WebOperad.VisualStyle.stroke"     .conSym      "AgdaMirror.WebOperad.VisualStyle.stroke" .unrelated 1
  , mkSym "label"                 "Context.Tools.WebOperad.VisualStyle.label"      .conSym      "AgdaMirror.WebOperad.VisualStyle.label"  .unrelated 2
  , mkSym "Scene"                 "Context.Tools.WebOperad.Scene"                  .typeSym     "AgdaMirror.WebOperad.Scene"
  , mkSym "empty"                 "Context.Tools.WebOperad.Scene.empty"            .conSym      "AgdaMirror.WebOperad.Scene.empty"       .unrelated 0
  , mkSym "decorRect"             "Context.Tools.WebOperad.Scene.decorRect"        .conSym      "AgdaMirror.WebOperad.Scene.decorRect"   .unrelated 2
  , mkSym "occludeRect"           "Context.Tools.WebOperad.Scene.occludeRect"      .conSym      "AgdaMirror.WebOperad.Scene.occludeRect" .unrelated 2
  , mkSym "hitRect"               "Context.Tools.WebOperad.Scene.hitRect"          .conSym      "AgdaMirror.WebOperad.Scene.hitRect"     .unrelated 3
  , mkSym "decorLine"             "Context.Tools.WebOperad.Scene.decorLine"        .conSym      "AgdaMirror.WebOperad.Scene.decorLine"   .unrelated 3
  , mkSym "transform"             "Context.Tools.WebOperad.Scene.transform"        .conSym      "AgdaMirror.WebOperad.Scene.transform"   .unrelated 2
  , mkSym "clip"                  "Context.Tools.WebOperad.Scene.clip"             .conSym      "AgdaMirror.WebOperad.Scene.clip"        .unrelated 2
  , mkSym "over"                  "Context.Tools.WebOperad.Scene.over"             .conSym      "AgdaMirror.WebOperad.Scene.over"        .unrelated 2
  , mkSym "mapScene"              "Context.Tools.WebOperad.mapScene"               .defSym      "AgdaMirror.WebOperad.mapScene"
  , mkSym "paint"                 "Context.Tools.WebOperad.paint"                  .defSym      "AgdaMirror.WebOperad.paint"
  , mkSym "ownerInk"              "Context.Tools.WebOperad.ownerInk"               .defSym      "AgdaMirror.WebOperad.ownerInk"
  , mkSym "colourInk"             "Context.Tools.WebOperad.colourInk"              .defSym      "AgdaMirror.WebOperad.colourInk"
  , mkSym "paintOwner"            "Context.Tools.WebOperad.paintOwner"             .defSym      "AgdaMirror.WebOperad.paintOwner"
  , mkSym "paintSurfaceColour"    "Context.Tools.WebOperad.paintSurfaceColour"     .defSym      "AgdaMirror.WebOperad.paintSurfaceColour"
  , mkSym "HitResult"             "Context.Tools.WebOperad.HitResult"              .typeSym     "AgdaMirror.WebOperad.HitResult"
  , mkSym "miss"                  "Context.Tools.WebOperad.HitResult.miss"         .conSym      "AgdaMirror.WebOperad.HitResult.miss"    .unrelated 0
  , mkSym "blocked"               "Context.Tools.WebOperad.HitResult.blocked"      .conSym      "AgdaMirror.WebOperad.HitResult.blocked" .unrelated 0
  , mkSym "hit"                   "Context.Tools.WebOperad.HitResult.hit"          .conSym      "AgdaMirror.WebOperad.HitResult.hit"     .unrelated 1
  , mkSym "route"                 "Context.Tools.WebOperad.route"                  .defSym      "AgdaMirror.WebOperad.route"
  , mkSym "resolve"               "Context.Tools.WebOperad.resolve"                .defSym      "AgdaMirror.WebOperad.resolve"
  , mkSym "hitTest"               "Context.Tools.WebOperad.hitTest"                .defSym      "AgdaMirror.WebOperad.hitTest"
  , mkSym "visual-hit-consistent" "Context.Tools.WebOperad.visual-hit-consistent"  .defSym      "AgdaMirror.WebOperad.visualHitConsistent"
  , mkSym "DrawCmd"               "Context.Tools.WebOperad.DrawCmd"                .typeSym     "AgdaMirror.WebOperad.DrawCmd"
  , mkSym "cmdSave"               "Context.Tools.WebOperad.DrawCmd.cmdSave"        .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdSave"       .unrelated 0
  , mkSym "cmdRestore"            "Context.Tools.WebOperad.DrawCmd.cmdRestore"     .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdRestore"    .unrelated 0
  , mkSym "cmdTransform"          "Context.Tools.WebOperad.DrawCmd.cmdTransform"   .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdTransform"  .unrelated 1
  , mkSym "cmdClip"               "Context.Tools.WebOperad.DrawCmd.cmdClip"        .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdClip"       .unrelated 1
  , mkSym "cmdFillRect"           "Context.Tools.WebOperad.DrawCmd.cmdFillRect"    .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdFillRect"   .unrelated 2
  , mkSym "cmdStrokeRect"         "Context.Tools.WebOperad.DrawCmd.cmdStrokeRect"  .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdStrokeRect" .unrelated 2
  , mkSym "cmdText"               "Context.Tools.WebOperad.DrawCmd.cmdText"        .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdText"       .unrelated 3
  , mkSym "cmdLine"               "Context.Tools.WebOperad.DrawCmd.cmdLine"        .conSym      "AgdaMirror.WebOperad.DrawCmd.cmdLine"       .unrelated 3
  , mkSym "styleCmd"              "Context.Tools.WebOperad.styleCmd"               .defSym      "AgdaMirror.WebOperad.styleCmd"
  , mkSym "DrawPass"              "Context.Tools.WebOperad.DrawPass"               .typeSym     "AgdaMirror.WebOperad.DrawPass"
  , mkSym "full"                  "Context.Tools.WebOperad.DrawPass.full"          .conSym      "AgdaMirror.WebOperad.DrawPass.full"     .unrelated 0
  , mkSym "surfaces"              "Context.Tools.WebOperad.DrawPass.surfaces"      .conSym      "AgdaMirror.WebOperad.DrawPass.surfaces" .unrelated 0
  , mkSym "emit"                  "Context.Tools.WebOperad.emit"                   .defSym      "AgdaMirror.WebOperad.emit"
  , mkSym "compileDraw"           "Context.Tools.WebOperad.compileDraw"            .defSym      "AgdaMirror.WebOperad.compileDraw"
  , mkSym "compileSurfaceDraw"    "Context.Tools.WebOperad.compileSurfaceDraw"     .defSym      "AgdaMirror.WebOperad.compileSurfaceDraw"
  , mkSym "FrameState"            "Context.Tools.WebOperad.FrameState"             .typeSym     "AgdaMirror.WebOperad.FrameState"
  , mkSym "mask"                  "Context.Tools.WebOperad.mask"                   .defSym      "AgdaMirror.WebOperad.mask"
  , mkSym "putColour"             "Context.Tools.WebOperad.putColour"              .defSym      "AgdaMirror.WebOperad.putColour"
  , mkSym "run"                   "Context.Tools.WebOperad.run"                    .defSym      "AgdaMirror.WebOperad.run"
  , mkSym "runDrawStack"          "Context.Tools.WebOperad.runDrawStack"           .defSym      "AgdaMirror.WebOperad.runDrawStack"
  , mkSym "draw-machine-sound"    "Context.Tools.WebOperad.draw-machine-sound"     .defSym      "AgdaMirror.WebOperad.drawMachineSound"
  , mkSym "HostInput"             "Context.Tools.WebOperad.HostInput"              .typeSym     "AgdaMirror.WebOperad.HostInput"
  , mkSym "hostClick"             "Context.Tools.WebOperad.HostInput.hostClick"    .conSym      "AgdaMirror.WebOperad.HostInput.hostClick"   .unrelated 2
  , mkSym "hostPanZoom"           "Context.Tools.WebOperad.HostInput.hostPanZoom"  .conSym      "AgdaMirror.WebOperad.HostInput.hostPanZoom" .unrelated 4
  , mkSym "hostKey"               "Context.Tools.WebOperad.HostInput.hostKey"      .conSym      "AgdaMirror.WebOperad.HostInput.hostKey"     .unrelated 1
  , mkSym "hostResize"            "Context.Tools.WebOperad.HostInput.hostResize"   .conSym      "AgdaMirror.WebOperad.HostInput.hostResize"  .unrelated 2
  , mkSym "hostTickMs"            "Context.Tools.WebOperad.HostInput.hostTickMs"   .conSym      "AgdaMirror.WebOperad.HostInput.hostTickMs"  .unrelated 1
  ]

def worldExports : List SymInfo :=
  [ -- Re-exported `Context.Tools.Clock` public symbols
    mkSym "SimClock"            "Context.Tools.Clock.SimClock"               .typeSym     "AgdaMirror.Clock.SimClock"
  , mkSym "simClock"            "Context.Tools.Clock.simClock"               .conSym      "AgdaMirror.Clock.SimClock.simClock" .unrelated 3
  , mkSym "monoMs"              "Context.Tools.Clock.SimClock.monoMs"        (.projSym 0) "AgdaMirror.Clock.SimClock.monoMs"
  , mkSym "wallEpochMs"         "Context.Tools.Clock.SimClock.wallEpochMs"   (.projSym 0) "AgdaMirror.Clock.SimClock.wallEpochMs"
  , mkSym "autoTicks"           "Context.Tools.Clock.SimClock.autoTicks"     (.projSym 0) "AgdaMirror.Clock.SimClock.autoTicks"
  , mkSym "initClock"           "Context.Tools.Clock.initClock"              .defSym      "AgdaMirror.Clock.initClock"
  , mkSym "zeroClock"           "Context.Tools.Clock.zeroClock"              .defSym      "AgdaMirror.Clock.zeroClock"
  , mkSym "fixedStepClock"      "Context.Tools.Clock.fixedStepClock"         .defSym      "AgdaMirror.Clock.fixedStepClock"
  , mkSym "advanceClock"        "Context.Tools.Clock.advanceClock"           .defSym      "AgdaMirror.Clock.advanceClock"
  , mkSym "tickClock"           "Context.Tools.Clock.tickClock"              .defSym      "AgdaMirror.Clock.tickClock"
  , mkSym "readMonoMs"          "Context.Tools.Clock.readMonoMs"             .defSym      "AgdaMirror.Clock.readMonoMs"
  , mkSym "readWallMs"          "Context.Tools.Clock.readWallMs"             .defSym      "AgdaMirror.Clock.readWallMs"
  , mkSym "sleepClockMs"        "Context.Tools.Clock.sleepClockMs"           .defSym      "AgdaMirror.Clock.sleepClockMs"
  , mkSym "deadlineReached"     "Context.Tools.Clock.deadlineReached"        .defSym      "AgdaMirror.Clock.deadlineReached"
  , mkSym "remainingMs"         "Context.Tools.Clock.remainingMs"            .defSym      "AgdaMirror.Clock.remainingMs"
  -- §1 Capability Lattice
  , mkSym "Cap"                 "Context.World.Cap"                          .typeSym     "AgdaMirror.World.Cap"
  , mkSym "clockCap"            "Context.World.Cap.clockCap"                 .conSym      "AgdaMirror.World.Cap.clockCap" .unrelated 0
  , mkSym "envCap"              "Context.World.Cap.envCap"                   .conSym      "AgdaMirror.World.Cap.envCap"   .unrelated 0
  , mkSym "ttyCap"              "Context.World.Cap.ttyCap"                   .conSym      "AgdaMirror.World.Cap.ttyCap"   .unrelated 0
  , mkSym "fsCap"               "Context.World.Cap.fsCap"                    .conSym      "AgdaMirror.World.Cap.fsCap"    .unrelated 0
  , mkSym "netCap"              "Context.World.Cap.netCap"                   .conSym      "AgdaMirror.World.Cap.netCap"   .unrelated 0
  , mkSym "gitCap"              "Context.World.Cap.gitCap"                   .conSym      "AgdaMirror.World.Cap.gitCap"   .unrelated 0
  , mkSym "webCap"              "Context.World.Cap.webCap"                   .conSym      "AgdaMirror.World.Cap.webCap"   .unrelated 0
  , mkSym "eqCap"               "Context.World.eqCap"                        .defSym      "AgdaMirror.World.eqCap"
  , mkSym "_∈_"                 "Context.World._∈_"                          .typeSym     "AgdaMirror.World.CapMem"      (.related 4 .infixN)
  , mkSym "here"                "Context.World._∈_.here"                     .conSym      "AgdaMirror.World.CapMem.here"  .unrelated 0
  , mkSym "there"               "Context.World._∈_.there"                    .conSym      "AgdaMirror.World.CapMem.there" .unrelated 1
  , mkSym "_⊆_"                 "Context.World._⊆_"                          .typeSym     "AgdaMirror.World.CapSub"      (.related 4 .infixN)
  , mkSym "⊆-refl"              "Context.World.⊆-refl"                       .defSym      "AgdaMirror.World.capSubRefl"
  , mkSym "⊆-trans"             "Context.World.⊆-trans"                      .defSym      "AgdaMirror.World.capSubTrans"
  , mkSym "⊆-nil"               "Context.World.⊆-nil"                        .defSym      "AgdaMirror.World.capSubNil"
  , mkSym "⊆-step"              "Context.World.⊆-step"                       .defSym      "AgdaMirror.World.capSubStep"
  , mkSym "⊆-cons"              "Context.World.⊆-cons"                       .defSym      "AgdaMirror.World.capSubCons"
  , mkSym "hasCap"              "Context.World.hasCap"                       .defSym      "AgdaMirror.World.hasCap"
  , mkSym "findCap∈"            "Context.World.findCap∈"                     .defSym      "AgdaMirror.World.findCapIn"
  , mkSym "PureCaps"            "Context.World.PureCaps"                     .defSym      "AgdaMirror.World.PureCaps"
  , mkSym "CliCaps"             "Context.World.CliCaps"                      .defSym      "AgdaMirror.World.CliCaps"
  , mkSym "AllCaps"             "Context.World.AllCaps"                      .defSym      "AgdaMirror.World.AllCaps"
  , mkSym "clock∈Cli"           "Context.World.clock∈Cli"                    .defSym      "AgdaMirror.World.clockInCli"
  , mkSym "env∈Cli"             "Context.World.env∈Cli"                      .defSym      "AgdaMirror.World.envInCli"
  , mkSym "tty∈Cli"             "Context.World.tty∈Cli"                      .defSym      "AgdaMirror.World.ttyInCli"
  , mkSym "fs∈Cli"              "Context.World.fs∈Cli"                       .defSym      "AgdaMirror.World.fsInCli"
  , mkSym "net∈Cli"             "Context.World.net∈Cli"                      .defSym      "AgdaMirror.World.netInCli"
  , mkSym "clock∈All"           "Context.World.clock∈All"                    .defSym      "AgdaMirror.World.clockInAll"
  , mkSym "env∈All"             "Context.World.env∈All"                      .defSym      "AgdaMirror.World.envInAll"
  , mkSym "tty∈All"             "Context.World.tty∈All"                      .defSym      "AgdaMirror.World.ttyInAll"
  , mkSym "fs∈All"              "Context.World.fs∈All"                       .defSym      "AgdaMirror.World.fsInAll"
  , mkSym "net∈All"             "Context.World.net∈All"                      .defSym      "AgdaMirror.World.netInAll"
  , mkSym "git∈All"             "Context.World.git∈All"                      .defSym      "AgdaMirror.World.gitInAll"
  , mkSym "web∈All"             "Context.World.web∈All"                      .defSym      "AgdaMirror.World.webInAll"
  , mkSym "cli⊆All"             "Context.World.cli⊆All"                      .defSym      "AgdaMirror.World.cliSubAll"
  -- §2 UTF-8 & Deterministic Error Models
  , mkSym "decodeUtf8Chars"     "Context.World.decodeUtf8Chars"              .defSym      "AgdaMirror.World.decodeUtf8Chars"
  , mkSym "decodeUtf8"          "Context.World.decodeUtf8"                   .defSym      "AgdaMirror.World.decodeUtf8"
  , mkSym "decodeUtf8LossyChars" "Context.World.decodeUtf8LossyChars"        .defSym      "AgdaMirror.World.decodeUtf8LossyChars"
  , mkSym "decodeUtf8Lossy"     "Context.World.decodeUtf8Lossy"              .defSym      "AgdaMirror.World.decodeUtf8Lossy"
  , mkSym "FsError"             "Context.World.FsError"                      .typeSym     "AgdaMirror.World.FsError"
  , mkSym "fsNotFound"          "Context.World.FsError.fsNotFound"           .conSym      "AgdaMirror.World.FsError.fsNotFound"         .unrelated 0
  , mkSym "fsIsDirectory"       "Context.World.FsError.fsIsDirectory"        .conSym      "AgdaMirror.World.FsError.fsIsDirectory"      .unrelated 0
  , mkSym "fsNotDirectory"      "Context.World.FsError.fsNotDirectory"       .conSym      "AgdaMirror.World.FsError.fsNotDirectory"     .unrelated 0
  , mkSym "fsAlreadyExists"     "Context.World.FsError.fsAlreadyExists"      .conSym      "AgdaMirror.World.FsError.fsAlreadyExists"    .unrelated 0
  , mkSym "fsPermissionDenied"  "Context.World.FsError.fsPermissionDenied"   .conSym      "AgdaMirror.World.FsError.fsPermissionDenied" .unrelated 0
  , mkSym "fsSymlinkLoop"       "Context.World.FsError.fsSymlinkLoop"        .conSym      "AgdaMirror.World.FsError.fsSymlinkLoop"      .unrelated 0
  , mkSym "fsInvalidPath"       "Context.World.FsError.fsInvalidPath"        .conSym      "AgdaMirror.World.FsError.fsInvalidPath"      .unrelated 0
  , mkSym "fsIoError"           "Context.World.FsError.fsIoError"            .conSym      "AgdaMirror.World.FsError.fsIoError"          .unrelated 0
  , mkSym "eqFsError"           "Context.World.eqFsError"                    .defSym      "AgdaMirror.World.eqFsError"
  , mkSym "describeFsError"     "Context.World.describeFsError"              .defSym      "AgdaMirror.World.describeFsError"
  , mkSym "NetError"            "Context.World.NetError"                     .typeSym     "AgdaMirror.World.NetError"
  , mkSym "netConnRefused"      "Context.World.NetError.netConnRefused"      .conSym      "AgdaMirror.World.NetError.netConnRefused"     .unrelated 0
  , mkSym "netTimedOut"         "Context.World.NetError.netTimedOut"         .conSym      "AgdaMirror.World.NetError.netTimedOut"        .unrelated 0
  , mkSym "netInvalidEndpoint"  "Context.World.NetError.netInvalidEndpoint"  .conSym      "AgdaMirror.World.NetError.netInvalidEndpoint" .unrelated 0
  , mkSym "netTlsError"         "Context.World.NetError.netTlsError"         .conSym      "AgdaMirror.World.NetError.netTlsError"        .unrelated 0
  , mkSym "netIoError"          "Context.World.NetError.netIoError"          .conSym      "AgdaMirror.World.NetError.netIoError"         .unrelated 0
  , mkSym "eqNetError"          "Context.World.eqNetError"                   .defSym      "AgdaMirror.World.eqNetError"
  , mkSym "describeNetError"    "Context.World.describeNetError"             .defSym      "AgdaMirror.World.describeNetError"
  -- §3 Simulated World Components & `SimWorld`
  , mkSym "SimProcessEnv"       "Context.World.SimProcessEnv"                .typeSym     "AgdaMirror.World.SimProcessEnv"
  , mkSym "simProcessEnv"       "Context.World.simProcessEnv"                .conSym      "AgdaMirror.World.SimProcessEnv.simProcessEnv" .unrelated 4
  , mkSym "progName"            "Context.World.SimProcessEnv.progName"       (.projSym 0) "AgdaMirror.World.SimProcessEnv.progName"
  , mkSym "args"                "Context.World.SimProcessEnv.args"           (.projSym 0) "AgdaMirror.World.SimProcessEnv.args"
  , mkSym "envVars"             "Context.World.SimProcessEnv.envVars"        (.projSym 0) "AgdaMirror.World.SimProcessEnv.envVars"
  , mkSym "stdinBytes"          "Context.World.SimProcessEnv.stdinBytes"     (.projSym 0) "AgdaMirror.World.SimProcessEnv.stdinBytes"
  , mkSym "emptyProcessEnv"     "Context.World.emptyProcessEnv"              .defSym      "AgdaMirror.World.emptyProcessEnv"
  , mkSym "cliProcessEnv"       "Context.World.cliProcessEnv"                .defSym      "AgdaMirror.World.cliProcessEnv"
  , mkSym "SimTTY"              "Context.World.SimTTY"                       .typeSym     "AgdaMirror.World.SimTTY"
  , mkSym "simTTY"              "Context.World.simTTY"                       .conSym      "AgdaMirror.World.SimTTY.simTTY" .unrelated 7
  , mkSym "ttyStdin"            "Context.World.SimTTY.ttyStdin"              (.projSym 0) "AgdaMirror.World.SimTTY.ttyStdin"
  , mkSym "ttyStdout"           "Context.World.SimTTY.ttyStdout"             (.projSym 0) "AgdaMirror.World.SimTTY.ttyStdout"
  , mkSym "ttyStderr"           "Context.World.SimTTY.ttyStderr"             (.projSym 0) "AgdaMirror.World.SimTTY.ttyStderr"
  , mkSym "stdoutBuf"           "Context.World.SimTTY.stdoutBuf"             (.projSym 0) "AgdaMirror.World.SimTTY.stdoutBuf"
  , mkSym "stderrBuf"           "Context.World.SimTTY.stderrBuf"             (.projSym 0) "AgdaMirror.World.SimTTY.stderrBuf"
  , mkSym "ttyInput"            "Context.World.SimTTY.ttyInput"              (.projSym 0) "AgdaMirror.World.SimTTY.ttyInput"
  , mkSym "ttyScreen"           "Context.World.SimTTY.ttyScreen"             (.projSym 0) "AgdaMirror.World.SimTTY.ttyScreen"
  , mkSym "pipeTTY"             "Context.World.pipeTTY"                      .defSym      "AgdaMirror.World.pipeTTY"
  , mkSym "interactiveTTY"      "Context.World.interactiveTTY"               .defSym      "AgdaMirror.World.interactiveTTY"
  , mkSym "NetEndpoint"         "Context.World.NetEndpoint"                  .typeSym     "AgdaMirror.World.NetEndpoint"
  , mkSym "netEndpoint"         "Context.World.netEndpoint"                  .conSym      "AgdaMirror.World.NetEndpoint.netEndpoint" .unrelated 6
  , mkSym "epHost"              "Context.World.NetEndpoint.epHost"           (.projSym 0) "AgdaMirror.World.NetEndpoint.epHost"
  , mkSym "epPort"              "Context.World.NetEndpoint.epPort"           (.projSym 0) "AgdaMirror.World.NetEndpoint.epPort"
  , mkSym "epTls"               "Context.World.NetEndpoint.epTls"            (.projSym 0) "AgdaMirror.World.NetEndpoint.epTls"
  , mkSym "epCertOk"            "Context.World.NetEndpoint.epCertOk"         (.projSym 0) "AgdaMirror.World.NetEndpoint.epCertOk"
  , mkSym "epLatencyMs"         "Context.World.NetEndpoint.epLatencyMs"      (.projSym 0) "AgdaMirror.World.NetEndpoint.epLatencyMs"
  , mkSym "epTopology"          "Context.World.NetEndpoint.epTopology"       (.projSym 0) "AgdaMirror.World.NetEndpoint.epTopology"
  , mkSym "SimNet"              "Context.World.SimNet"                       .typeSym     "AgdaMirror.World.SimNet"
  , mkSym "simNet"              "Context.World.simNet"                       .conSym      "AgdaMirror.World.SimNet.simNet" .unrelated 2
  , mkSym "endpoints"           "Context.World.SimNet.endpoints"             (.projSym 0) "AgdaMirror.World.SimNet.endpoints"
  , mkSym "capturedWire"        "Context.World.SimNet.capturedWire"          (.projSym 0) "AgdaMirror.World.SimNet.capturedWire"
  , mkSym "emptyNet"            "Context.World.emptyNet"                     .defSym      "AgdaMirror.World.emptyNet"
  , mkSym "httpStubEndpoint"    "Context.World.httpStubEndpoint"             .defSym      "AgdaMirror.World.httpStubEndpoint"
  , mkSym "CanvasDOM"           "Context.World.CanvasDOM"                    .typeSym     "AgdaMirror.World.CanvasDOM"
  , mkSym "canvasDOM"           "Context.World.canvasDOM"                    .conSym      "AgdaMirror.World.CanvasDOM.canvasDOM" .unrelated 4
  , mkSym "domViewport"         "Context.World.CanvasDOM.domViewport"        (.projSym 0) "AgdaMirror.World.CanvasDOM.domViewport"
  , mkSym "domCommands"         "Context.World.CanvasDOM.domCommands"        (.projSym 0) "AgdaMirror.World.CanvasDOM.domCommands"
  , mkSym "domTitle"            "Context.World.CanvasDOM.domTitle"           (.projSym 0) "AgdaMirror.World.CanvasDOM.domTitle"
  , mkSym "domEvents"           "Context.World.CanvasDOM.domEvents"          (.projSym 0) "AgdaMirror.World.CanvasDOM.domEvents"
  , mkSym "emptyCanvasDOM"      "Context.World.emptyCanvasDOM"               .defSym      "AgdaMirror.World.emptyCanvasDOM"
  , mkSym "SimWorld"            "Context.World.SimWorld"                     .typeSym     "AgdaMirror.World.SimWorld"
  , mkSym "simWorld"            "Context.World.simWorld"                     .conSym      "AgdaMirror.World.SimWorld.simWorld" .unrelated 7
  , mkSym "clock"               "Context.World.SimWorld.clock"               (.projSym 0) "AgdaMirror.World.SimWorld.clock"
  , mkSym "env"                 "Context.World.SimWorld.env"                 (.projSym 0) "AgdaMirror.World.SimWorld.env"
  , mkSym "tty"                 "Context.World.SimWorld.tty"                 (.projSym 0) "AgdaMirror.World.SimWorld.tty"
  , mkSym "fs"                  "Context.World.SimWorld.fs"                  (.projSym 0) "AgdaMirror.World.SimWorld.fs"
  , mkSym "net"                 "Context.World.SimWorld.net"                 (.projSym 0) "AgdaMirror.World.SimWorld.net"
  , mkSym "git"                 "Context.World.SimWorld.git"                 (.projSym 0) "AgdaMirror.World.SimWorld.git"
  , mkSym "web"                 "Context.World.SimWorld.web"                 (.projSym 0) "AgdaMirror.World.SimWorld.web"
  , mkSym "defaultGitRepo"      "Context.World.defaultGitRepo"               .defSym      "AgdaMirror.World.defaultGitRepo"
  , mkSym "defaultSimWorld"     "Context.World.defaultSimWorld"              .defSym      "AgdaMirror.World.defaultSimWorld"
  , mkSym "cliSimWorld"         "Context.World.cliSimWorld"                  .defSym      "AgdaMirror.World.cliSimWorld"
  -- §4 Effect Algebra (`Op`, `Ret`, `WorldProg`, `liftWorld`, smart constructors)
  , mkSym "Op"                  "Context.World.Op"                           .typeSym     "AgdaMirror.World.Op"
  , mkSym "opNowMono"           "Context.World.Op.opNowMono"                 .conSym      "AgdaMirror.World.Op.opNowMono"       .unrelated 0
  , mkSym "opNowWall"           "Context.World.Op.opNowWall"                 .conSym      "AgdaMirror.World.Op.opNowWall"       .unrelated 0
  , mkSym "opSleepMs"           "Context.World.Op.opSleepMs"                 .conSym      "AgdaMirror.World.Op.opSleepMs"       .unrelated 1
  , mkSym "opGetProgName"       "Context.World.Op.opGetProgName"             .conSym      "AgdaMirror.World.Op.opGetProgName"   .unrelated 0
  , mkSym "opGetArgs"           "Context.World.Op.opGetArgs"                 .conSym      "AgdaMirror.World.Op.opGetArgs"       .unrelated 0
  , mkSym "opLookupEnv"         "Context.World.Op.opLookupEnv"               .conSym      "AgdaMirror.World.Op.opLookupEnv"     .unrelated 1
  , mkSym "opReadStdinAll"      "Context.World.Op.opReadStdinAll"            .conSym      "AgdaMirror.World.Op.opReadStdinAll"  .unrelated 0
  , mkSym "opReadStdinLine"     "Context.World.Op.opReadStdinLine"           .conSym      "AgdaMirror.World.Op.opReadStdinLine" .unrelated 0
  , mkSym "opIsTTYStdin"        "Context.World.Op.opIsTTYStdin"              .conSym      "AgdaMirror.World.Op.opIsTTYStdin"    .unrelated 0
  , mkSym "opIsTTYStdout"       "Context.World.Op.opIsTTYStdout"             .conSym      "AgdaMirror.World.Op.opIsTTYStdout"   .unrelated 0
  , mkSym "opIsTTYStderr"       "Context.World.Op.opIsTTYStderr"             .conSym      "AgdaMirror.World.Op.opIsTTYStderr"   .unrelated 0
  , mkSym "opTermSize"          "Context.World.Op.opTermSize"                .conSym      "AgdaMirror.World.Op.opTermSize"      .unrelated 0
  , mkSym "opWriteStdout"       "Context.World.Op.opWriteStdout"             .conSym      "AgdaMirror.World.Op.opWriteStdout"   .unrelated 1
  , mkSym "opWriteStderr"       "Context.World.Op.opWriteStderr"             .conSym      "AgdaMirror.World.Op.opWriteStderr"   .unrelated 1
  , mkSym "opReadTTYByte"       "Context.World.Op.opReadTTYByte"             .conSym      "AgdaMirror.World.Op.opReadTTYByte"   .unrelated 0
  , mkSym "opReadFile"          "Context.World.Op.opReadFile"                .conSym      "AgdaMirror.World.Op.opReadFile"      .unrelated 1
  , mkSym "opWriteFile"         "Context.World.Op.opWriteFile"               .conSym      "AgdaMirror.World.Op.opWriteFile"     .unrelated 2
  , mkSym "opMkdir"             "Context.World.Op.opMkdir"                   .conSym      "AgdaMirror.World.Op.opMkdir"         .unrelated 2
  , mkSym "opSymlink"           "Context.World.Op.opSymlink"                 .conSym      "AgdaMirror.World.Op.opSymlink"       .unrelated 2
  , mkSym "opUnlink"            "Context.World.Op.opUnlink"                  .conSym      "AgdaMirror.World.Op.opUnlink"        .unrelated 1
  , mkSym "opStat"              "Context.World.Op.opStat"                    .conSym      "AgdaMirror.World.Op.opStat"          .unrelated 1
  , mkSym "opTcpExchange"       "Context.World.Op.opTcpExchange"             .conSym      "AgdaMirror.World.Op.opTcpExchange"   .unrelated 5
  , mkSym "opTlsExchange"       "Context.World.Op.opTlsExchange"             .conSym      "AgdaMirror.World.Op.opTlsExchange"   .unrelated 7
  , mkSym "opGitStep"           "Context.World.Op.opGitStep"                 .conSym      "AgdaMirror.World.Op.opGitStep"       .unrelated 1
  , mkSym "opGitSummary"        "Context.World.Op.opGitSummary"              .conSym      "AgdaMirror.World.Op.opGitSummary"    .unrelated 0
  , mkSym "opWebViewport"       "Context.World.Op.opWebViewport"             .conSym      "AgdaMirror.World.Op.opWebViewport"   .unrelated 0
  , mkSym "opWebSetTitle"       "Context.World.Op.opWebSetTitle"             .conSym      "AgdaMirror.World.Op.opWebSetTitle"   .unrelated 1
  , mkSym "opWebDrawScene"      "Context.World.Op.opWebDrawScene"            .conSym      "AgdaMirror.World.Op.opWebDrawScene"  .unrelated 1
  , mkSym "opWebHitTest"        "Context.World.Op.opWebHitTest"              .conSym      "AgdaMirror.World.Op.opWebHitTest"    .unrelated 2
  , mkSym "opWebPollInput"      "Context.World.Op.opWebPollInput"            .conSym      "AgdaMirror.World.Op.opWebPollInput"  .unrelated 0
  , mkSym "Ret"                 "Context.World.Ret"                          .defSym      "AgdaMirror.World.Ret"
  , mkSym "WorldProg"           "Context.World.WorldProg"                    .typeSym     "AgdaMirror.World.WorldProg"
  , mkSym "pure"                "Context.World.WorldProg.pure"               .conSym      "AgdaMirror.World.WorldProg.pure" .unrelated 1
  , mkSym "step"                "Context.World.WorldProg.step"               .conSym      "AgdaMirror.World.WorldProg.step" .unrelated 3
  , mkSym "_>>=w_"              "Context.World._>>=w_"                       .defSym      "AgdaMirror.World.worldBind" (.related 1 .infixL)
  , mkSym "_>>w_"               "Context.World._>>w_"                        .defSym      "AgdaMirror.World.worldSeq"  (.related 1 .infixL)
  , mkSym "mapWorld"            "Context.World.mapWorld"                     .defSym      "AgdaMirror.World.mapWorld"
  , mkSym "liftWorld"           "Context.World.liftWorld"                    .defSym      "AgdaMirror.World.liftWorld"
  , mkSym "nowMonoW"            "Context.World.nowMonoW"                     .defSym      "AgdaMirror.World.nowMonoW"
  , mkSym "nowWallW"            "Context.World.nowWallW"                     .defSym      "AgdaMirror.World.nowWallW"
  , mkSym "sleepW"              "Context.World.sleepW"                       .defSym      "AgdaMirror.World.sleepW"
  , mkSym "getProgNameW"        "Context.World.getProgNameW"                 .defSym      "AgdaMirror.World.getProgNameW"
  , mkSym "getArgsW"            "Context.World.getArgsW"                     .defSym      "AgdaMirror.World.getArgsW"
  , mkSym "lookupEnvW"          "Context.World.lookupEnvW"                   .defSym      "AgdaMirror.World.lookupEnvW"
  , mkSym "readStdinAllW"       "Context.World.readStdinAllW"                .defSym      "AgdaMirror.World.readStdinAllW"
  , mkSym "readStdinLineW"      "Context.World.readStdinLineW"               .defSym      "AgdaMirror.World.readStdinLineW"
  , mkSym "isTTYStdinW"         "Context.World.isTTYStdinW"                  .defSym      "AgdaMirror.World.isTTYStdinW"
  , mkSym "isTTYStdoutW"        "Context.World.isTTYStdoutW"                 .defSym      "AgdaMirror.World.isTTYStdoutW"
  , mkSym "isTTYStderrW"        "Context.World.isTTYStderrW"                 .defSym      "AgdaMirror.World.isTTYStderrW"
  , mkSym "termSizeW"           "Context.World.termSizeW"                    .defSym      "AgdaMirror.World.termSizeW"
  , mkSym "writeStdoutW"        "Context.World.writeStdoutW"                 .defSym      "AgdaMirror.World.writeStdoutW"
  , mkSym "writeStdoutStrW"     "Context.World.writeStdoutStrW"              .defSym      "AgdaMirror.World.writeStdoutStrW"
  , mkSym "writeStderrW"        "Context.World.writeStderrW"                 .defSym      "AgdaMirror.World.writeStderrW"
  , mkSym "writeStderrStrW"     "Context.World.writeStderrStrW"              .defSym      "AgdaMirror.World.writeStderrStrW"
  , mkSym "readTTYByteW"        "Context.World.readTTYByteW"                 .defSym      "AgdaMirror.World.readTTYByteW"
  , mkSym "readFileW"           "Context.World.readFileW"                    .defSym      "AgdaMirror.World.readFileW"
  , mkSym "writeFileW"          "Context.World.writeFileW"                   .defSym      "AgdaMirror.World.writeFileW"
  , mkSym "mkdirW"              "Context.World.mkdirW"                       .defSym      "AgdaMirror.World.mkdirW"
  , mkSym "symlinkW"            "Context.World.symlinkW"                     .defSym      "AgdaMirror.World.symlinkW"
  , mkSym "unlinkW"             "Context.World.unlinkW"                      .defSym      "AgdaMirror.World.unlinkW"
  , mkSym "statW"               "Context.World.statW"                        .defSym      "AgdaMirror.World.statW"
  , mkSym "tcpExchangeW"        "Context.World.tcpExchangeW"                 .defSym      "AgdaMirror.World.tcpExchangeW"
  , mkSym "tlsExchangeW"        "Context.World.tlsExchangeW"                 .defSym      "AgdaMirror.World.tlsExchangeW"
  , mkSym "gitStepW"            "Context.World.gitStepW"                     .defSym      "AgdaMirror.World.gitStepW"
  , mkSym "gitSummaryW"         "Context.World.gitSummaryW"                  .defSym      "AgdaMirror.World.gitSummaryW"
  , mkSym "webViewportW"        "Context.World.webViewportW"                 .defSym      "AgdaMirror.World.webViewportW"
  , mkSym "webSetTitleW"        "Context.World.webSetTitleW"                 .defSym      "AgdaMirror.World.webSetTitleW"
  , mkSym "webDrawSceneW"       "Context.World.webDrawSceneW"                .defSym      "AgdaMirror.World.webDrawSceneW"
  , mkSym "webHitTestW"         "Context.World.webHitTestW"                  .defSym      "AgdaMirror.World.webHitTestW"
  , mkSym "webPollInputW"       "Context.World.webPollInputW"                .defSym      "AgdaMirror.World.webPollInputW"
  -- §5 Batch CLI & Interactive Reactive Application Shapes
  , mkSym "ExitCode"            "Context.World.ExitCode"                     .typeSym     "AgdaMirror.World.ExitCode"
  , mkSym "CliApp"              "Context.World.CliApp"                       .typeSym     "AgdaMirror.World.CliApp"
  , mkSym "EventPayload"        "Context.World.EventPayload"                 .typeSym     "AgdaMirror.World.EventPayload"
  , mkSym "evTickMs"            "Context.World.EventPayload.evTickMs"        .conSym      "AgdaMirror.World.EventPayload.evTickMs"   .unrelated 1
  , mkSym "evSignal"            "Context.World.EventPayload.evSignal"        .conSym      "AgdaMirror.World.EventPayload.evSignal"   .unrelated 1
  , mkSym "evKey"               "Context.World.EventPayload.evKey"           .conSym      "AgdaMirror.World.EventPayload.evKey"      .unrelated 1
  , mkSym "evResize"            "Context.World.EventPayload.evResize"        .conSym      "AgdaMirror.World.EventPayload.evResize"   .unrelated 2
  , mkSym "evTTYBytes"          "Context.World.EventPayload.evTTYBytes"      .conSym      "AgdaMirror.World.EventPayload.evTTYBytes" .unrelated 1
  , mkSym "evFsWatch"           "Context.World.EventPayload.evFsWatch"       .conSym      "AgdaMirror.World.EventPayload.evFsWatch"  .unrelated 1
  , mkSym "evNetConn"           "Context.World.EventPayload.evNetConn"       .conSym      "AgdaMirror.World.EventPayload.evNetConn"  .unrelated 1
  , mkSym "evGitHook"           "Context.World.EventPayload.evGitHook"       .conSym      "AgdaMirror.World.EventPayload.evGitHook"  .unrelated 1
  , mkSym "evWebInput"          "Context.World.EventPayload.evWebInput"      .conSym      "AgdaMirror.World.EventPayload.evWebInput" .unrelated 1
  , mkSym "Event"               "Context.World.Event"                        .typeSym     "AgdaMirror.World.Event"
  , mkSym "mkEvent"             "Context.World.mkEvent"                      .conSym      "AgdaMirror.World.Event.mkEvent" .unrelated 2
  , mkSym "evHasCap"            "Context.World.Event.evHasCap"               (.projSym 1) "AgdaMirror.World.Event.evHasCap"
  , mkSym "evPayload"           "Context.World.Event.evPayload"              (.projSym 1) "AgdaMirror.World.Event.evPayload"
  , mkSym "liftEvent"           "Context.World.liftEvent"                    .defSym      "AgdaMirror.World.liftEvent"
  , mkSym "ReactiveApp"         "Context.World.ReactiveApp"                  .typeSym     "AgdaMirror.World.ReactiveApp"
  , mkSym "reactiveApp"         "Context.World.reactiveApp"                  .conSym      "AgdaMirror.World.ReactiveApp.reactiveApp" .unrelated 2
  , mkSym "init"                "Context.World.ReactiveApp.init"             (.projSym 2) "AgdaMirror.World.ReactiveApp.init"
  , mkSym "onStep"              "Context.World.ReactiveApp.onStep"           (.projSym 2) "AgdaMirror.World.ReactiveApp.onStep"
  -- §6 Pure Helpers & `runWorldPure`
  , mkSym "lookupEnvVar"        "Context.World.lookupEnvVar"                 .defSym      "AgdaMirror.World.lookupEnvVar"
  , mkSym "takeLineBytes"       "Context.World.takeLineBytes"                .defSym      "AgdaMirror.World.takeLineBytes"
  , mkSym "popByte"             "Context.World.popByte"                      .defSym      "AgdaMirror.World.popByte"
  , mkSym "hasDotSlashPrefix"   "Context.World.hasDotSlashPrefix"            .defSym      "AgdaMirror.World.hasDotSlashPrefix"
  , mkSym "stripDotSlashChars"  "Context.World.stripDotSlashChars"           .defSym      "AgdaMirror.World.stripDotSlashChars"
  , mkSym "normalizeRelPath"    "Context.World.normalizeRelPath"             .defSym      "AgdaMirror.World.normalizeRelPath"
  , mkSym "readVirtualFileFuel" "Context.World.readVirtualFileFuel"          .defSym      "AgdaMirror.World.readVirtualFileFuel"
  , mkSym "readVirtualFile"     "Context.World.readVirtualFile"              .defSym      "AgdaMirror.World.readVirtualFile"
  , mkSym "writeVirtualFileFuel" "Context.World.writeVirtualFileFuel"        .defSym      "AgdaMirror.World.writeVirtualFileFuel"
  , mkSym "writeVirtualFile"    "Context.World.writeVirtualFile"             .defSym      "AgdaMirror.World.writeVirtualFile"
  , mkSym "mkdirVirtual"        "Context.World.mkdirVirtual"                 .defSym      "AgdaMirror.World.mkdirVirtual"
  , mkSym "symlinkVirtual"      "Context.World.symlinkVirtual"               .defSym      "AgdaMirror.World.symlinkVirtual"
  , mkSym "unlinkVirtual"       "Context.World.unlinkVirtual"                .defSym      "AgdaMirror.World.unlinkVirtual"
  , mkSym "statVirtual"         "Context.World.statVirtual"                  .defSym      "AgdaMirror.World.statVirtual"
  , mkSym "isLoopbackHost"      "Context.World.isLoopbackHost"               .defSym      "AgdaMirror.World.isLoopbackHost"
  , mkSym "hostMatches"         "Context.World.hostMatches"                  .defSym      "AgdaMirror.World.hostMatches"
  , mkSym "findEndpoint"        "Context.World.findEndpoint"                 .defSym      "AgdaMirror.World.findEndpoint"
  , mkSym "stubDelayOf"         "Context.World.stubDelayOf"                  .defSym      "AgdaMirror.World.stubDelayOf"
  , mkSym "evalNetExchange"     "Context.World.evalNetExchange"              .defSym      "AgdaMirror.World.evalNetExchange"
  , mkSym "popWebEvent"         "Context.World.popWebEvent"                  .defSym      "AgdaMirror.World.popWebEvent"
  , mkSym "stepWorldPure"       "Context.World.stepWorldPure"                .defSym      "AgdaMirror.World.stepWorldPure"
  , mkSym "runWorldPure"        "Context.World.runWorldPure"                 .defSym      "AgdaMirror.World.runWorldPure"
  , mkSym "runCliPure"          "Context.World.runCliPure"                   .defSym      "AgdaMirror.World.runCliPure"
  , mkSym "runReactiveSteps"    "Context.World.runReactiveSteps"             .defSym      "AgdaMirror.World.runReactiveSteps"
  , mkSym "runReactivePure"     "Context.World.runReactivePure"              .defSym      "AgdaMirror.World.runReactivePure"
  ]

def worldLawsExports : List SymInfo :=
  [ mkSym "bind-pure-left"         "Context.WorldLaws.bind-pure-left"         .defSym "AgdaMirror.WorldLaws.bindPureLeft"
  , mkSym "bind-pure-left-run"     "Context.WorldLaws.bind-pure-left-run"     .defSym "AgdaMirror.WorldLaws.bindPureLeftRun"
  , mkSym "bind-pure-right-run"    "Context.WorldLaws.bind-pure-right-run"    .defSym "AgdaMirror.WorldLaws.bindPureRightRun"
  , mkSym "runWorldPure-bind"      "Context.WorldLaws.runWorldPure-bind"      .defSym "AgdaMirror.WorldLaws.runWorldPureBind"
  , mkSym "bind-assoc-run"         "Context.WorldLaws.bind-assoc-run"         .defSym "AgdaMirror.WorldLaws.bindAssocRun"
  , mkSym "mapWorld-pure"          "Context.WorldLaws.mapWorld-pure"          .defSym "AgdaMirror.WorldLaws.mapWorldPure"
  , mkSym "mapWorld-run"           "Context.WorldLaws.mapWorld-run"           .defSym "AgdaMirror.WorldLaws.mapWorldRun"
  , mkSym "liftWorld-pure"         "Context.WorldLaws.liftWorld-pure"         .defSym "AgdaMirror.WorldLaws.liftWorldPure"
  , mkSym "liftWorld-preserves-run" "Context.WorldLaws.liftWorld-preserves-run" .defSym "AgdaMirror.WorldLaws.liftWorldPreservesRun"
  , mkSym "liftWorld-bind-run"     "Context.WorldLaws.liftWorld-bind-run"     .defSym "AgdaMirror.WorldLaws.liftWorldBindRun"
  , mkSym "eqCap-refl"             "Context.WorldLaws.eqCap-refl"             .defSym "AgdaMirror.WorldLaws.eqCapRefl"
  , mkSym "notHasCap⇒∉"            "Context.WorldLaws.notHasCap⇒∉"            .defSym "AgdaMirror.WorldLaws.notHasCapNotIn"
  , mkSym "step-preserves-clock"   "Context.WorldLaws.step-preserves-clock"   .defSym "AgdaMirror.WorldLaws.stepPreservesClock"
  , mkSym "step-preserves-fs"      "Context.WorldLaws.step-preserves-fs"      .defSym "AgdaMirror.WorldLaws.stepPreservesFs"
  , mkSym "step-preserves-net"     "Context.WorldLaws.step-preserves-net"     .defSym "AgdaMirror.WorldLaws.stepPreservesNet"
  , mkSym "step-preserves-tty"     "Context.WorldLaws.step-preserves-tty"     .defSym "AgdaMirror.WorldLaws.stepPreservesTty"
  , mkSym "prog-preserves-clock"   "Context.WorldLaws.prog-preserves-clock"   .defSym "AgdaMirror.WorldLaws.progPreservesClock"
  , mkSym "prog-preserves-fs"      "Context.WorldLaws.prog-preserves-fs"      .defSym "AgdaMirror.WorldLaws.progPreservesFs"
  , mkSym "prog-preserves-net"     "Context.WorldLaws.prog-preserves-net"     .defSym "AgdaMirror.WorldLaws.progPreservesNet"
  , mkSym "prog-preserves-tty"     "Context.WorldLaws.prog-preserves-tty"     .defSym "AgdaMirror.WorldLaws.progPreservesTty"
  , mkSym "continueReactiveAfter"  "Context.WorldLaws.continueReactiveAfter"  .defSym "AgdaMirror.WorldLaws.continueReactiveAfter"
  , mkSym "runReactiveSteps-++"    "Context.WorldLaws.runReactiveSteps-++"    .defSym "AgdaMirror.WorldLaws.runReactiveStepsAppend"
  ]

def protocolExports : List SymInfo :=
  [ mkSym "Proto"                  "Context.Protocol.Proto"                  .typeSym "AgdaMirror.Protocol.Proto"
  , mkSym "pEnd"                   "Context.Protocol.Proto.pEnd"             .conSym  "AgdaMirror.Protocol.Proto.pEnd"             .unrelated 0
  , mkSym "pSend"                  "Context.Protocol.Proto.pSend"            .conSym  "AgdaMirror.Protocol.Proto.pSend"            .unrelated 2
  , mkSym "pRecv"                  "Context.Protocol.Proto.pRecv"            .conSym  "AgdaMirror.Protocol.Proto.pRecv"            .unrelated 2
  , mkSym "pSelect"                "Context.Protocol.Proto.pSelect"          .conSym  "AgdaMirror.Protocol.Proto.pSelect"          .unrelated 2
  , mkSym "pOffer"                 "Context.Protocol.Proto.pOffer"           .conSym  "AgdaMirror.Protocol.Proto.pOffer"           .unrelated 2
  , mkSym "dual"                   "Context.Protocol.dual"                   .defSym  "AgdaMirror.Protocol.dual"
  , mkSym "dual-involutive"        "Context.Protocol.dual-involutive"        .defSym  "AgdaMirror.Protocol.dualInvolutive"
  , mkSym "EndpointCore"           "Context.Protocol.EndpointCore"           .typeSym "AgdaMirror.Protocol.EndpointCore"
  , mkSym "Endpoint"               "Context.Protocol.Endpoint"               .defSym  "AgdaMirror.Protocol.Endpoint"
  , mkSym "epDone"                 "Context.Protocol.EndpointCore.epDone"    .conSym  "AgdaMirror.Protocol.EndpointCore.epDone"    .unrelated 1
  , mkSym "epStep"                 "Context.Protocol.EndpointCore.epStep"    .conSym  "AgdaMirror.Protocol.EndpointCore.epStep"    .unrelated 3
  , mkSym "epSend"                 "Context.Protocol.EndpointCore.epSend"    .conSym  "AgdaMirror.Protocol.EndpointCore.epSend"    .unrelated 2
  , mkSym "epRecv"                 "Context.Protocol.EndpointCore.epRecv"    .conSym  "AgdaMirror.Protocol.EndpointCore.epRecv"    .unrelated 1
  , mkSym "epSelectL"              "Context.Protocol.EndpointCore.epSelectL" .conSym  "AgdaMirror.Protocol.EndpointCore.epSelectL" .unrelated 1
  , mkSym "epSelectR"              "Context.Protocol.EndpointCore.epSelectR" .conSym  "AgdaMirror.Protocol.EndpointCore.epSelectR" .unrelated 1
  , mkSym "epOffer"                "Context.Protocol.EndpointCore.epOffer"   .conSym  "AgdaMirror.Protocol.EndpointCore.epOffer"   .unrelated 2
  , mkSym "mapEndpoint"            "Context.Protocol.mapEndpoint"            .defSym  "AgdaMirror.Protocol.mapEndpoint"
  , mkSym "liftProgToEndpoint"     "Context.Protocol.liftProgToEndpoint"     .defSym  "AgdaMirror.Protocol.liftProgToEndpoint"
  , mkSym "liftEndpoint"           "Context.Protocol.liftEndpoint"           .defSym  "AgdaMirror.Protocol.liftEndpoint"
  , mkSym "coupleEndpoints"        "Context.Protocol.coupleEndpoints"        .defSym  "AgdaMirror.Protocol.coupleEndpoints"
  , mkSym "composeReactive"        "Context.Protocol.composeReactive"        .defSym  "AgdaMirror.Protocol.composeReactive"
  , mkSym "coupleReactiveTurn"     "Context.Protocol.coupleReactiveTurn"     .defSym  "AgdaMirror.Protocol.coupleReactiveTurn"
  , mkSym "coupleReactive"         "Context.Protocol.coupleReactive"         .defSym  "AgdaMirror.Protocol.coupleReactive"
  , mkSym "couple-done"            "Context.Protocol.couple-done"            .defSym  "AgdaMirror.Protocol.coupleDone"
  , mkSym "couple-send-recv"       "Context.Protocol.couple-send-recv"       .defSym  "AgdaMirror.Protocol.coupleSendRecv"
  , mkSym "couple-recv-send"       "Context.Protocol.couple-recv-send"       .defSym  "AgdaMirror.Protocol.coupleRecvSend"
  , mkSym "couple-selectL-offer"   "Context.Protocol.couple-selectL-offer"   .defSym  "AgdaMirror.Protocol.coupleSelectLOffer"
  , mkSym "couple-selectR-offer"   "Context.Protocol.couple-selectR-offer"   .defSym  "AgdaMirror.Protocol.coupleSelectROffer"
  , mkSym "couple-offer-selectL"   "Context.Protocol.couple-offer-selectL"   .defSym  "AgdaMirror.Protocol.coupleOfferSelectL"
  , mkSym "couple-offer-selectR"   "Context.Protocol.couple-offer-selectR"   .defSym  "AgdaMirror.Protocol.coupleOfferSelectR"
  , mkSym "couple-step-left"       "Context.Protocol.couple-step-left"       .defSym  "AgdaMirror.Protocol.coupleStepLeft"
  , mkSym "couple-preserves-clock" "Context.Protocol.couple-preserves-clock" .defSym  "AgdaMirror.Protocol.couplePreservesClock"
  , mkSym "couple-preserves-fs"    "Context.Protocol.couple-preserves-fs"    .defSym  "AgdaMirror.Protocol.couplePreservesFs"
  , mkSym "couple-preserves-net"   "Context.Protocol.couple-preserves-net"   .defSym  "AgdaMirror.Protocol.couplePreservesNet"
  , mkSym "couple-preserves-tty"   "Context.Protocol.couple-preserves-tty"   .defSym  "AgdaMirror.Protocol.couplePreservesTty"
  ]

def lookupStdModule (modPath : String) : Option (List SymInfo) :=
  match modPath with
  | "Agda.Builtin.Nat"                         => some builtinNatExports
  | "Data.Nat" | "Data.Nat.Base"               => some dataNatExports
  | "Data.Nat.Properties"                      => some dataNatPropsExports
  | "Data.Nat.Show"                            => some dataNatShowExports
  | "Data.Nat.DivMod"                          => some dataNatDivModExports
  | "Agda.Builtin.Int"                         => some builtinIntExports
  | "Data.Integer" | "Data.Integer.Base"       => some dataIntExports
  | "Data.Integer.Properties"                  => some dataIntPropsExports
  | "Agda.Builtin.Bool"                        => some builtinBoolExports
  | "Data.Bool" | "Data.Bool.Base"             => some dataBoolExports
  | "Data.Bool.Properties"                     => some dataBoolPropsExports
  | "Agda.Builtin.List"                        => some builtinListExports
  | "Data.List" | "Data.List.Base"             => some dataListExports
  | "Data.List.Properties"                     => some dataListPropsExports
  | "Data.List.Relation.Unary.Any"             => some dataListAnyExports
  | "Data.List.Relation.Unary.All"             => some dataListAllExports
  | "Data.List.Relation.Binary.Permutation.Propositional"
  | "Data.List.Relation.Binary.Permutation.Propositional.Core" => some (dataPermutationExports modPath)
  | "Agda.Builtin.Maybe" | "Data.Maybe" | "Data.Maybe.Base" => some dataMaybeExports
  | "Agda.Builtin.Sigma"                       => some builtinSigmaExports
  | "Data.Product"                             => some dataProductExports
  | "Data.Sum" | "Data.Sum.Base"               => some dataSumExports
  | "Data.Fin" | "Data.Fin.Base"               => some dataFinExports
  | "Agda.Builtin.Char" | "Data.Char" | "Data.Char.Base" => some dataCharExports
  | "Agda.Builtin.Char.Properties"             => some builtinCharPropsExports
  | "Data.Char.Properties"                     => some dataCharPropsExports
  | "Agda.Builtin.String"                      => some builtinStringExports
  | "Data.String.Base"                         => some dataStringBaseExports
  | "Data.String"                              => some dataStringExports
  | "Agda.Builtin.String.Properties"         => some builtinStringPropsExports
  | "Data.String.Properties"                   => some dataStringPropsExports
  | "Agda.Builtin.Unit" | "Data.Unit" | "Data.Unit.Base" => some dataUnitExports
  | "Data.Unit.Polymorphic" | "Data.Unit.Polymorphic.Base" => some dataPolyUnitExports
  | "Data.Empty"                               => some dataEmptyExports
  | "Relation.Nullary.Decidable" | "Relation.Nullary.Decidable.Core" => some decidableCoreExports
  | "Relation.Nullary"                         => some relNullaryExports
  | "Agda.Builtin.Equality"
  | "Relation.Binary.PropositionalEquality"
  | "Relation.Binary.PropositionalEquality.Core" => some propEqExports
  | "Function" | "Function.Base"               => some functionExports
  | "Context.Taboo"                            => some tabooExports
  | "Context.Blueprint"                        => some blueprintExports
  | "Context.PolyTransport"                    => some polyTransportExports
  | "Context.Terminal"                         => some terminalExports
  | "Context.Filter"                           => some filterExports
  | "Context.Tools.Clock"                      => some clockExports
  | "Context.Tools.ClockLaws"                  => some clockLawsExports
  | "Context.Tools.TermLaws"                   => some termLawsExports
  | "Context.Tools.FuzzGen"                    => some fuzzGenExports
  | "Context.Tools.FsSandbox"                  => some fsSandboxExports
  | "Context.Tools.FsLaws"                     => some fsLawsExports
  | "Context.Tools.NetSandbox"                 => some netSandboxExports
  | "Context.Tools.NetLaws"                    => some netLawsExports
  | "Context.Tools.GitSandbox"                 => some gitSandboxExports
  | "Context.Tools.GitLaws"                    => some gitLawsExports
  | "Context.Tools.WebOperad"                  => some webOperadExports
  | "Context.World"                            => some worldExports
  | "Context.WorldLaws"                        => some worldLawsExports
  | "Context.Protocol"                         => some protocolExports
  | "IO"                                       => some ioExports
  | "Agda.Builtin.IO" | "IO.Primitive"         => some primIOExports
  | "IO.Primitive.Finite"                      => some primFiniteIOExports
  | "System.Environment"                       => some sysEnvExports
  | "System.Environment.Primitive"             => some primSysEnvExports
  | "OwnershipIO.FFI"                          => some ffiSafeExports
  | "OwnershipIO.WorldRunner"                  => some worldRunnerExports
  | _                                          => none

def isStdModuleSafe (modPath : String) : Bool :=
  match modPath with
  | "Context.Blueprint" | "Context.Filter"
  | "IO" | "Agda.Builtin.IO" | "IO.Primitive" | "IO.Primitive.Finite"
  | "System.Environment" | "System.Environment.Primitive"
  | "OwnershipIO.FFI" | "OwnershipIO.WorldRunner" => false
  | _ => (lookupStdModule modPath).isSome

def isStdModuleGuarded (modPath : String) : Bool :=
  modPath == "IO" || modPath == "OwnershipIO.WorldRunner"

end Prism
