module Gen.T1.GronText where

  open import Agda.Builtin.Char using (Char; primNatToChar)
  open import Data.Bool using (true)
  open import Data.List using (List; []; _∷_; map)
  open import Data.Product using (_,_)
  open import Data.String using (String; fromList; toList; _++_)
  import Data.Sum as Sum
  open import Data.Unit using (⊤)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Context.Blueprint using (PortLift; portLift; keepPort; Commutes₁)
  import Gen.T0.Gron as Base
  open Sum using (_⊎_; inj₁; inj₂)
  data StatementEncoding : Set where
    assignments : StatementEncoding
    tuples : StatementEncoding
  data AssignmentRead : Set where
    skipped : AssignmentRead
    accepted : Base.Statement → AssignmentRead
    rejected : (fragment reason : String) → AssignmentRead
  notationOf : List Char → Base.KeyNotation
  notationOf ('.' ∷ _) = Base.dotted
  notationOf _ = Base.bracketed
  keyPort : PortLift Base.KeyNotation (List Char)
  keyPort = portLift notationOf
  postulate
    readDocument : String → String ⊎ Base.JSON
  postulate
    readAssignment : String → AssignmentRead
  postulate
    readValueAssignment : String → AssignmentRead
  postulate
    readTuple : String → String ⊎ Base.Statement
  postulate
    renderKey : String → List Char
  postulate
    renderStatement : StatementEncoding → Base.Style → Base.Statement → String
  postulate
    renderJSON : Base.Style → Base.JSON → String
  postulate
    keySquare : Commutes₁ (keepPort String) keyPort (λ _ → ⊤) _≡_ Base.keyNotation renderKey
  postulate
    dottedKeyText : (k : String) → (Base.keyNotation k ≡ Base.dotted) → renderKey k ≡ ('.' ∷ toList k)
  postulate
    reservedKeyText : fromList (renderKey "class") ≡ "[\"class\"]"
  postulate
    bracketKeyText : fromList (renderKey "a\"b\\c\n") ≡ "[\"a\\\"b\\\\c\\n\"]"
  postulate
    joiningKeyText : fromList (renderKey (fromList ('a' ∷ (primNatToChar 8204 ∷ [])))) ≡ fromList ('[' ∷ ('\"' ∷ ('a' ∷ (primNatToChar 8204 ∷ ('\"' ∷ (']' ∷ []))))))
  postulate
    firstDocument : readDocument "1 2" ≡ inj₂ (Base.jNumber "1")
  postulate
    numericSpellings : readDocument "[1.0,1e+02,-0,9007199254740993,1e-09,1e-7,1e20]" ≡ inj₂ (Base.jArray (Base.jNumber "1.0" ∷ (Base.jNumber "1e+02" ∷ (Base.jNumber "-0" ∷ (Base.jNumber "9007199254740993" ∷ (Base.jNumber "1e-09" ∷ (Base.jNumber "1e-7" ∷ (Base.jNumber "1e20" ∷ []))))))))
  postulate
    stringEscapes : Sum.map (λ reason → reason) (λ value → renderStatement assignments Base.plain (Base.statement [] value)) (readDocument "\"<>&\\u2028\\u2029\\ud800\"") ≡ inj₂ "json = \"<>&\\u2028\\u2029�\";\n"
  postulate
    duplicateDocument : Sum.map (λ reason → reason) (Base.flatten Base.sortPaths) (readDocument "{\"a\":{\"x\":1},\"a\":{\"y\":2},\"b\":1,\"b\":2}") ≡ inj₂ (Base.statement [] (Base.jObject []) ∷ (Base.statement (Base.key "a" ∷ []) (Base.jObject []) ∷ (Base.statement (Base.key "a" ∷ (Base.key "y" ∷ [])) (Base.jNumber "2") ∷ (Base.statement (Base.key "b" ∷ []) (Base.jNumber "2") ∷ []))))
  postulate
    emptyDocument : readDocument "" ≡ inj₁ "EOF"
  postulate
    truncatedDocument : readDocument "{\"k\":100" ≡ inj₁ "unexpected EOF"
  postulate
    badArrayValue : readDocument "[29,]" ≡ inj₁ "invalid character ']' looking for beginning of value"
  postulate
    missingObjectColon : readDocument "{\"146\" 146}" ≡ inj₁ "invalid character '1' after object key"
  postulate
    missingObjectComma : readDocument "{\"k\":219 \"j\":0}" ≡ inj₁ "invalid character '\"' after object key:value pair"
  postulate
    missingArrayComma : readDocument "[72 null]" ≡ inj₁ "invalid character 'n' after array element"
  postulate
    badStringEscape : readDocument "\"105\\q\"" ≡ inj₁ "invalid character 'q' in string escape code"
  postulate
    badLiteral : readDocument "[nul14]" ≡ inj₁ "invalid character '1' in literal null (expecting 'l')"
  postulate
    badExponent : readDocument "[71e+]" ≡ inj₁ "invalid character ']' in exponent of numeric literal"
  postulate
    badHexEscape : readDocument "[\"\\u245g\"]" ≡ inj₁ "invalid character 'g' in \\u hexadecimal character escape"
  postulate
    emptyAssignmentLine : readAssignment "" ≡ skipped
  postulate
    compactAssignment : readAssignment "json.a=1;" ≡ accepted (Base.statement (Base.key "a" ∷ []) (Base.jNumber "1"))
  postulate
    rewrittenRoot : readAssignment "renamed.a = 1;" ≡ accepted (Base.statement (Base.key "renamed" ∷ (Base.key "a" ∷ [])) (Base.jNumber "1"))
  postulate
    escapedAssignmentKey : readAssignment "json[\"a = b.c\\\"d\\\\e\"] = true;" ≡ accepted (Base.statement (Base.key "a = b.c\"d\\e" ∷ []) (Base.jBool true))
  postulate
    paddedIndex : readAssignment "json.a[01] = 3;" ≡ accepted (Base.statement (Base.key "a" ∷ (Base.index 1 ∷ [])) (Base.jNumber "3"))
  postulate
    trailingComment : readAssignment "json.a = 1; // tail" ≡ accepted (Base.statement (Base.key "a" ∷ []) (Base.jNumber "1"))
  postulate
    largeExponent : readAssignment "json = 1e9999;" ≡ accepted (Base.statement [] (Base.jNumber "1e9999"))
  postulate
    assignmentNumberSpellings : map readAssignment ("json.a = 1.0;" ∷ ("json.b = 1e+02;" ∷ ("json.c = -0;" ∷ ("json.d = 9007199254740993;" ∷ [])))) ≡ (accepted (Base.statement (Base.key "a" ∷ []) (Base.jNumber "1.0")) ∷ (accepted (Base.statement (Base.key "b" ∷ []) (Base.jNumber "1e+02")) ∷ (accepted (Base.statement (Base.key "c" ∷ []) (Base.jNumber "-0")) ∷ (accepted (Base.statement (Base.key "d" ∷ []) (Base.jNumber "9007199254740993")) ∷ []))))
  postulate
    assignmentFirstNumber : map readAssignment ("json = 01;" ∷ ("json = -012;" ∷ ("json = 01.5;" ∷ ("json = 1 2;" ∷ [])))) ≡ (accepted (Base.statement [] (Base.jNumber "0")) ∷ (accepted (Base.statement [] (Base.jNumber "-0")) ∷ (accepted (Base.statement [] (Base.jNumber "0")) ∷ (accepted (Base.statement [] (Base.jNumber "1")) ∷ []))))
  postulate
    missingSemicolon : readAssignment "json.a = 1" ≡ rejected "json.a = 1" "statement has no value"
  postulate
    leadingZeroWithoutSemicolon : readAssignment "json = 01" ≡ rejected "json = 01" "statement has no value"
  postulate
    leadingComment : readAssignment "// comment" ≡ rejected "" "invalid statement"
  postulate
    indentedComment : readAssignment "  // comment" ≡ skipped
  postulate
    singleQuotedKey : readAssignment "json['a'] = 2;" ≡ rejected "json[" "invalid statement"
  postulate
    inlineObject : readAssignment "json.a = {\"x\":2};" ≡ rejected "json.a = {" "statement has no value"
  postulate
    valuesComment : readValueAssignment "// comment" ≡ skipped
  postulate
    valuesLeadingZero : readValueAssignment "json = 01;" ≡ accepted (Base.statement [] (Base.jNumber "01"))
  postulate
    valuesScalarAssignments : map readValueAssignment ("json.a[2] = 1e+02;" ∷ ("json.n = null;" ∷ ("json[\"with space\"] = \"<>&\";" ∷ []))) ≡ (accepted (Base.statement (Base.key "a" ∷ (Base.index 2 ∷ [])) (Base.jNumber "1e+02")) ∷ (accepted (Base.statement (Base.key "n" ∷ []) Base.jNull) ∷ (accepted (Base.statement (Base.key "with space" ∷ []) (Base.jString "<&>")) ∷ [])))
  postulate
    tupleRoot : readTuple "[[],{}]" ≡ inj₂ (Base.statement [] (Base.jObject []))
  postulate
    tupleEmptyArray : readTuple "[[],[]]" ≡ inj₂ (Base.statement [] (Base.jArray []))
  postulate
    tuplePath : readTuple "[[\"a\",2],\"<>&\"]" ≡ inj₂ (Base.statement (Base.key "a" ∷ (Base.index 2 ∷ [])) (Base.jString "<&>"))
  postulate
    tuplePathType : readTuple "[[true],1]" ≡ inj₁ "invalid JSON layout"
  postulate
    tupleArity : readTuple "[[\"a\"],1,2]" ≡ inj₁ "invalid JSON layout"
  postulate
    blankTuple : readTuple "" ≡ inj₁ "unexpected end of JSON input"
  postulate
    tupleBinary64Numbers : map readTuple ("[[0],1.0]" ∷ ("[[1],1e+02]" ∷ ("[[2],-0]" ∷ ("[[3],9007199254740993]" ∷ ("[[4],9007199254740995]" ∷ ("[[5],1e-6]" ∷ ("[[6],1e-7]" ∷ ("[[7],1e20]" ∷ ("[[8],1e21]" ∷ ("[[9],-1e-999]" ∷ ("[[10],0.100000000000000005]" ∷ ("[[11],5e-324]" ∷ [])))))))))))) ≡ (inj₂ (Base.statement (Base.index 0 ∷ []) (Base.jNumber "1")) ∷ (inj₂ (Base.statement (Base.index 1 ∷ []) (Base.jNumber "100")) ∷ (inj₂ (Base.statement (Base.index 2 ∷ []) (Base.jNumber "-0")) ∷ (inj₂ (Base.statement (Base.index 3 ∷ []) (Base.jNumber "9007199254740992")) ∷ (inj₂ (Base.statement (Base.index 4 ∷ []) (Base.jNumber "9007199254740996")) ∷ (inj₂ (Base.statement (Base.index 5 ∷ []) (Base.jNumber "0.000001")) ∷ (inj₂ (Base.statement (Base.index 6 ∷ []) (Base.jNumber "1e-7")) ∷ (inj₂ (Base.statement (Base.index 7 ∷ []) (Base.jNumber "100000000000000000000")) ∷ (inj₂ (Base.statement (Base.index 8 ∷ []) (Base.jNumber "1e+21")) ∷ (inj₂ (Base.statement (Base.index 9 ∷ []) (Base.jNumber "-0")) ∷ (inj₂ (Base.statement (Base.index 10 ∷ []) (Base.jNumber "0.1")) ∷ (inj₂ (Base.statement (Base.index 11 ∷ []) (Base.jNumber "5e-324")) ∷ []))))))))))))
  postulate
    tupleNestedValue : readTuple "[[],{\"a\":[1.0,1e+02,-0,9007199254740993]}]" ≡ inj₁ "invalid JSON layout"
  postulate
    tupleNumberOverflow : readTuple "[[],1e9999]" ≡ inj₁ "json: cannot unmarshal number 1e9999 into Go value of type float64"
  postulate
    tupleFractionalIndex : readTuple "[[1.9],true]" ≡ inj₁ "ungron failed for `json[1.9] = true;`: invalid integer key `1.9`"
  postulate
    tupleExponentIndex : readTuple "[[1e0],true]" ≡ inj₂ (Base.statement (Base.index 1 ∷ []) (Base.jBool true))
  postulate
    plainAssignment : renderStatement assignments Base.plain (Base.statement (Base.key "items" ∷ (Base.index 10 ∷ [])) (Base.jNumber "1e+02")) ≡ "json.items[10] = 1e+02;\n"
  postulate
    plainBracketAssignment : renderStatement assignments Base.plain (Base.statement (Base.key "two words" ∷ []) (Base.jObject [])) ≡ "json[\"two words\"] = {};\n"
  postulate
    plainTuple : renderStatement tuples Base.plain (Base.statement (Base.key "items" ∷ (Base.index 2 ∷ [])) Base.jNull) ≡ "[[\"items\",2],null]\n"
  postulate
    coloredAssignment : renderStatement assignments Base.ansi (Base.statement (Base.key "items" ∷ (Base.index 1 ∷ [])) (Base.jBool true)) ≡ "[34;1mjson[0;22m.[34;1mitems[0;22m[35m[[0m[31m1[0m[35m][0m = [36mtrue[0m;\n"
  postulate
    coloredBracketAssignment : renderStatement assignments Base.ansi (Base.statement (Base.key "two words" ∷ []) (Base.jObject [])) ≡ "[34;1mjson[0;22m[35m[[0m[33m\"two words\"[0m[35m][0m = [35m{}[0m;\n"
  postulate
    coloredTuple : renderStatement tuples Base.ansi (Base.statement (Base.key "a b" ∷ (Base.index 0 ∷ [])) (Base.jBool true)) ≡ "[35m[[0m[35m[[0m[33m\"a b\"[0m,[31m0[0m[35m][0m,[36mtrue[0m[35m][0m\n"
  postulate
    prettyJSON : renderJSON Base.plain (Base.jObject (("a" , Base.jArray (Base.jObject (("k" , Base.jNumber "1") ∷ []) ∷ (Base.jNull ∷ (Base.jString "<&>" ∷ [])))) ∷ (("z z" , Base.jBool true) ∷ []))) ≡ "{\n  \"a\": [\n    {\n      \"k\": 1\n    },\n    null,\n    \"<>&\"\n  ],\n  \"z z\": true\n}\n"
  postulate
    coloredJSON : renderJSON Base.ansi (Base.jObject (("a" , Base.jNumber "9007199254740993") ∷ (("b" , Base.jNumber "1e+02") ∷ (("c" , Base.jNumber "-0") ∷ (("d" , Base.jString (fromList (primNatToChar 8232 ∷ (primNatToChar 8233 ∷ ('<' ∷ ('&' ∷ ('>' ∷ (primNatToChar 0 ∷ [])))))))) ∷ []))))) ≡ ("[35m{[0m[34;1m\"[0;22m[34;1ma[0;22m[34;1m\"[0;22m[1m:[22m[31m9007199254740993[0m[1m,[22m" ++ ("[34;1m\"[0;22m[34;1mb[0;22m[34;1m\"[0;22m[1m:[22m[31m1e+02[0m[1m,[22m" ++ ("[34;1m\"[0;22m[34;1mc[0;22m[34;1m\"[0;22m[1m:[22m[31m-0[0m[1m,[22m" ++ "[34;1m\"[0;22m[34;1md[0;22m[34;1m\"[0;22m[1m:[22m[32m\"[0m[33m\\u2028\\u2029<>&\\u0000[0m[32m\"[0m[35m}[0m\n")))
