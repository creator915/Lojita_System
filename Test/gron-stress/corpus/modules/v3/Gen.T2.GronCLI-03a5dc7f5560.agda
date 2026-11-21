module Gen.T2.GronCLI where

  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Bool using (Bool; false; true)
  open import Data.List using (List; []; _∷_; foldr)
  open import Data.Nat using (ℕ)
  open import Data.String using (String; _++_)
  open import Data.Sum using (inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  import Gen.T0.Gron as Base
  import Gen.T1.GronText as Text
  record Options : Set where
    constructor options
    field
      mode : Base.Mode
      encoding : Text.StatementEncoding
      style : Base.Style
      order : Base.SortMode
      stream : Bool
  data InputSource : Set where
    stdinSource : InputSource
    fileSource : String → InputSource
    urlSource : (address : String) → (insecure : Bool) → (proxy noProxy : String) → InputSource
  record Result : Set where
    constructor result
    field
      exitCode : ℕ
      stdout : String
      stderr : String
  data Invocation : Set where
    completed : Result → Invocation
    requestInput : InputSource → Options → Invocation
  data InputResult : Set where
    contents : String → InputResult
    openFailed : String → InputResult
    readFailed : String → InputResult
    fetchFailed : String → InputResult
  data ProxyPolicy : Set where
    environmentProxy : (excludedHosts : String) → ProxyPolicy
    explicitProxy : (address : String) → ProxyPolicy
  postulate
    usage : String
  postulate
    plan : Base.StdoutAttachment → List String → Invocation
  postulate
    execute : Options → InputResult → Result
  postulate
    selectProxy : (proxy noProxy : String) → ProxyPolicy
  postulate
    defaultProxySelection : (noProxy : String) → selectProxy "" noProxy ≡ environmentProxy noProxy
  postulate
    explicitProxySelection : (proxy noProxy : String) → (primStringEquality proxy "" ≡ false) → selectProxy proxy noProxy ≡ explicitProxy proxy
  postulate
    usageBytes : usage ≡ "Transform JSON (from a file, URL, or stdin) into discrete assignments to make it greppable\n\nUsage:\n  gron [OPTIONS] [FILE|URL|-]\n\nOptions:\n  -u, --ungron     Reverse the operation (turn assignments back into JSON)\n  -v, --values     Print just the values of provided assignments\n  -c, --colorize   Colorize output (default on tty)\n  -m, --monochrome Monochrome (don't colorize output)\n  -s, --stream     Treat each line of input as a separate JSON object\n  -k, --insecure   Disable certificate validation\n  -x, --proxy      Set proxy configuration\n      --noproxy    Comma-separated list of hosts for which not to use a proxy, if one is specified.\n  -j, --json       Represent gron data as JSON stream\n      --no-sort    Don't sort output (faster)\n      --version    Print version information\n\nExit Codes:\n  0	OK\n  1	Failed to open file\n  2	Failed to read input\n  3	Failed to form statements\n  4	Failed to fetch URL\n  5	Failed to parse statements\n  6	Failed to encode JSON\n\nExamples:\n  gron /tmp/apiresponse.json\n  gron http://jsonplaceholder.typicode.com/users/1 \n  curl -s http://jsonplaceholder.typicode.com/users/1 | gron\n  gron http://jsonplaceholder.typicode.com/users/1 | grep company | gron --ungron\n"
  postulate
    version : plan Base.stdoutPipe ("--version" ∷ []) ≡ completed (result 0 "gron version dev\n" "")
  postulate
    longHelp : plan Base.stdoutPipe ("--help" ∷ []) ≡ completed (result 0 "" usage)
  postulate
    shortHelp : plan Base.stdoutPipe ("-h" ∷ []) ≡ completed (result 0 "" usage)
  postulate
    unknownFlag : plan Base.stdoutPipe ("--bogus" ∷ []) ≡ completed (result 2 "" ("flag provided but not defined: -bogus\n" ++ usage))
  postulate
    invalidBoolean : plan Base.stdoutPipe ("--stream=no" ∷ []) ≡ completed (result 2 "" ("invalid boolean value \"no\" for -stream: parse error\n" ++ usage))
  postulate
    missingProxy : plan Base.stdoutPipe ("--proxy" ∷ []) ≡ completed (result 2 "" ("flag needs an argument: -proxy\n" ++ usage))
  postulate
    pipedStdin : plan Base.stdoutPipe [] ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    terminalStdin : plan Base.stdoutTTY [] ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.ansi Base.sortPaths false)
  postulate
    monochromeTerminal : plan Base.stdoutTTY ("-m" ∷ []) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    forcedColor : plan Base.stdoutPipe ("-c" ∷ ("-m" ∷ [])) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.ansi Base.sortPaths false)
  postulate
    afterFlagTerminator : plan Base.stdoutPipe ("--" ∷ ("-" ∷ ("--ungron" ∷ []))) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    fileOperand : plan Base.stdoutPipe ("./gron-probe-absent.json" ∷ []) ≡ requestInput (fileSource "./gron-probe-absent.json") (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    urlOperand : plan Base.stdoutPipe ("http://127.0.0.1:1/" ∷ []) ≡ requestInput (urlSource "http://127.0.0.1:1/" false "" "") (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    urlFlags : plan Base.stdoutPipe ("-k" ∷ ("--proxy=http://proxy.invalid:80" ∷ ("--noproxy=127.0.0.1" ∷ ("http://127.0.0.1:1/" ∷ [])))) ≡ requestInput (urlSource "http://127.0.0.1:1/" true "http://proxy.invalid:80" "127.0.0.1") (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    reversePrecedence : plan Base.stdoutPipe ("-u" ∷ ("-v" ∷ [])) ≡ requestInput stdinSource (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    tupleValues : plan Base.stdoutPipe ("-j" ∷ ("-v" ∷ [])) ≡ requestInput stdinSource (options Base.valuesMode Text.tuples Base.plain Base.sortPaths false)
  postulate
    tupleStream : plan Base.stdoutPipe ("-j" ∷ ("-s" ∷ [])) ≡ requestInput stdinSource (options Base.gronMode Text.tuples Base.plain Base.sortPaths true)
  postulate
    reverseTupleStream : plan Base.stdoutPipe ("-j" ∷ ("-u" ∷ ("-s" ∷ []))) ≡ requestInput stdinSource (options Base.ungronMode Text.tuples Base.plain Base.sortPaths true)
  postulate
    explicitBooleans : plan Base.stdoutPipe ("-stream=false" ∷ ("-m=true" ∷ [])) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  postulate
    unsorted : plan Base.stdoutPipe ("--no-sort" ∷ []) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.skipSort false)
  postulate
    openFailure : (o : Options) → (reason : String) → execute o (openFailed reason) ≡ result 1 "" (reason ++ "\n")
  postulate
    fetchFailure : (o : Options) → (reason : String) → execute o (fetchFailed reason) ≡ result 4 "" (reason ++ "\n")
  postulate
    forwardReadFailure : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths false) (readFailed "read /: is a directory") ≡ result 3 "" "failed to form statements: read /: is a directory\n"
  postulate
    streamReadFailure : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (readFailed "read /: is a directory") ≡ result 3 "json = [];\n" "error reading multiline input: read /: is a directory: %!s(MISSING)\n"
  postulate
    reverseReadFailure : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (readFailed "read /: is a directory") ≡ result 2 "" "failed to read input statements\n"
  postulate
    documentOutput : (enc : Text.StatementEncoding) → (style : Base.Style) → (order : Base.SortMode) → (input : String) → (value : Base.JSON) → (Text.readDocument input ≡ inj₂ value) → execute (options Base.gronMode enc style order false) (contents input) ≡ result 0 (foldr (λ s rest → Text.renderStatement enc style s ++ rest) "" (Base.flatten order value)) ""
  postulate
    documentError : (enc : Text.StatementEncoding) → (style : Base.Style) → (order : Base.SortMode) → (input reason : String) → (Text.readDocument input ≡ inj₁ reason) → execute (options Base.gronMode enc style order false) (contents input) ≡ result 3 "" ("failed to form statements: " ++ (reason ++ "\n"))
  postulate
    emptyStream : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (contents "") ≡ result 0 "json = [];\n" ""
  postulate
    crlfStream : execute (options Base.gronMode Text.tuples Base.plain Base.sortPaths true) (contents "1 2\r\n{}\r\n") ≡ result 0 "[[],[]]\n[[0],1]\n[[1],{}]\n" ""
  postulate
    blankStreamLine : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (contents "1\n\n2\n") ≡ result 3 "json = [];\njson[0] = 1;\n" "failed to form statements: EOF\n"
  postulate
    malformedStreamLine : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (contents "1\nbad\n2\n") ≡ result 3 "json = [];\njson[0] = 1;\n" "failed to form statements: invalid character 'b' looking for beginning of value\n"
  postulate
    extractScalars : execute (options Base.valuesMode Text.assignments Base.ansi Base.sortPaths false) (contents "json = {};\njson.a = [];\njson.a[2] = 1e+02;\njson.n = null;\njson[\"with space\"] = \"<>&\";\n") ≡ result 0 "1e+02\nnull\n<>&\n" ""
  postulate
    extractFromTupleInput : execute (options Base.valuesMode Text.tuples Base.plain Base.sortPaths false) (contents "[[],{}]\n[[\"a\"],[]]\n[[\"a\",2],1e+02]\n[[\"with space\"],\"<>&\"]\n") ≡ result 0 "" ""
  postulate
    extractPartial : execute (options Base.valuesMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\nnoise\n\njson.b = false;\n") ≡ result 5 "1\n" "failed to parse '' as gron statement\n"
  postulate
    extractComment : execute (options Base.valuesMode Text.assignments Base.plain Base.sortPaths false) (contents "// comment\njson.a = 1;\n") ≡ result 0 "1\n" ""
  postulate
    extractLeadingZero : execute (options Base.valuesMode Text.assignments Base.plain Base.sortPaths false) (contents "json = 01;\n") ≡ result 0 "01\n" ""
  postulate
    reverseSparse : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json[\"z z\"] = true;\njson.a[2] = \"<>&\";\njson.a[0].k = 1;\n") ≡ result 0 "{\n  \"a\": [\n    {\n      \"k\": 1\n    },\n    null,\n    \"<>&\"\n  ],\n  \"z z\": true\n}\n" ""
  postulate
    reverseBlankLine : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\n\njson.b = 2;\n") ≡ result 0 "{\n  \"a\": 1,\n  \"b\": 2\n}\n" ""
  postulate
    reverseIndented : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "  json.a = 1;  \r\n") ≡ result 5 "" "no statements were parsed\n"
  postulate
    reverseInlineObject : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\njson.a = {\"x\":2};\njson.a.y = 3;\n") ≡ result 5 "" "ungron failed for `json.a = {`: statement has no value\n"
  postulate
    reverseComment : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\n// comment\n") ≡ result 5 "" "ungron failed for ``: invalid statement\n"
  postulate
    reverseIndentedComment : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "  // comment\njson.a = 1;\n") ≡ result 0 "{\n  \"a\": 1\n}\n" ""
  postulate
    reverseLeadingZero : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json = 01;\n") ≡ result 0 "0\n" ""
  postulate
    reverseNumberSpellings : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1.0;\njson.b = 1e+02;\njson.c = -0;\njson.d = 9007199254740993;\n") ≡ result 0 "{\n  \"a\": 1.0,\n  \"b\": 1e+02,\n  \"c\": -0,\n  \"d\": 9007199254740993\n}\n" ""
  postulate
    reverseBlankTuple : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths false) (contents "[[],{}]\n\n[[\"a\"],1]\n") ≡ result 5 "" "unexpected end of JSON input\n"
  postulate
    assembleTupleStream : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths true) (contents "[[],[]]\n[[2,\"x\"],1]\n") ≡ result 0 "[\n  null,\n  null,\n  {\n    \"x\": 1\n  }\n]\n" ""
  postulate
    reverseTupleNumbers : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths false) (contents ("[[],[]]\n[[0],1.0]\n[[1],1e+02]\n[[2],-0]\n[[3],9007199254740993]\n[[4],9007199254740995]\n" ++ "[[5],1e-6]\n[[6],1e-7]\n[[7],1e20]\n[[8],1e21]\n[[9],-1e-999]\n[[10],0.100000000000000005]\n[[11],5e-324]\n")) ≡ result 0 "[\n  1,\n  100,\n  -0,\n  9007199254740992,\n  9007199254740996,\n  0.000001,\n  1e-7,\n  100000000000000000000,\n  1e+21,\n  -0,\n  0.1,\n  5e-324\n]\n" ""
  postulate
    reverseTupleOverflow : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths false) (contents "[[],1e9999]\n") ≡ result 5 "" "json: cannot unmarshal number 1e9999 into Go value of type float64\n"
  postulate
    reverseTupleFractionalIndex : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths false) (contents "[[1.9],true]\n") ≡ result 5 "" "ungron failed for `json[1.9] = true;`: invalid integer key `1.9`\n"
