module Gen.T2.GronCLI where

  open import Agda.Builtin.Char using (Char; primCharToNat; primNatToChar; primIsPrint; primIsSpace)
  open import Agda.Builtin.Nat using (div-helper)
  open import Agda.Builtin.String using (primStringEquality)
  open import Data.Maybe using (Maybe; nothing; just)
  open import Data.Product using (_×_; _,_)
  open import Data.Bool using (Bool; false; true; not; _∧_; _∨_; if_then_else_)
  open import Data.List using (List; []; _∷_; any; foldr; reverse) renaming (_++_ to _++ˡ_)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _<ᵇ_)
  open import Data.String using (String; _++_; fromList; toList)
  open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; map)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  import Gen.T0.Gron as Base
  import Gen.T1.GronText as Text
  open import Data.Bool using (Bool; false; true)
  open import Data.List using (List; []; _∷_; foldr)
  open import Data.Nat using (ℕ)
  open import Data.String using (String; _++_)
  open import Data.Sum using (inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_)
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
  usage : String
  usage = "Transform JSON (from a file, URL, or stdin) into discrete assignments to make it greppable\n\nUsage:\n  gron [OPTIONS] [FILE|URL|-]\n\nOptions:\n  -u, --ungron     Reverse the operation (turn assignments back into JSON)\n  -v, --values     Print just the values of provided assignments\n  -c, --colorize   Colorize output (default on tty)\n  -m, --monochrome Monochrome (don't colorize output)\n  -s, --stream     Treat each line of input as a separate JSON object\n  -k, --insecure   Disable certificate validation\n  -x, --proxy      Set proxy configuration\n      --noproxy    Comma-separated list of hosts for which not to use a proxy, if one is specified.\n  -j, --json       Represent gron data as JSON stream\n      --no-sort    Don't sort output (faster)\n      --version    Print version information\n\nExit Codes:\n  0	OK\n  1	Failed to open file\n  2	Failed to read input\n  3	Failed to form statements\n  4	Failed to fetch URL\n  5	Failed to parse statements\n  6	Failed to encode JSON\n\nExamples:\n  gron /tmp/apiresponse.json\n  gron http://jsonplaceholder.typicode.com/users/1 \n  curl -s http://jsonplaceholder.typicode.com/users/1 | gron\n  gron http://jsonplaceholder.typicode.com/users/1 | grep company | gron --ungron\n"
  private
    record Flags : Set where
      field
        wantReverse : Bool
        wantValues : Bool
        wantColor : Bool
        wantMono : Bool
        wantStream : Bool
        allowInsecure : Bool
        wantTuples : Bool
        omitSort : Bool
        wantVersion : Bool
        proxySetting : String
        noProxySetting : String
  private
    defaultFlags : Flags
    defaultFlags = record { wantReverse = false ; wantValues = false ; wantColor = false ; wantMono = false ; wantStream = false ; allowInsecure = false ; wantTuples = false ; omitSort = false ; wantVersion = false ; proxySetting = "" ; noProxySetting = "" }
  private
    data FlagAction : Set where
      switchFlag : (Bool → Flags → Flags) → FlagAction
      stringFlag : (String → Flags → Flags) → FlagAction
      helpFlag : FlagAction
      unregisteredFlag : FlagAction
  private
    flagNames : List (List String × FlagAction)
    flagNames = (("u" ∷ ("ungron" ∷ [])) , switchFlag (λ value state → record state { wantReverse = value })) ∷ ((("v" ∷ ("values" ∷ [])) , switchFlag (λ value state → record state { wantValues = value })) ∷ ((("c" ∷ ("colorize" ∷ [])) , switchFlag (λ value state → record state { wantColor = value })) ∷ ((("m" ∷ ("monochrome" ∷ [])) , switchFlag (λ value state → record state { wantMono = value })) ∷ ((("s" ∷ ("stream" ∷ [])) , switchFlag (λ value state → record state { wantStream = value })) ∷ ((("k" ∷ ("insecure" ∷ [])) , switchFlag (λ value state → record state { allowInsecure = value })) ∷ ((("j" ∷ ("json" ∷ [])) , switchFlag (λ value state → record state { wantTuples = value })) ∷ ((("no-sort" ∷ []) , switchFlag (λ value state → record state { omitSort = value })) ∷ ((("version" ∷ []) , switchFlag (λ value state → record state { wantVersion = value })) ∷ ((("x" ∷ ("proxy" ∷ [])) , stringFlag (λ value state → record state { proxySetting = value })) ∷ ((("noproxy" ∷ []) , stringFlag (λ value state → record state { noProxySetting = value })) ∷ ((("h" ∷ ("help" ∷ [])) , helpFlag) ∷ [])))))))))))
  private
    lookupFlag : String → List (List String × FlagAction) → FlagAction
    lookupFlag name [] = unregisteredFlag
    lookupFlag name ((aliases , action) ∷ rest) = if any (primStringEquality name) aliases then action else lookupFlag name rest
  private
    readBool : String → Maybe Bool
    readBool text = if any (primStringEquality text) ("1" ∷ ("t" ∷ ("T" ∷ ("true" ∷ ("TRUE" ∷ ("True" ∷ [])))))) then just true else (if any (primStringEquality text) ("0" ∷ ("f" ∷ ("F" ∷ ("false" ∷ ("FALSE" ∷ ("False" ∷ [])))))) then just false else nothing)
  private
    hexDigits : ℕ → ℕ → List Char → List Char
    hexDigits zero n acc = acc
    hexDigits (suc digits) n acc = let quotient = div-helper 0 15 n 15; digit = n ∸ (16 * quotient); c = primNatToChar (if (digit <ᵇ 10) then (48 + digit) else (87 + digit)) in hexDigits digits quotient (c ∷ acc)
  private
    quoteFlagChar : Char → List Char
    quoteFlagChar c = let n = primCharToNat c in if (n ≡ᵇ 34) then toList "\\\"" else (if (n ≡ᵇ 92) then toList "\\\\" else (if (n ≡ᵇ 7) then toList "\\a" else (if (n ≡ᵇ 8) then toList "\\b" else (if (n ≡ᵇ 9) then toList "\\t" else (if (n ≡ᵇ 10) then toList "\\n" else (if (n ≡ᵇ 11) then toList "\\v" else (if (n ≡ᵇ 12) then toList "\\f" else (if (n ≡ᵇ 13) then toList "\\r" else (if ((n <ᵇ 32) ∨ (n ≡ᵇ 127)) then ('\\' ∷ ('x' ∷ hexDigits 2 n [])) else (if ((n ≡ᵇ 32) ∨ (primIsPrint c ∧ not (primIsSpace c))) then (c ∷ []) else (if (n <ᵇ 65536) then ('\\' ∷ ('u' ∷ hexDigits 4 n [])) else ('\\' ∷ ('U' ∷ hexDigits 8 n [])))))))))))))
  private
    quoteFlagValue : String → String
    quoteFlagValue text = fromList ('\"' ∷ foldr (λ c rest → quoteFlagChar c ++ˡ rest) ('\"' ∷ []) (toList text))
  private
    flagError : String → Result
    flagError message = result 2 "" (message ++ ("\n" ++ usage))
  private
    data FlagStep : Set where
      flagOperand : FlagStep
      flagTerminator : FlagStep
      flagDone : Result → FlagStep
      flagUpdated : Flags → FlagStep
      flagArgument : String → (String → Flags) → FlagStep
  private
    applyFlag : String → Maybe String → Flags → FlagAction → FlagStep
    applyFlag name attached state helpFlag = flagDone (result 0 "" usage)
    applyFlag name attached state unregisteredFlag = flagDone (flagError ("flag provided but not defined: -" ++ name))
    applyFlag name nothing state (switchFlag update) = flagUpdated (update true state)
    applyFlag name (just text) state (switchFlag update) with readBool text
    applyFlag name (just text) state (switchFlag update) | (just value) = flagUpdated (update value state)
    applyFlag name (just text) state (switchFlag update) | nothing = flagDone (flagError ("invalid boolean value " ++ (quoteFlagValue text ++ (" for -" ++ (name ++ ": parse error")))))
    applyFlag name nothing state (stringFlag update) = flagArgument name (λ text → update text state)
    applyFlag name (just text) state (stringFlag update) = flagUpdated (update text state)
  private
    splitFlag : List Char → List Char × Maybe String
    splitFlag [] = [] , nothing
    splitFlag ('=' ∷ cs) = [] , just (fromList cs)
    splitFlag (c ∷ cs) with splitFlag cs
    splitFlag (c ∷ cs) | (name , attached) = (c ∷ name) , attached
  private
    stepNamed : String → List Char → Flags → FlagStep
    stepNamed original [] state = flagTerminator
    stepNamed original ('-' ∷ _) state = flagDone (flagError ("bad flag syntax: " ++ original))
    stepNamed original ('=' ∷ _) state = flagDone (flagError ("bad flag syntax: " ++ original))
    stepNamed original (c ∷ cs) state with splitFlag (c ∷ cs)
    stepNamed original (c ∷ cs) state | (chars , attached) = let name = fromList chars in applyFlag name attached state (lookupFlag name flagNames)
  private
    stepFlag : String → Flags → FlagStep
    stepFlag arg state with toList arg
    stepFlag arg state | ('-' ∷ ('-' ∷ rest)) = stepNamed arg rest state
    stepFlag arg state | ('-' ∷ (c ∷ rest)) = stepNamed arg (c ∷ rest) state
    stepFlag arg state | _ = flagOperand
  private
    startsWith : List Char → List Char → Bool
    startsWith [] chars = true
    startsWith (c ∷ prefix) [] = false
    startsWith (c ∷ prefix) (d ∷ chars) = if (primCharToNat c ≡ᵇ primCharToNat d) then startsWith prefix chars else false
  private
    selectSource : Flags → List String → InputSource
    selectSource state [] = stdinSource
    selectSource state (address ∷ _) = if primStringEquality address "-" then stdinSource else (let chars = toList address in if (startsWith (toList "http://") chars ∨ startsWith (toList "https://") chars) then urlSource address (Flags.allowInsecure state) (Flags.proxySetting state) (Flags.noProxySetting state) else fileSource address)
  private
    finishPlan : Base.StdoutAttachment → Flags → List String → Invocation
    finishPlan attachment state operands = if Flags.wantVersion state then completed (result 0 "gron version dev\n" "") else requestInput (selectSource state operands) (options (Base.selectMode (Base.modeFlags (Flags.wantReverse state) (Flags.wantValues state))) (if Flags.wantTuples state then Text.tuples else Text.assignments) (Base.selectStyle (Base.colorFlags (Flags.wantColor state) (Flags.wantMono state) attachment)) (if Flags.omitSort state then Base.skipSort else Base.sortPaths) (Flags.wantStream state))
  private
    scanArgs : Base.StdoutAttachment → Flags → List String → Invocation
    scanArgs attachment state [] = finishPlan attachment state []
    scanArgs attachment state (arg ∷ rest) with stepFlag arg state
    scanArgs attachment state (arg ∷ rest) | flagOperand = finishPlan attachment state (arg ∷ rest)
    scanArgs attachment state (arg ∷ rest) | flagTerminator = finishPlan attachment state rest
    scanArgs attachment state (arg ∷ rest) | (flagDone outcome) = completed outcome
    scanArgs attachment state (arg ∷ rest) | (flagUpdated updated) = scanArgs attachment updated rest
    scanArgs attachment state (arg ∷ rest) | (flagArgument name update) with rest
    scanArgs attachment state (arg ∷ rest) | (flagArgument name update) | [] = completed (flagError ("flag needs an argument: -" ++ name))
    scanArgs attachment state (arg ∷ rest) | (flagArgument name update) | (value ∷ more) = scanArgs attachment (update value) more
  plan : Base.StdoutAttachment → List String → Invocation
  plan attachment args = scanArgs attachment defaultFlags args
  private
    dropCR : List Char → List Char
    dropCR [] = []
    dropCR (c ∷ rev) = if (primCharToNat c ≡ᵇ 13) then rev else (c ∷ rev)
  private
    finishLine : List Char → String
    finishLine rev = fromList (reverse (dropCR rev))
  private
    splitLines : List Char → List Char → List String
    splitLines [] [] = []
    splitLines (c ∷ rev) [] = finishLine (c ∷ rev) ∷ []
    splitLines rev (c ∷ rest) = if (primCharToNat c ≡ᵇ 10) then (finishLine rev ∷ splitLines [] rest) else splitLines (c ∷ rev) rest
  private
    prependOutput : String → Result → Result
    prependOutput prefix (result code output diagnostic) = result code (prefix ++ output) diagnostic
  private
    renderStatements : Text.StatementEncoding → Base.Style → List Base.Statement → String
    renderStatements enc style = foldr (λ s rest → Text.renderStatement enc style s ++ rest) ""
  private
    formError : String → Result
    formError reason = result 3 "" ("failed to form statements: " ++ (reason ++ "\n"))
  private
    forwardDocument : Text.StatementEncoding → Base.Style → Base.SortMode → (String ⊎ Base.JSON) → Result
    forwardDocument enc style order (inj₁ reason) = formError reason
    forwardDocument enc style order (inj₂ value) = result 0 (renderStatements enc style (Base.flatten order value)) ""
  private
    indexedStatement : ℕ → Base.Statement → Base.Statement
    indexedStatement i (Base.statement path value) = Base.statement (Base.index i ∷ path) value
  private
    streamHeader : Text.StatementEncoding → Base.Style → String
    streamHeader enc style = Text.renderStatement enc style (Base.statement [] (Base.jArray []))
  private
    forwardRows : Text.StatementEncoding → Base.Style → Base.SortMode → ℕ → List String → Result
    forwardRows enc style order i [] = result 0 "" ""
    forwardRows enc style order i (line ∷ rest) with Text.readDocument line
    forwardRows enc style order i (line ∷ rest) | (inj₁ reason) = formError reason
    forwardRows enc style order i (line ∷ rest) | (inj₂ value) = prependOutput (foldr (λ s output → Text.renderStatement enc style (indexedStatement i s) ++ output) "" (Base.flatten order value)) (forwardRows enc style order (suc i) rest)
  private
    selectedAssignment : String → Text.AssignmentRead
    selectedAssignment line with toList line
    selectedAssignment line | [] = Text.skipped
    selectedAssignment line | (c ∷ cs) with Base.keyNotation (fromList (c ∷ []))
    selectedAssignment line | (c ∷ cs) | Base.bracketed = Text.skipped
    selectedAssignment line | (c ∷ cs) | Base.dotted = if any (λ d → primCharToNat d ≡ᵇ 61) cs then Text.readAssignment line else Text.skipped
  private
    valueError : String → Result
    valueError fragment = result 5 "" ("failed to parse '" ++ (fragment ++ "' as gron statement\n"))
  private
    extractValues : List String → Result
    extractValues [] = result 0 "" ""
    extractValues (line ∷ rest) with primStringEquality line "" | selectedAssignment line
    extractValues (line ∷ rest) | true | _ = valueError ""
    extractValues (line ∷ rest) | false | Text.skipped = extractValues rest
    extractValues (line ∷ rest) | false | (Text.rejected fragment _) = valueError fragment
    extractValues (line ∷ rest) | false | (Text.accepted s) = prependOutput (foldr (λ value output → value ++ ("\n" ++ output)) "" (Base.valueLines (s ∷ []))) (extractValues rest)
  private
    reverseLine : Text.StatementEncoding → String → String ⊎ Maybe Base.Statement
    reverseLine Text.tuples line = map (λ reason → reason) just (Text.readTuple line)
    reverseLine Text.assignments line with selectedAssignment line
    reverseLine Text.assignments line | Text.skipped = inj₂ nothing
    reverseLine Text.assignments line | (Text.accepted s) = inj₂ (just s)
    reverseLine Text.assignments line | (Text.rejected fragment reason) = inj₁ ("ungron failed for `" ++ (fragment ++ ("`: " ++ reason)))
  private
    collectStatements : (String → String ⊎ Maybe Base.Statement) → List String → String ⊎ List Base.Statement
    collectStatements readLine [] = inj₂ []
    collectStatements readLine (line ∷ rest) with readLine line
    collectStatements readLine (line ∷ rest) | (inj₁ reason) = inj₁ reason
    collectStatements readLine (line ∷ rest) | (inj₂ nothing) = collectStatements readLine rest
    collectStatements readLine (line ∷ rest) | (inj₂ (just s)) = map (λ reason → reason) (λ statements → s ∷ statements) (collectStatements readLine rest)
  private
    reverseOutput : Base.Style → (String ⊎ List Base.Statement) → Result
    reverseOutput style (inj₁ reason) = result 5 "" (reason ++ "\n")
    reverseOutput style (inj₂ statements) with Base.assemble statements
    reverseOutput style (inj₂ statements) | nothing = result 5 "" "no statements were parsed\n"
    reverseOutput style (inj₂ statements) | (just value) = result 0 (Text.renderJSON style value) ""
  execute : Options → InputResult → Result
  execute o (openFailed reason) = result 1 "" (reason ++ "\n")
  execute o (fetchFailed reason) = result 4 "" (reason ++ "\n")
  execute (options Base.gronMode enc style order false) (readFailed reason) = formError reason
  execute (options Base.gronMode enc style order true) (readFailed reason) = result 3 (streamHeader enc style) ("error reading multiline input: " ++ (reason ++ ": %!s(MISSING)\n"))
  execute o (readFailed reason) = result 2 "" "failed to read input statements\n"
  execute (options Base.gronMode enc style order false) (contents input) = forwardDocument enc style order (Text.readDocument input)
  execute (options Base.gronMode enc style order true) (contents input) = prependOutput (streamHeader enc style) (forwardRows enc style order zero (splitLines [] (toList input)))
  execute (options Base.valuesMode enc style order stream) (contents input) = extractValues (splitLines [] (toList input))
  execute (options Base.ungronMode enc style order stream) (contents input) = reverseOutput style (collectStatements (reverseLine enc) (splitLines [] (toList input)))
  usageBytes : usage ≡ "Transform JSON (from a file, URL, or stdin) into discrete assignments to make it greppable\n\nUsage:\n  gron [OPTIONS] [FILE|URL|-]\n\nOptions:\n  -u, --ungron     Reverse the operation (turn assignments back into JSON)\n  -v, --values     Print just the values of provided assignments\n  -c, --colorize   Colorize output (default on tty)\n  -m, --monochrome Monochrome (don't colorize output)\n  -s, --stream     Treat each line of input as a separate JSON object\n  -k, --insecure   Disable certificate validation\n  -x, --proxy      Set proxy configuration\n      --noproxy    Comma-separated list of hosts for which not to use a proxy, if one is specified.\n  -j, --json       Represent gron data as JSON stream\n      --no-sort    Don't sort output (faster)\n      --version    Print version information\n\nExit Codes:\n  0	OK\n  1	Failed to open file\n  2	Failed to read input\n  3	Failed to form statements\n  4	Failed to fetch URL\n  5	Failed to parse statements\n  6	Failed to encode JSON\n\nExamples:\n  gron /tmp/apiresponse.json\n  gron http://jsonplaceholder.typicode.com/users/1 \n  curl -s http://jsonplaceholder.typicode.com/users/1 | gron\n  gron http://jsonplaceholder.typicode.com/users/1 | grep company | gron --ungron\n"
  usageBytes = refl
  version : plan Base.stdoutPipe ("--version" ∷ []) ≡ completed (result 0 "gron version dev\n" "")
  version = refl
  longHelp : plan Base.stdoutPipe ("--help" ∷ []) ≡ completed (result 0 "" usage)
  longHelp = refl
  shortHelp : plan Base.stdoutPipe ("-h" ∷ []) ≡ completed (result 0 "" usage)
  shortHelp = refl
  unknownFlag : plan Base.stdoutPipe ("--bogus" ∷ []) ≡ completed (result 2 "" ("flag provided but not defined: -bogus\n" ++ usage))
  unknownFlag = refl
  invalidBoolean : plan Base.stdoutPipe ("--stream=no" ∷ []) ≡ completed (result 2 "" ("invalid boolean value \"no\" for -stream: parse error\n" ++ usage))
  invalidBoolean = refl
  missingProxy : plan Base.stdoutPipe ("--proxy" ∷ []) ≡ completed (result 2 "" ("flag needs an argument: -proxy\n" ++ usage))
  missingProxy = refl
  pipedStdin : plan Base.stdoutPipe [] ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  pipedStdin = refl
  terminalStdin : plan Base.stdoutTTY [] ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.ansi Base.sortPaths false)
  terminalStdin = refl
  monochromeTerminal : plan Base.stdoutTTY ("-m" ∷ []) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  monochromeTerminal = refl
  forcedColor : plan Base.stdoutPipe ("-c" ∷ ("-m" ∷ [])) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.ansi Base.sortPaths false)
  forcedColor = refl
  afterFlagTerminator : plan Base.stdoutPipe ("--" ∷ ("-" ∷ ("--ungron" ∷ []))) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  afterFlagTerminator = refl
  fileOperand : plan Base.stdoutPipe ("./gron-probe-absent.json" ∷ []) ≡ requestInput (fileSource "./gron-probe-absent.json") (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  fileOperand = refl
  urlOperand : plan Base.stdoutPipe ("http://127.0.0.1:1/" ∷ []) ≡ requestInput (urlSource "http://127.0.0.1:1/" false "" "") (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  urlOperand = refl
  urlFlags : plan Base.stdoutPipe ("-k" ∷ ("--proxy=http://proxy.invalid:80" ∷ ("--noproxy=127.0.0.1" ∷ ("http://127.0.0.1:1/" ∷ [])))) ≡ requestInput (urlSource "http://127.0.0.1:1/" true "http://proxy.invalid:80" "127.0.0.1") (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  urlFlags = refl
  reversePrecedence : plan Base.stdoutPipe ("-u" ∷ ("-v" ∷ [])) ≡ requestInput stdinSource (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false)
  reversePrecedence = refl
  tupleValues : plan Base.stdoutPipe ("-j" ∷ ("-v" ∷ [])) ≡ requestInput stdinSource (options Base.valuesMode Text.tuples Base.plain Base.sortPaths false)
  tupleValues = refl
  tupleStream : plan Base.stdoutPipe ("-j" ∷ ("-s" ∷ [])) ≡ requestInput stdinSource (options Base.gronMode Text.tuples Base.plain Base.sortPaths true)
  tupleStream = refl
  reverseTupleStream : plan Base.stdoutPipe ("-j" ∷ ("-u" ∷ ("-s" ∷ []))) ≡ requestInput stdinSource (options Base.ungronMode Text.tuples Base.plain Base.sortPaths true)
  reverseTupleStream = refl
  explicitBooleans : plan Base.stdoutPipe ("-stream=false" ∷ ("-m=true" ∷ [])) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.sortPaths false)
  explicitBooleans = refl
  unsorted : plan Base.stdoutPipe ("--no-sort" ∷ []) ≡ requestInput stdinSource (options Base.gronMode Text.assignments Base.plain Base.skipSort false)
  unsorted = refl
  openFailure : (o : Options) → (reason : String) → execute o (openFailed reason) ≡ result 1 "" (reason ++ "\n")
  openFailure o reason = refl
  fetchFailure : (o : Options) → (reason : String) → execute o (fetchFailed reason) ≡ result 4 "" (reason ++ "\n")
  fetchFailure o reason = refl
  forwardReadFailure : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths false) (readFailed "read /: is a directory") ≡ result 3 "" "failed to form statements: read /: is a directory\n"
  forwardReadFailure = refl
  streamReadFailure : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (readFailed "read /: is a directory") ≡ result 3 "json = [];\n" "error reading multiline input: read /: is a directory: %!s(MISSING)\n"
  streamReadFailure = refl
  reverseReadFailure : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (readFailed "read /: is a directory") ≡ result 2 "" "failed to read input statements\n"
  reverseReadFailure = refl
  documentOutput : (enc : Text.StatementEncoding) → (style : Base.Style) → (order : Base.SortMode) → (input : String) → (value : Base.JSON) → (Text.readDocument input ≡ inj₂ value) → execute (options Base.gronMode enc style order false) (contents input) ≡ result 0 (foldr (λ s rest → Text.renderStatement enc style s ++ rest) "" (Base.flatten order value)) ""
  documentOutput enc style order input value eq = cong (forwardDocument enc style order) eq
  documentError : (enc : Text.StatementEncoding) → (style : Base.Style) → (order : Base.SortMode) → (input reason : String) → (Text.readDocument input ≡ inj₁ reason) → execute (options Base.gronMode enc style order false) (contents input) ≡ result 3 "" ("failed to form statements: " ++ (reason ++ "\n"))
  documentError enc style order input reason eq = cong (forwardDocument enc style order) eq
  emptyStream : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (contents "") ≡ result 0 "json = [];\n" ""
  emptyStream = refl
  crlfStream : execute (options Base.gronMode Text.tuples Base.plain Base.sortPaths true) (contents "1 2\r\n{}\r\n") ≡ result 0 "[[],[]]\n[[0],1]\n[[1],{}]\n" ""
  crlfStream = refl
  blankStreamLine : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (contents "1\n\n2\n") ≡ result 3 "json = [];\njson[0] = 1;\n" "failed to form statements: EOF\n"
  blankStreamLine = refl
  malformedStreamLine : execute (options Base.gronMode Text.assignments Base.plain Base.sortPaths true) (contents "1\nbad\n2\n") ≡ result 3 "json = [];\njson[0] = 1;\n" "failed to form statements: invalid character 'b' looking for beginning of value\n"
  malformedStreamLine = refl
  extractScalars : execute (options Base.valuesMode Text.assignments Base.ansi Base.sortPaths false) (contents "json = {};\njson.a = [];\njson.a[2] = 1e+02;\njson.n = null;\njson[\"with space\"] = \"<>&\";\n") ≡ result 0 "1e+02\nnull\n<>&\n" ""
  extractScalars = refl
  extractFromTupleInput : execute (options Base.valuesMode Text.tuples Base.plain Base.sortPaths false) (contents "[[],{}]\n[[\"a\"],[]]\n[[\"a\",2],1e+02]\n[[\"with space\"],\"<>&\"]\n") ≡ result 0 "" ""
  extractFromTupleInput = refl
  extractPartial : execute (options Base.valuesMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\nnoise\n\njson.b = false;\n") ≡ result 5 "1\n" "failed to parse '' as gron statement\n"
  extractPartial = refl
  reverseSparse : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json[\"z z\"] = true;\njson.a[2] = \"<>&\";\njson.a[0].k = 1;\n") ≡ result 0 "{\n  \"a\": [\n    {\n      \"k\": 1\n    },\n    null,\n    \"<>&\"\n  ],\n  \"z z\": true\n}\n" ""
  reverseSparse = refl
  reverseBlankLine : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\n\njson.b = 2;\n") ≡ result 0 "{\n  \"a\": 1,\n  \"b\": 2\n}\n" ""
  reverseBlankLine = refl
  reverseIndented : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "  json.a = 1;  \r\n") ≡ result 5 "" "no statements were parsed\n"
  reverseIndented = refl
  reverseInlineObject : execute (options Base.ungronMode Text.assignments Base.plain Base.sortPaths false) (contents "json.a = 1;\njson.a = {\"x\":2};\njson.a.y = 3;\n") ≡ result 5 "" "ungron failed for `json.a = {`: statement has no value\n"
  reverseInlineObject = refl
  reverseBlankTuple : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths false) (contents "[[],{}]\n\n[[\"a\"],1]\n") ≡ result 5 "" "unexpected end of JSON input\n"
  reverseBlankTuple = refl
  assembleTupleStream : execute (options Base.ungronMode Text.tuples Base.plain Base.sortPaths true) (contents "[[],[]]\n[[2,\"x\"],1]\n") ≡ result 0 "[\n  null,\n  null,\n  {\n    \"x\": 1\n  }\n]\n" ""
  assembleTupleStream = refl
