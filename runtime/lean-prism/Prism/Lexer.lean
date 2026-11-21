import Prism.Outcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `Prism.Lexer`: 100% Agda-Faithful Whitespace-Delimited Lexer & Layout Tracker

Agda's concrete lexer differs radically from C/Lean/Haskell:
only whitespace and `( ) { } ⦃ ⦄ ; @ " '` (plus leading `\` for ASCII lambda and
`{! !}` / `{- -}`) separate tokens. Characters like `:`, `=`, `,`, `+`, `→`, `[`, `]`,
`λ`, `∀` are *ordinary identifier characters* when not separated by whitespace!
For instance:
- `(1, 2)` lexes `"1,"` as a single identifier (scope error in Agda);
- `(x:ℕ)` lexes `"x:ℕ"` as a single identifier (scope error in Agda);
- `λx → x` lexes `"λx"` as a single identifier, whereas `\x -> x` lexes `\` + `"x"`;
- `[1]` lexes `"[1]"` as a single identifier, whereas `[ 1 ]` lexes `"["`, `1`, `"]"`.
-/

namespace Prism

inductive TokKind : Type where
  | lparen | rparen
  | lbrace | rbrace
  | lbrace2 | rbrace2
  | semi | atSign
  | kwModule | kwWhere | kwImport | kwOpen
  | kwUsing | kwHiding | kwRenaming
  | kwPublic | kwPrivate | kwInstance | kwAbstract | kwMutual
  | kwData | kwRecord | kwConstructor | kwInductive | kwCoinductive
  | kwField | kwVariable | kwPostulate | kwSyntax | kwPattern
  | kwInfix | kwInfixL | kwInfixR
  | kwLet | kwIn | kwDo | kwWith | kwRewrite
  | kwForall | kwLambda
  | kwSet : Nat → TokKind
  | kwProp
  | symArrow | symLeftArrow | symColon | symEq | symBar | symEllipsis | symDot
  | underscore | question | holeLit
  | pragma : String → TokKind
  | natLit : Nat → TokKind
  | strLit : String → TokKind
  | charLit : Char → TokKind
  | dotIdent : String → TokKind
  | ident : String → TokKind
  | eof
  deriving Repr, BEq, Inhabited

structure Token : Type where
  kind        : TokKind
  line        : Nat
  col         : Nat
  firstOnLine : Bool
  deriving Repr, BEq, Inhabited

private def isDelimChar (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\r' || c == '\t' ||
  c == '(' || c == ')' || c == '{' || c == '}' ||
  c == '⦃' || c == '⦄' || c == ';' || c == '@' ||
  c == '"' || c == '\''

private def allAsciiDigits (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all (fun c => '0' <= c && c <= '9')

private def parseDecimal (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private def parseSubscriptDigits (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else
    let rec go : List Char → Nat → Option Nat
      | [], acc => some acc
      | c :: rest, acc =>
          if '₀' <= c && c <= '₉' then
            go rest (acc * 10 + (c.toNat - '₀'.toNat))
          else none
    go cs 0

private def classifyWord (w : String) : PrismOutcome TokKind :=
  match w with
  | "module"      => .translated .kwModule
  | "where"       => .translated .kwWhere
  | "import"      => .translated .kwImport
  | "open"        => .translated .kwOpen
  | "using"       => .translated .kwUsing
  | "hiding"      => .translated .kwHiding
  | "renaming"    => .translated .kwRenaming
  | "public"      => .translated .kwPublic
  | "private"     => .translated .kwPrivate
  | "instance"    => .translated .kwInstance
  | "abstract"    => .translated .kwAbstract
  | "mutual"      => .translated .kwMutual
  | "data"        => .translated .kwData
  | "record"      => .translated .kwRecord
  | "constructor" => .translated .kwConstructor
  | "inductive"   => .translated .kwInductive
  | "coinductive" => .translated .kwCoinductive
  | "field"       => .translated .kwField
  | "variable"    => .translated .kwVariable
  | "postulate"   => .translated .kwPostulate
  | "syntax"      => .translated .kwSyntax
  | "pattern"     => .translated .kwPattern
  | "infix"       => .translated .kwInfix
  | "infixl"      => .translated .kwInfixL
  | "infixr"      => .translated .kwInfixR
  | "let"         => .translated .kwLet
  | "in"          => .translated .kwIn
  | "do"          => .translated .kwDo
  | "with"        => .translated .kwWith
  | "rewrite"     => .translated .kwRewrite
  | "forall"      => .translated .kwForall
  | "∀"           => .translated .kwForall
  | "λ"           => .translated .kwLambda
  | "->"          => .translated .symArrow
  | "→"           => .translated .symArrow
  | "<-"          => .translated .symLeftArrow
  | "←"           => .translated .symLeftArrow
  | ":"           => .translated .symColon
  | "="           => .translated .symEq
  | "|"           => .translated .symBar
  | "..."         => .translated .symEllipsis
  | "."           => .translated .symDot
  | "_"           => .translated .underscore
  | "?"           => .translated .question
  | "Set"         => .translated (.kwSet 0)
  | "Prop"        => .translated .kwProp
  | _ =>
      let cs := w.toList
      if allAsciiDigits cs then
        .translated (.natLit (parseDecimal cs))
      else if w.startsWith "Set" then
        match parseSubscriptDigits (cs.drop 3) with
        | some lvl => .translated (.kwSet lvl)
        | none     => .translated (.ident w)
      else if w.startsWith "Prop" && (parseSubscriptDigits (cs.drop 4)).isSome then
        .translated .kwProp
      else if w.startsWith "." then
        let rest := String.ofList (cs.drop 1)
        if rest.isEmpty || rest.startsWith "." then
          .syntaxErr s!"malformed dotted token '{w}'"
        else
          .translated (.dotIdent rest)
      else if w.contains '.' then
        let parts := w.splitOn "."
        if parts.any String.isEmpty then
          .syntaxErr s!"malformed qualified identifier '{w}'"
        else
          .translated (.ident w)
      else
        .translated (.ident w)

private partial def lexBlockComment (cs : List Char) (depth line col : Nat) :
    PrismOutcome (List Char × Nat × Nat) :=
  match cs with
  | [] => .syntaxErr "unclosed block comment '{-'"
  | '{' :: '-' :: rest => lexBlockComment rest (depth + 1) line (col + 2)
  | '-' :: '}' :: rest =>
      if depth == 1 then .translated (rest, line, col + 2)
      else lexBlockComment rest (depth - 1) line (col + 2)
  | '\n' :: rest => lexBlockComment rest depth (line + 1) 1
  | '\t' :: _    => .syntaxErr s!"line {line}: tab character inside comment/layout"
  | _ :: rest    => lexBlockComment rest depth line (col + 1)

private partial def lexPragma (cs : List Char) (acc : List Char) (line col : Nat) :
    PrismOutcome (String × List Char × Nat × Nat) :=
  match cs with
  | [] => .syntaxErr "unclosed pragma '{-#'"
  | '#' :: '-' :: '}' :: rest =>
      .translated ((String.ofList acc.reverse).trimAscii.toString, rest, line, col + 3)
  | '\n' :: rest => lexPragma rest ('\n' :: acc) (line + 1) 1
  | c :: rest    => lexPragma rest (c :: acc) line (col + 1)

private partial def lexHole (cs : List Char) (depth line col : Nat) :
    PrismOutcome (List Char × Nat × Nat) :=
  match cs with
  | [] => .syntaxErr "unclosed interaction hole '{!'"
  | '{' :: '!' :: rest => lexHole rest (depth + 1) line (col + 2)
  | '!' :: '}' :: rest =>
      if depth == 1 then .translated (rest, line, col + 2)
      else lexHole rest (depth - 1) line (col + 2)
  | '\n' :: rest => lexHole rest depth (line + 1) 1
  | _ :: rest    => lexHole rest depth line (col + 1)

private def hexDigitVal? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then some (c.toNat - '0'.toNat)
  else if 'a' <= c && c <= 'f' then some (10 + (c.toNat - 'a'.toNat))
  else if 'A' <= c && c <= 'F' then some (10 + (c.toNat - 'A'.toNat))
  else none

private def decodeEscape : List Char → PrismOutcome (Char × List Char × Nat)
  | '"' :: rest               => .translated ('"', rest, 1)
  | '\'' :: rest              => .translated ('\'', rest, 1)
  | '\\' :: rest              => .translated ('\\', rest, 1)
  | 'n' :: rest               => .translated ('\n', rest, 1)
  | 'r' :: rest               => .translated ('\r', rest, 1)
  | 't' :: rest               => .translated ('\t', rest, 1)
  | '0' :: rest               => .translated (Char.ofNat 0, rest, 1)
  | 'N' :: 'U' :: 'L' :: rest => .translated (Char.ofNat 0, rest, 3)
  | 'E' :: 'S' :: 'C' :: rest => .translated (Char.ofNat 27, rest, 3)
  | 'x' :: rest               =>
      let (hexCs, after) := rest.span (fun c => (hexDigitVal? c).isSome)
      if hexCs.isEmpty then .syntaxErr "malformed '\\x' hex escape"
      else
        let v := hexCs.foldl (fun acc c => acc * 16 + (hexDigitVal? c).getD 0) 0
        if v < 1114112 && !(55296 <= v && v < 57344) then
          .translated (Char.ofNat v, after, 1 + hexCs.length)
        else
          .syntaxErr "out-of-range '\\x' Unicode scalar value"
  | []                        => .syntaxErr "unterminated escape sequence"
  | _                         => .bot "unsupported Agda string/char escape sequence"

private partial def lexString (cs : List Char) (acc : List Char) (line col : Nat) :
    PrismOutcome (String × List Char × Nat × Nat) :=
  match cs with
  | []           => .syntaxErr s!"line {line}: unclosed string literal"
  | '\n' :: _    => .syntaxErr s!"line {line}: raw newline inside string literal"
  | '"' :: rest  => .translated (String.ofList acc.reverse, rest, line, col + 1)
  | '\\' :: rest => do
      let (ch, rest', consumed) ← decodeEscape rest
      lexString rest' (ch :: acc) line (col + 1 + consumed)
  | c :: rest    => lexString rest (c :: acc) line (col + 1)

private def lexCharLit (cs : List Char) (line col : Nat) :
    PrismOutcome (Char × List Char × Nat) :=
  match cs with
  | [] | '\n' :: _ => .syntaxErr s!"line {line}: unclosed character literal"
  | '\'' :: _      => .syntaxErr s!"line {line}: empty character literal"
  | '\\' :: rest   => do
      let (ch, rest', consumed) ← decodeEscape rest
      match rest' with
      | '\'' :: after => .translated (ch, after, col + 2 + consumed)
      | _             => .syntaxErr s!"line {line}: malformed character literal"
  | c :: '\'' :: after => .translated (c, after, col + 2)
  | _ => .syntaxErr s!"line {line}: multi-character or unclosed character literal"

private partial def takeWord : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | c :: cs, acc =>
      if isDelimChar c then (acc.reverse, c :: cs)
      else takeWord cs (c :: acc)

private partial def skipLineComment : List Char → List Char
  | [] => []
  | '\n' :: rest => '\n' :: rest
  | _ :: rest    => skipLineComment rest

partial def tokenizeAgda (src : String) : PrismOutcome (List Token) :=
  let rec loop (cs : List Char) (line col : Nat) (first : Bool) (acc : List Token) :
      PrismOutcome (List Token) :=
    match cs with
    | [] =>
        let eofTok : Token := { kind := .eof, line := line, col := col, firstOnLine := first }
        .translated (eofTok :: acc).reverse
    | ' ' :: rest =>
        loop rest line (col + 1) first acc
    | '\r' :: rest =>
        loop rest line col first acc
    | '\n' :: rest =>
        loop rest (line + 1) 1 true acc
    | '\t' :: _ =>
        .syntaxErr s!"line {line}, col {col}: tab characters are forbidden in Agda layout"
    | '{' :: '-' :: '#' :: rest => do
        let (body, rest', line', col') ← lexPragma rest [] line (col + 3)
        let tok : Token := { kind := .pragma body, line := line, col := col, firstOnLine := first }
        loop rest' line' col' false (tok :: acc)
    | '{' :: '-' :: rest => do
        let (rest', line', col') ← lexBlockComment rest 1 line (col + 2)
        loop rest' line' col' first acc
    | '{' :: '!' :: rest => do
        let (rest', line', col') ← lexHole rest 1 line (col + 2)
        let tok : Token := { kind := .holeLit, line := line, col := col, firstOnLine := first }
        loop rest' line' col' false (tok :: acc)
    | '{' :: '{' :: rest =>
        let tok : Token := { kind := .lbrace2, line := line, col := col, firstOnLine := first }
        loop rest line (col + 2) false (tok :: acc)
    | '}' :: '}' :: rest =>
        let tok : Token := { kind := .rbrace2, line := line, col := col, firstOnLine := first }
        loop rest line (col + 2) false (tok :: acc)
    | '⦃' :: rest =>
        let tok : Token := { kind := .lbrace2, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '⦄' :: rest =>
        let tok : Token := { kind := .rbrace2, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '(' :: rest =>
        let tok : Token := { kind := .lparen, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | ')' :: rest =>
        let tok : Token := { kind := .rparen, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '{' :: rest =>
        let tok : Token := { kind := .lbrace, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '}' :: rest =>
        let tok : Token := { kind := .rbrace, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | ';' :: rest =>
        let tok : Token := { kind := .semi, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '@' :: rest =>
        let tok : Token := { kind := .atSign, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '\\' :: rest =>
        let tok : Token := { kind := .kwLambda, line := line, col := col, firstOnLine := first }
        loop rest line (col + 1) false (tok :: acc)
    | '"' :: rest => do
        let (s, rest', line', col') ← lexString rest [] line (col + 1)
        let tok : Token := { kind := .strLit s, line := line, col := col, firstOnLine := first }
        loop rest' line' col' false (tok :: acc)
    | '\'' :: rest => do
        let (ch, rest', col') ← lexCharLit rest line (col + 1)
        let tok : Token := { kind := .charLit ch, line := line, col := col, firstOnLine := first }
        loop rest' line col' false (tok :: acc)
    | '-' :: '-' :: rest =>
        -- Check whether `--` starts a line comment: in Agda `--` at token start is always a comment!
        let rest' := skipLineComment rest
        loop rest' line col first acc
    | '.' :: '(' :: rest =>
        -- Dot pattern `.(e)`
        let dotTok : Token := { kind := .symDot, line := line, col := col, firstOnLine := first }
        let lpTok  : Token := { kind := .lparen, line := line, col := col + 1, firstOnLine := false }
        loop rest line (col + 2) false (lpTok :: dotTok :: acc)
    | _ => do
        let (wChars, rest) := takeWord cs []
        let w := String.ofList wChars
        let kind ← classifyWord w
        let tok : Token := { kind := kind, line := line, col := col, firstOnLine := first }
        loop rest line (col + wChars.length) false (tok :: acc)
  loop src.toList 1 1 true []

end Prism
