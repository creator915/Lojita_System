import Gen.GronBoundary
import LojitaCtx.Cli

namespace Gen.GronDocument
open LojitaCtx.Terminal LojitaCtx.World LojitaCtx.Cli Gen.GronBoundary

-- The boundary machine decides when to reply. The decoder formats the first
-- JSON value, including its original numeric spelling, or explains its syntax error.
def hexDigits := "0123456789abcdef".toList.toArray

def hexByte (b : Byte) : String :=
  String.ofList [hexDigits[b.toNat / 16]!, hexDigits[b.toNat % 16]!]

def invalid (b : Byte) (context : String) : String :=
  let c := if b < 32 || b == 127 then "\\x" ++ hexByte b else String.singleton (Char.ofNat b.toNat)
  "invalid character '" ++ c ++ "' " ++ context

def quoted (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | _ => if c.toNat < 32 then "\\u00" ++ hexByte c.toNat.toUInt8 else String.singleton c) ++ "\""

def keyPath (path key : String) : String :=
  let startId := fun (c : Char) => c.isAlpha || c == '_' || c == '$'
  if key.toList.head?.any startId && key.toList.all (fun c => startId c || c.isDigit) then
    path ++ "." ++ key
  else path ++ "[" ++ quoted key ++ "]"

def hex4 : Nat → Nat → Bytes → Except String (Nat × Bytes)
  | 0, n, bs => .ok (n, bs)
  | _ + 1, _, [] => .error "unexpected EOF"
  | k + 1, n, b :: bs =>
    if !hex b then .error (invalid b "in \\u hexadecimal character escape")
    else hex4 k (16 * n + (if digit b then b.toNat - 48 else (b.toNat % 32) + 9)) bs
termination_by structural k _ _ => k

def unicodeEscape (bs : Bytes) : Except String (Bytes × Bytes) := do
  let (u, rest) ← hex4 4 0 bs
  if 0xd800 ≤ u && u ≤ 0xdbff then
    if let 92 :: 117 :: tail := rest then
      if let .ok (v, more) := hex4 4 0 tail then
        if 0xdc00 ≤ v && v ≤ 0xdfff then
          return (bytes (String.singleton (Char.ofNat (0x10000 + (u - 0xd800) * 1024 + v - 0xdc00))), more)
  let c := if 0xd800 ≤ u && u ≤ 0xdfff then '�' else Char.ofNat u
  return (bytes (String.singleton c), rest)

def stringBytes : Nat → Bytes → Bytes → Except String (String × Bytes)
  | 0, _, _ | _ + 1, _, [] => .error "unexpected EOF"
  | _ + 1, acc, 34 :: bs => .ok (decodeUtf8Lossy acc.reverse, bs)
  | k + 1, acc, 92 :: b :: bs => do
    if b == 117 then
      let (cs, rest) ← unicodeEscape bs
      stringBytes k (cs.reverse ++ acc) rest
    else
      let some c := ([(34,34), (47,47), (92,92), (98,8), (102,12), (110,10), (114,13), (116,9)]
        : List (Byte × Byte)).lookup b | throw (invalid b "in string escape code")
      stringBytes k (c :: acc) bs
  | _ + 1, _, [92] => .error "unexpected EOF"
  | k + 1, acc, b :: bs =>
    if b < 32 then .error (invalid b "in string literal") else stringBytes k (b :: acc) bs
termination_by structural k _ _ => k

def literalTail (name : String) : Bytes → Bytes → Except String Bytes
  | [], bs => .ok bs
  | _ :: _, [] => .error "unexpected EOF"
  | c :: cs, b :: bs =>
    if b == c then literalTail name cs bs
    else .error (invalid b ("in literal " ++ name ++ " (expecting '" ++ String.singleton (Char.ofNat c.toNat) ++ "')"))
termination_by structural cs _ => cs

def numberNeedsDigit : NumberEnd → Option String
  | .sign => some "in numeric literal"
  | .point => some "after decimal point in numeric literal"
  | .exponentMark | .exponentSign => some "in exponent of numeric literal"
  | _ => none

def numberToken (phase : NumberEnd) (rev : Bytes) : Bytes → Except String (String × Bytes)
  | [] => if (numberNeedsDigit phase).isSome then .error "unexpected EOF" else .ok (decodeUtf8Lossy rev.reverse, [])
  | b :: bs =>
    match numberBoundary ⟨#[], .number phase⟩ phase b with
    | some ⟨_, .number next⟩ => numberToken next (b :: rev) bs
    | _ => match numberNeedsDigit phase with
      | some context => .error (invalid b context)
      | none => .ok (decodeUtf8Lossy rev.reverse, b :: bs)
termination_by structural bs => bs

def assignment (path value : String) : String := path ++ " = " ++ value ++ ";\n"

mutual
  def value : Nat → String → Bytes → Except String (List String × Bytes)
    | 0, _, _ => .error "unexpected EOF"
    | k + 1, path, raw => do
      let b :: bs := raw.dropWhile space | throw "unexpected EOF"
      match b with
      | 123 =>
        let tail := bs.dropWhile space
        if let 125 :: rest := tail then return ([assignment path "{}"], rest)
        let (fields, rest) ← objectFields k path tail
        let ordered := fields.mergeSort (fun a b => a.1 ≤ b.1)
        return (assignment path "{}" :: ordered.flatMap Prod.snd, rest)
      | 91 =>
        let tail := bs.dropWhile space
        if let 93 :: rest := tail then return ([assignment path "[]"], rest)
        let (items, rest) ← arrayItems k path 0 tail
        return (assignment path "[]" :: items, rest)
      | 34 =>
        let (s, rest) ← stringBytes (bs.length + 1) [] bs
        return ([assignment path (quoted s)], rest)
      | _ =>
        match (startValue start b) with
        | some ⟨_, .number phase⟩ =>
          let (n, rest) ← numberToken phase [b] bs
          return ([assignment path n], rest)
        | some ⟨_, .literal tail⟩ =>
          let name := decodeUtf8Lossy (b :: tail)
          return ([assignment path name], ← literalTail name tail bs)
        | _ => throw (invalid b "looking for beginning of value")
  termination_by structural k _ _ => k

  def objectFields : Nat → String → Bytes → Except String (List (String × List String) × Bytes)
    | 0, _, _ | _ + 1, _, [] => .error "unexpected EOF"
    | k + 1, path, b :: bs => do
      unless b == 34 do throw (invalid b "looking for beginning of object key string")
      let (key, tail) ← stringBytes (bs.length + 1) [] bs
      let colon :: raw := tail.dropWhile space | throw "unexpected EOF"
      unless colon == 58 do throw (invalid colon "after object key")
      let (lines, tail) ← value k (keyPath path key) raw
      let c :: rest := tail.dropWhile space | throw "unexpected EOF"
      if c == 125 then return ([(key, lines)], rest)
      unless c == 44 do throw (invalid c "after object key:value pair")
      let (more, rest) ← objectFields k path (rest.dropWhile space)
      return ((key, lines) :: more, rest)
  termination_by structural k _ _ => k

  def arrayItems : Nat → String → Nat → Bytes → Except String (List String × Bytes)
    | 0, _, _, _ => .error "unexpected EOF"
    | k + 1, path, i, raw => do
      let (lines, tail) ← value k (path ++ "[" ++ toString i ++ "]") raw
      let c :: rest := tail.dropWhile space | throw "unexpected EOF"
      if c == 93 then return (lines, rest)
      unless c == 44 do throw (invalid c "after array element")
      let (more, rest) ← arrayItems k path (i + 1) rest
      return (lines ++ more, rest)
  termination_by structural k _ _ _ => k
end

def reply (path : String) (raw : Bytes) : StreamReply :=
  let parsed := if raw.all space then Except.error "EOF" else value (2 * raw.length + 2) path raw
  match parsed with
  | .ok (lines, _) => ⟨bytes (String.join lines), [], 0⟩
  | .error e => ⟨[], bytes ("failed to form statements: " ++ e ++ "\n"), 3⟩

end Gen.GronDocument
