import LojitaCtx.PosixChannel

namespace Gen.GronBoundary
open LojitaCtx.Terminal LojitaCtx.PosixChannel

-- JSON prefix transitions from probe_167.lean. A terminal transition can denote either
-- a complete document or a syntax error. Both unblock the decoder.
inductive Frame : Type where
  | array
  | object

inductive NumberEnd : Type where
  | sign
  | zero
  | integer
  | point
  | fraction
  | exponentMark
  | exponentSign
  | exponent

/-- The byte boundary only needs to know which part of the JSON grammar is open. -/
inductive Position : Type where
  | value
  | firstItem
  | field (allowEnd : Bool)
  | colon
  | afterValue
  | string (key : Bool)
  | escape (key : Bool)
  | unicode (key : Bool) (remaining : Nat)
  | literal (remaining : Bytes)
  | number (phase : NumberEnd)

structure Boundary : Type where
  frames : Array Frame
  position : Position

def start : Boundary := ⟨#[], .value⟩
def taking (s : Boundary) (p : Position) : Option Boundary := some {s with position := p}

def finishFrame (s : Boundary) : Option Boundary :=
  if s.frames.size ≤ 1 then none
  else some ⟨s.frames.pop, .afterValue⟩

def space (b : Byte) : Bool := b == 32 || b == 9 || b == 10 || b == 13
def digit (b : Byte) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57
def hex (b : Byte) : Bool :=
  digit b || (65 ≤ b.toNat && b.toNat ≤ 70) || (97 ≤ b.toNat && b.toNat ≤ 102)

/-- After a top-level scalar, even a non-whitespace byte is sufficient lookahead.
    Inside an open container the same byte must satisfy the enclosing grammar. -/
def afterValue (s : Boundary) (b : Byte) : Option Boundary :=
  match s.frames[s.frames.size - 1]? with
  | none => none
  | some f =>
    if space b then taking s .afterValue
    else match f with
    | .array =>
      if b == 44 then taking s .value else if b == 93 then finishFrame s else none
    | .object =>
      if b == 44 then taking s (.field false) else if b == 125 then finishFrame s else none

def openFrame (s : Boundary) (f : Frame) (p : Position) : Option Boundary :=
  if s.frames.size < 10000 then some ⟨s.frames.push f, p⟩ else none

def startValue (s : Boundary) (b : Byte) : Option Boundary :=
  if space b then taking s .value
  else match b with
  | 91 => openFrame s .array .firstItem
  | 123 => openFrame s .object (.field true)
  | 34 => taking s (.string false)
  | 45 => taking s (.number .sign)
  | 48 => taking s (.number .zero)
  | 116 => taking s (.literal [114, 117, 101])
  | 102 => taking s (.literal [97, 108, 115, 101])
  | 110 => taking s (.literal [117, 108, 108])
  | _ => if digit b then taking s (.number .integer) else none

def exponentMarker (b : Byte) : Bool := b == 69 || b == 101
def numberTail (s : Boundary) (allowPoint : Bool) (b : Byte) : Option Boundary :=
  if allowPoint && b == 46 then taking s (.number .point)
  else if exponentMarker b then taking s (.number .exponentMark)
  else afterValue s b

def numberBoundary (s : Boundary) (p : NumberEnd) (b : Byte) : Option Boundary :=
  match p with
  | .sign =>
    if b == 48 then taking s (.number .zero)
    else if digit b then taking s (.number .integer) else none
  | .zero => numberTail s true b
  | .integer => if digit b then taking s (.number .integer) else numberTail s true b
  | .point => if digit b then taking s (.number .fraction) else none
  | .fraction => if digit b then taking s (.number .fraction) else numberTail s false b
  | .exponentMark =>
    if b == 43 || b == 45 then taking s (.number .exponentSign)
    else if digit b then taking s (.number .exponent) else none
  | .exponentSign => if digit b then taking s (.number .exponent) else none
  | .exponent => if digit b then taking s (.number .exponent) else afterValue s b

/-- A terminal transition makes the first document or its syntax error observable.
    The decoder and renderer remain responsible for the exact reply bytes. -/
def advance (s : Boundary) (b : Byte) : Option Boundary :=
  match s.position with
  | .value => startValue s b
  | .firstItem =>
    if space b then taking s .firstItem
    else if b == 93 then finishFrame s
    else startValue s b
  | .field allowEnd =>
    if space b then taking s (.field allowEnd)
    else if b == 34 then taking s (.string true)
    else if allowEnd && b == 125 then finishFrame s
    else none
  | .colon =>
    if space b then taking s .colon
    else if b == 58 then taking s .value else none
  | .afterValue => afterValue s b
  | .string key =>
    if b == 34 then taking s (if key then .colon else .afterValue)
    else if b == 92 then taking s (.escape key)
    else if b.toNat < 32 then none else taking s (.string key)
  | .escape key =>
    if b == 117 then taking s (.unicode key 4)
    else if [34, 47, 92, 98, 102, 110, 114, 116].contains b then taking s (.string key)
    else none
  | .unicode key remaining =>
    if !hex b then none
    else if remaining ≤ 1 then taking s (.string key)
    else taking s (.unicode key (remaining - 1))
  | .literal [] => afterValue s b
  | .literal (wanted :: rest) =>
    if b != wanted then none
    else taking s (if rest.isEmpty then .afterValue else .literal rest)
  | .number phase => numberBoundary s phase b

def scanner : ByteScanner Boundary Unit where
  init := start
  onByte s b := match advance s b with
    | some next => .more next
    | none => .done ()
  onEOF _ := ()

end Gen.GronBoundary
