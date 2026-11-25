import LojitaCtx.Posix.Stream

namespace LojitaCtx.Posix

/-- Linux anonymous pipes use a bounded ring of 4096-byte pages on x86-64.
    Reading from the head advances its offset. It does not free the slot until
    every byte in the page has been consumed. -/
structure PipePage where
  readable : Nat
  endOffset : Nat
  deriving Inhabited

abbrev PipePages := List PipePage

namespace PipePages

def pageBytes : Nat := 4096

def packed (count : Nat) : PipePages :=
  let tail := count % pageBytes
  List.replicate (count / pageBytes) ⟨pageBytes,pageBytes⟩ ++
    (if tail == 0 then [] else [⟨tail,tail⟩])

def consume : PipePages → Nat → PipePages
  | [], _ => []
  | p :: rest, n =>
    if n < p.readable then {p with readable := p.readable - n} :: rest
    else consume rest (n - p.readable)

/-- A nonempty write first tries to merge its length modulo PAGE_SIZE into
    the existing tail. Otherwise the kernel must allocate a fresh ring slot. -/
def mergeSize (ps : PipePages) (requested : Nat) : Nat :=
  let rem := requested % pageBytes
  match ps.getLast? with
  | some tail => if tail.endOffset + rem ≤ pageBytes then rem else 0
  | none => 0

def freeSlots (ps : PipePages) (cap : Nat) : Nat :=
  (cap + pageBytes - 1) / pageBytes - ps.length

def accepted (ps : PipePages) (cap requested : Nat) : Nat :=
  min requested (mergeSize ps requested + freeSlots ps cap * pageBytes)

def appendWrite (ps : PipePages) (requested transferred : Nat) : PipePages := Id.run do
  let merged := min transferred (mergeSize ps requested)
  if merged == 0 then return ps ++ packed transferred
  match ps.reverse with
  | [] => return packed transferred
  | p :: rev =>
    let p' := {readable := p.readable + merged, endOffset := p.endOffset + merged : PipePage}
    return (p' :: rev).reverse ++ packed (transferred - merged)

def write (ps : PipePages) (sl : StepSlice) (nb : Bool) (bs : Bytes) (s : StreamBuf) :
    Ret Nat × StreamBuf × PipePages := Id.run do
  let room := accepted ps s.cap bs.length
  if !(bs.isEmpty || s.readers == 0 || sl.intrBefore) && room == 0 then
    return (if nb then .err .EAGAIN else .wouldBlock .writable,s,ps)
  let (r,next) := streamWrite {sl with maxBytes := min sl.maxBytes room} nb bs s
  return (r,next,match r with | .ok n => appendWrite ps bs.length n | _ => ps)

end PipePages
end LojitaCtx.Posix
