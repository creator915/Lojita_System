import LojitaCtx.Posix.Stream

namespace LojitaCtx.Posix

structure Termios where
  icanon : Bool
  echo : Bool
  isig : Bool
  icrnl : Bool
  opost : Bool
  deriving DecidableEq, Repr, Inhabited

def rawTermios : Termios := ⟨false, false, false, false, false⟩
def canonTermios : Termios := ⟨true, true, true, true, true⟩
def cfmakeraw (_ : Termios) := rawTermios

structure Winsize where
  rows : Nat := 24
  cols : Nat := 80
  deriving DecidableEq, Repr, Inhabited

structure PtyState where
  toSlave : StreamBuf := {}
  toMaster : StreamBuf := {}
  attrs : Termios := canonTermios
  size : Winsize := {}
  editing : Bytes := []
  /-- Remaining bytes in each readable canonical record. Zero is a VEOF record. -/
  records : List Nat := []
  interruptPending : Bool := false
  deriving Repr, DecidableEq, Inhabited

def tcsetattr (p : PtyState) (t : Termios) : PtyState :=
  let pending := p.toSlave.pendingBytes ++ p.editing
  if p.attrs.icanon = t.icanon then {p with attrs := t}
  else {p with attrs := t, editing := [], toSlave := {p.toSlave with pendingBytes := pending},
               records := if t.icanon && !pending.isEmpty then [pending.length] else []}
def tcgetattr (p : PtyState) := p.attrs

theorem tcsetattr_tcgetattr_roundtrip (p : PtyState) (t : Termios) :
    tcgetattr (tcsetattr p t) = t := by unfold tcsetattr; split <;> rfl

private def appendBytes (s : StreamBuf) (bs : Bytes) : StreamBuf :=
  { s with pendingBytes := s.pendingBytes ++ bs }

/-- Input that has reached the line discipline; caller applies the transfer budget. -/
private def receive (p : PtyState) (raw : UInt8) : PtyState := Id.run do
  let t := p.attrs
  let ch := if t.icrnl && raw == 13 then 10 else raw
  if t.isig && ch == 3 then
    return { p with interruptPending := true, records := [], editing := [], toSlave := {p.toSlave with pendingBytes := []} }
  if t.icanon && ch == 4 then
    return { p with toSlave := appendBytes p.toSlave p.editing, records := p.records ++ [p.editing.length], editing := [] }
  let echo := if !t.echo then [] else if t.opost && ch == 10 then [13, 10] else [ch]
  let p := { p with toMaster := appendBytes p.toMaster echo }
  if !t.icanon then return { p with toSlave := appendBytes p.toSlave [ch] }
  if ch == 127 then return {p with editing := p.editing.dropLast}
  let line := p.editing ++ [ch]
  if ch == 10 then return {p with editing := [], records := p.records ++ [line.length], toSlave := appendBytes p.toSlave line}
  return {p with editing := line}

def ptyMasterWrite (p : PtyState) (bs : Bytes) : PtyState :=
  let accepted := bs.take (p.toSlave.freeSpace - p.editing.length)
  if p.attrs = rawTermios then {p with toSlave := appendBytes p.toSlave accepted}
  else accepted.foldl receive p

theorem pty_raw_passthrough (p : PtyState) (bs : Bytes) (raw : p.attrs = rawTermios)
    (fits : bs.length ≤ p.toSlave.freeSpace - p.editing.length) :
    (ptyMasterWrite p bs).toSlave.pendingBytes = p.toSlave.pendingBytes ++ bs ∧
    (ptyMasterWrite p bs).toMaster.pendingBytes = p.toMaster.pendingBytes := by
  simp [ptyMasterWrite, raw, List.take_of_length_le fits, appendBytes]

/-- Canonical records are consumed in order, including an empty VEOF
    between two nonempty records. The caller handles a zero-sized read. -/
def ptyRead (sl : StepSlice) (nb master : Bool) (p : PtyState) : Ret Bytes × PtyState := Id.run do
  if master then
    if !sl.intrBefore && p.toMaster.writers == 0 && p.toMaster.pendingBytes.isEmpty then
      return (.err .EIO,p)
    let (r,s) := streamRead sl nb p.toMaster
    return (r,{p with toMaster := s})
  if p.attrs.icanon then
    if sl.intrBefore then return (.err .EINTR,p)
    match p.records with
    | 0 :: rest => return (.ok [],{p with records := rest})
    | (n+1) :: rest =>
      let (r,s) := streamRead {sl with maxBytes := min (max 1 sl.maxBytes) (n+1)} nb p.toSlave
      let remaining : Nat := match r with | .ok bs => n + 1 - bs.length | _ => n + 1
      return (r,{p with toSlave := s, records := if remaining = 0 then rest else (remaining :: rest)})
    | [] => pure ()
  let (r,s) := streamRead sl nb p.toSlave
  return (r,{p with toSlave := s})

/-- Linux flushes the slave input/line discipline when the last master closes.
    Closing the last slave retains unread output on the master until drained. -/
def ptyHangup (p : PtyState) (lostMaster : Bool) : PtyState :=
  if lostMaster then
    {p with
      editing := []
      records := []
      toSlave := {p.toSlave with writers := 0, pendingBytes := []}
      toMaster := {p.toMaster with readers := 0}}
  else
    {p with toMaster := {p.toMaster with writers := 0}, toSlave := {p.toSlave with readers := 0}}

def ptySlaveWrite (p : PtyState) (bs : Bytes) : PtyState :=
  let cooked := if p.attrs.opost then bs.flatMap fun b => if b == 10 then [13,b] else [b] else bs
  {p with toMaster := appendBytes p.toMaster cooked}

end LojitaCtx.Posix
