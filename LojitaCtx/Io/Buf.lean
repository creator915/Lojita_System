import LojitaCtx.Io.BufferState
import LojitaCtx.Posix.Program

namespace LojitaCtx.Io
open LojitaCtx.Posix

variable {Δ : List Cap}

def BufReader.receivePacked (r : BufReader) (reply : Ret ByteArray) : ReadProgress :=
  r.receive (reply.map (fun bs => bs.data.toList))

@[simp] theorem BufReader.receivePacked_list (r : BufReader) (reply : Ret Bytes) :
    r.receivePacked (reply.map List.toByteArray) = r.receive reply := by
  cases reply <;> simp only [BufReader.receivePacked, Ret.map, packed_bytes_view]

def readStep (allowed : .fdIoCap ∈ Δ) (mode : ReadMode) :
    ReadProgress → Request Δ ReadResult ReadProgress
  | .stopped a => .done a
  | .ready r =>
    match r.inspect mode with
    | some result => .done result
    | none => .ask (.read r.fd (max 1 r.chunkSize)) allowed r.receivePacked

def readLine (cap : .fdIoCap ∈ Δ) (r : BufReader) : PosixMachine Δ ReadProgress ReadResult :=
  PosixMachine.unfold (.ready r) (readStep cap .line)

abbrev BytesResult := Ret Bytes × BufReader

def readBytes (cap : .fdIoCap ∈ Δ) (mode : ReadMode) (r : BufReader) :
    PosixMachine Δ ReadProgress BytesResult :=
  (PosixMachine.unfold (.ready r) (readStep cap mode)).map fun (result, r') => (match result with
    | .ok xs => .ok (xs.getD [])
    | .err e => .err e
    | .wouldBlock w => .wouldBlock w, r')

def readExact (cap : .fdIoCap ∈ Δ) (r : BufReader) (n : Nat) : PosixMachine Δ ReadProgress BytesResult :=
  readBytes cap (.exact n) r

def readAll (cap : .fdIoCap ∈ Δ) (r : BufReader) : PosixMachine Δ ReadProgress BytesResult :=
  readBytes cap .all r

structure BufWriter where
  fd : Fd
  remaining : Bytes
  written : Nat := 0

abbrev WriteResult := Ret Unit × BufWriter

inductive WriteProgress where
  | ready (w : BufWriter)
  | stopped (result : WriteResult)

def BufWriter.advance (w : BufWriter) (n : Nat) : BufWriter :=
  {w with remaining := w.remaining.drop n, written := w.written + n}

def BufWriter.receive (w : BufWriter) : Ret Nat → WriteProgress
  | .ok n => if n = 0 || n > w.remaining.length then .stopped (.err .EIO, w)
             else .ready (w.advance n)
  | .err .EINTR => .ready w
  | .err e => .stopped (.err e, w)
  | .wouldBlock why => .stopped (.wouldBlock why, w)

def writeStep (allowed : .fdIoCap ∈ Δ) : WriteProgress → Request Δ WriteResult WriteProgress
  | .stopped result => .done result
  | .ready w =>
    if w.remaining.isEmpty then .done (.ok (), w)
    else .ask (.write w.fd w.remaining.toByteArray) allowed w.receive

def writeAll (cap : .fdIoCap ∈ Δ) (w : BufWriter) : PosixMachine Δ WriteProgress WriteResult :=
  PosixMachine.unfold (.ready w) (writeStep cap)

/-- A physical EOF or the next available line terminates the machine even at depth zero. -/
theorem readLine_observe_ready (cap : .fdIoCap ∈ Δ) (r : BufReader) (a : ReadResult)
    (h : r.inspect .line = some a) (n : Nat) :
    (readLine cap r).observe n = .done a := by
  rw [readLine, PosixMachine.observe_unfold]; cases n <;> simp [PosixMachine.unfoldPrefix, readStep, h]

/-- Drain the current batch of complete lines, then advance the same readLine
    state machine. The final unterminated line is available only after EOF. -/
def lineBatchStep {Δ : List Cap} (cap : .fdIoCap ∈ Δ) :
    ReadProgress × List Bytes → Request Δ (Ret (List Bytes)) (ReadProgress × List Bytes)
  | (.stopped (value,_), _) =>
    .done (match value with | .err e => .err e | .wouldBlock w => .wouldBlock w | .ok _ => .err .EIO)
  | (.ready r, rev) =>
    let queued := r.ready.reverse ++ rev
    let clean := {r with ready := []}
    match readStep cap .line (.ready clean) with
    | .done (.ok tail,_) => .done (.ok (queued.reverse ++ tail.toList))
    | .done (.err e,_) => .done (.err e)
    | .done (.wouldBlock why,_) => .done (.wouldBlock why)
    | .ask op h k => .ask op h (fun x => (k x,queued))

def readLines {Δ : List Cap} (cap : .fdIoCap ∈ Δ) (r : BufReader) :
    PosixMachine Δ (ReadProgress × List Bytes) (Ret (List Bytes)) :=
  PosixMachine.unfold (.ready r, []) (lineBatchStep cap)

end LojitaCtx.Io
