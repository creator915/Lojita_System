import Lojita.Ownership.Tools.Relay

namespace Lojita.Ownership.Tools.Term
open LojitaCtx.Terminal

def ptySpec := OwnedSpec "pty" TermConfig String TermStep RawTermObs TermConfig.files

def command : TermStep → String
  | .writeStdin bs => "W " ++ hex bs
  | .writeTTY bs => "T " ++ hex bs
  | .closeStdin => "C"
  | .sleepMs ms => s!"S {ms}"
  | .resizeTTY r c => s!"R {r} {c}"
  | .sendSignal sig => "K " ++ match sig with
    | .sigINT => "2" | .sigTERM => "15" | .sigHUP => "1" | .sigQUIT => "3" | .sigKILL => "9"
  | .drainRaw => "D"

def request (p : Pipe) (line : String) : IO RawTermObs := do
  let ["O", tty, out, err, code] ← exchange p line | throw (IO.userError "invalid terminal reply")
  return ⟨← unhex tty, ← unhex out, ← unhex err, ← status code⟩

def ptyToolWithMount (bin scratch : System.FilePath) (candidate : Option System.FilePath) : HandlerIO ptySpec := fun cfg owned => do
  checkEnv cfg.envVars
  requireWire (!cfg.executable.isEmpty && !(cfg.executable :: cfg.arguments).any (fun s : String => s.toList.any (fun c => c.toNat == 0)))
    "invalid terminal process arguments"
  let mode := match cfg.topology with | .allTTY => "tty" | .pipeStdioWithTTY => "pipe"
  let env := cfg.envVars.map fun (k,v) => k ++ "=" ++ v
  let args := [mode, toString cfg.rows, toString cfg.cols, toString env.length] ++ env ++ cfg.executable :: cfg.arguments
  openRelay bin scratch cfg.target cfg.files owned String.toUTF8
    (fun b => match String.fromUTF8? b with | some v => pure v | none => throw (IO.userError "invalid owned text"))
    args.toArray (fun _ => pure ()) (fun p q => request p (command q)) (fun p => discard (request p "Q")) true candidate

def ptyTool (bin scratch : System.FilePath) : HandlerIO ptySpec :=
  ptyToolWithMount bin scratch none

end Lojita.Ownership.Tools.Term
