import Lojita.Store.TreeCAS
import Lojita.Ownership.IO

namespace Lojita.Sandbox.LinuxIso

open System Lojita.Ownership Lojita.Store.TreeCAS

/-- Only the embedding host supplies mounts, executable paths, and resource ceilings. -/
structure Host where
  store : FilePath
  launcher : FilePath := ".lake/build/bin/lojita-sandbox"
  executable : FilePath
  fixtures : TreeHash
  baseRootfs : Option FilePath := none
  timeoutMs : Nat := 30000
  captureBytes : Nat := 1048576

structure Request where
  args : Array String := #[]
  stdin : ByteArray := ByteArray.empty

structure Capture where
  data : ByteArray
  truncated : Bool

structure Result where
  code : UInt32
  timedOut : Bool
  stdout : Capture
  stderr : Capture

/-- Always drain the pipe, even after reaching the retained byte limit. -/
private def drain (h : IO.FS.Handle) (limit : Nat) : IO Capture := do
  let mut data := ByteArray.empty
  let mut truncated := false
  repeat
    let chunk ← h.read 65536
    if chunk.isEmpty then break
    let room := limit - data.size
    if room < chunk.size then truncated := true
    if room > 0 then data := data ++ chunk.extract 0 (min room chunk.size)
  return ⟨data,truncated⟩

private def send (h : IO.FS.Handle) (data : ByteArray) : IO Unit := do
  try h.write data; h.flush
  catch
    | .resourceVanished 32 _ => pure ()
    | e => throw e

private def invoke (host : Host) (r : Request) (stage : FilePath) : IO Result := do
  let receipt := stage / "receipt"
  let args := #[(stage / "fixtures").toString, (stage / "seed").toString,
    (stage / "export").toString, host.baseRootfs.map FilePath.toString |>.getD "-",
    host.executable.toString, toString host.timeoutMs] ++ r.args
  let (stdin, child) ← (← IO.Process.spawn {
    cmd := host.launcher.toString
    args := args
    env := #[("LOJITA_SANDBOX_RECEIPT", some receipt.toString)],
    stdin := .piped, stdout := .piped, stderr := .piped}).takeStdin
  let out ← IO.asTask (drain child.stdout host.captureBytes) .dedicated
  let err ← IO.asTask (drain child.stderr host.captureBytes) .dedicated
  let writer ← IO.asTask (send stdin r.stdin) .dedicated
  let code ← child.wait
  let stdout ← IO.ofExcept (← IO.wait out)
  let stderr ← IO.ofExcept (← IO.wait err)
  IO.ofExcept (← IO.wait writer)
  let stamp := (← IO.FS.readFile receipt).trimAscii.toString
  unless stamp == s!"exit {code}" || (code == 124 && stamp == "timeout 124") do
    throw <| IO.userError s!"sandbox setup or export failed ({code}): {String.fromUTF8Lossy stderr.data}"
  return ⟨code, stamp == "timeout 124", stdout, stderr⟩

private def stageCleanup (path : FilePath) : IO Unit := do
  -- os.fsencode preserves arbitrary Linux names. No payload is alive during this walk.
  let script := "import os,shutil,sys\np=os.fsencode(sys.argv[1]); os.chmod(p,0o700)\nfor root,dirs,files in os.walk(p,topdown=True,followlinks=False):\n for name in dirs:\n  d=os.path.join(root,name)\n  if not os.path.islink(d): os.chmod(d,0o700)\nshutil.rmtree(p)\n"
  discard <| IO.Process.run {cmd := "/usr/bin/python3",args := #["-I","-c",script,path.toString]}

/-- Both CAS inputs are hash-checked during materialization. A new work hash is
    published only after the launcher reaps its entire namespace and exports /work. -/
def run (host : Host) (seed : TreeHash) (req : Request) : IO (Result × TreeHash) := do
  let stage ← IO.FS.createTempDir
  try
    materialize host.store host.fixtures (stage / "fixtures")
    materialize host.store seed (stage / "seed")
    IO.FS.createDir (stage / "export")
    let result ← invoke host req stage
    let hash ← captureDir host.store (stage / "export")
    return (result,hash)
  finally stageCleanup stage

abbrev Work : Ctx := [("work", .file TreeHash)]
def service : Spec := mkSpec "linuxIso" Work (srv Request Result (.dir Work))

def handler (host : Host) : HandlerIO service := fun _ owned => do
  let work ← Std.Mutex.new (α := TreeHash) owned.1
  return {
    callIO := fun request => work.atomically do
      let (result,next) ← run host (← get) request
      set next
      return result
    stopIO := do
      let final ← work.atomically get
      return ⟨(),final,()⟩
  }

/-- The program can return only after closing its service channel and recovering
    the same linear slot, with its updated content-addressed work tree. -/
def once (request : Request) : Prog [service] (.dir [("sandbox", .dir Work)])
    (.dir [("sandbox", .dir Work)]) Result :=
  .exec (.here rfl) (.here rfl) () rfl <|
    .step (.call (.here rfl) rfl request) fun result =>
    .step (.stop (.here rfl) rfl) fun _ => .done result

def runOwned (host : Host) (seed : TreeHash) (request : Request) : IO (Result × TreeHash) := do
  let (resources,result) ← evalIO (EnvIO.cons (handler host) EnvIO.nil) (once request) ((seed,()),())
  return (result,resources.1.1)

end Lojita.Sandbox.LinuxIso
