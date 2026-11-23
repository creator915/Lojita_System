import Lojita.Ownership.IO
import LojitaCtx.FsSandbox

namespace Lojita.Ownership.Tools
open LojitaCtx.Terminal
open System (FilePath)

abbrev Pipe := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

def requireWire (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def readLine (p : Pipe) : IO String := do
  let line ← p.stdout.getLine
  unless line.endsWith "\n" do throw (IO.userError "relay closed in the middle of a reply")
  return (line.dropEnd 1).toString

def exchange (p : Pipe) (request : String) : IO (List String) := do
  requireWire (!request.any (fun c => c == '\n' || c == '\r' || c.toNat == 0)) "invalid control frame"
  p.stdin.putStrLn request
  p.stdin.flush
  return (← readLine p).splitOn " "

private def digit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

def hex (bs : Bytes) : String :=
  if bs.isEmpty then "-" else String.ofList (bs.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

def hexText (s : String) := hex (bytes s)

private def nibble (c : Char) : IO Nat :=
  if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
  else throw (IO.userError "invalid hexadecimal relay digit")

def unhex (s : String) : IO Bytes := do
  if s == "-" then return []
  requireWire (!s.isEmpty) "empty hexadecimal token"
  go s.toList []
where
  go : List Char → Bytes → IO Bytes
    | [], acc => pure acc.reverse
    | [_], _ => throw (IO.userError "odd hexadecimal byte count")
    | h :: l :: cs, acc => do go cs (byte (16 * (← nibble h) + (← nibble l)) :: acc)
  termination_by structural cs _ => cs

def wireText (s : String) : IO String := do
  let some text := String.fromUTF8? (← unhex s).toByteArray | throw (IO.userError "invalid UTF-8 relay field")
  return text

def natural (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"invalid natural number {s}")

def status (s : String) : IO (Option Nat) := if s == "-1" then pure none else some <$> natural s
def flag : String → IO Bool
  | "1" => pure true
  | "0" => pure false
  | _ => throw (IO.userError "invalid relay flag")

def runRequest (exe : String) (args : List String) (input : Bytes) (timeout : Nat) :=
  String.intercalate " " (["R", toString timeout, hexText exe, toString args.length] ++ args.map hexText ++ [hex input])

def filesCtx (A : Type) (names : List String) : Ctx := names.map fun n => (n, .file A)

def OwnedSpec (name : String) (Cfg A Q R : Type) (files : Cfg → List String) : Spec :=
  specI name Cfg (fun cfg => filesCtx A (files cfg)) (fun cfg => srv Q R (.dir (filesCtx A (files cfg))))

def visitFiles {A : Type} (visit : String → A → IO Unit) :
    (ns : List String) → ModelsIO (filesCtx A ns) → IO Unit
  | [], _ => pure ()
  | n :: ns, m => do
    visit n m.1
    visitFiles visit ns m.2
termination_by structural ns _ => ns

def checkEnv (vars : List (String × String)) : IO Unit := do
  let names := vars.map Prod.fst
  requireWire (names.eraseDups.length == names.length && vars.all (fun (k, v) =>
    match k.toList with
    | [] => false
    | c :: cs => (c.isAlpha || c == '_') && cs.all (fun x => x.isAlphanum || x == '_') &&
        !v.any (·.toNat == 0))) "invalid or duplicate environment variables"

private def loadFiles {A : Type} (decode : ByteArray → IO A) (root : FilePath) :
    (ns : List String) → IO (ModelsIO (filesCtx A ns))
  | [] => pure ()
  | n :: ns => do
    let mut p := root
    for part in n.splitOn "/" do
      requireWire ((← p.symlinkMetadata).type == .dir) s!"expected owned directory {p}"
      -- The relay has exited. A fixture may have removed directory search permission.
      IO.setAccessRights p {user := {read := true, write := true, execution := true}}
      p := p / part
    let metadata ← p.symlinkMetadata
    requireWire (metadata.type == .file && metadata.numLinks == 1) s!"expected unaliased owned regular file {n}"
    let data ← try IO.FS.readBinFile p catch
      | .permissionDenied .. =>
        IO.setAccessRights p {user := {read := true}}
        IO.FS.readBinFile p
      | e => throw e
    let a ← decode data
    return (a, ← loadFiles decode root ns)
termination_by structural ns => ns

private def checked (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output {cmd, args}
  unless out.exitCode == 0 do throw (IO.userError s!"{cmd}: {out.stderr}")
  return out.stdout.trimAsciiEnd.toString

private def removeScratch (root : FilePath) : IO Unit := do
  unless ← root.pathExists do return
  try IO.FS.removeDirAll root catch
    | .permissionDenied .. =>
      -- Walk directories before their children, granting access to private
      -- fixtures. Leaves and symbolic links keep their modes.
      discard <| checked "find" #["-P", root.toString, "-type", "d", "-exec", "chmod", "u+rwx", "--", "{}", ";"]
      IO.FS.removeDirAll root
    | e => throw e

/-- Each open owns a new scratch directory. The child terminates before the
    declared leaves are recovered. All control traffic uses a single mutex. -/
def openRelay {A Q R : Type} (bin scratch : FilePath) (target : SandboxTarget)
    (names : List String) (owned : ModelsIO (filesCtx A names))
    (encode : A → ByteArray) (decode : ByteArray → IO A) (args : Array String)
    (setup : Pipe → IO Unit) (turn : Pipe → Q → IO R) (finish : Pipe → IO Unit)
    (seedOnDisk := true) (candidate : Option FilePath := none) :
    IO (RunningIO Q R ((_: Unit) × ModelsIO (filesCtx A names))) := do
  requireWire (names.all LojitaCtx.FsSandbox.validRelPath && LojitaCtx.FsSandbox.noPathCollisions names)
    "invalid or overlapping owned file paths"
  let bin ← IO.FS.realPath bin
  IO.FS.createDirAll scratch
  let parent ← IO.FS.realPath scratch
  let root : FilePath := ← checked "mktemp" #["-d", "--", (parent / "lojita.XXXXXXXXXX").toString]
  let work := root / "work"
  let container := root.fileName.getD "lojita"
  let docker := match target with | .localSandbox => false | .dockerSandbox _ => true
  let launch : IO (RunningIO Q R ((_: Unit) × ModelsIO (filesCtx A names))) := do
    IO.FS.createDir work
    if seedOnDisk then
      visitFiles (fun name a => do
        let path := work / name
        IO.FS.createDirAll (path.parent.getD work)
        IO.FS.writeBinFile path (encode a)) names owned
    let (cmd, argv) : String × Array String ← match target with
      | .localSandbox => pure (bin.toString, args)
      | .dockerSandbox img => do
        requireWire (!img.isEmpty && !img.startsWith "-" && !img.any (fun c : Char => c.toNat == 0) &&
          !bin.toString.contains ',' && !work.toString.contains ',') "invalid container parameters"
        let uid ← checked "id" #["-u"]
        let gid ← checked "id" #["-g"]
        let user ← if uid == "0" then do
          discard <| checked "chown" #["-R", "65534:65534", "--", work.toString]
          pure "65534:65534"
        else pure (uid ++ ":" ++ gid)
        let mut mounts := #[]
        if let some path := candidate then
          requireWire (!path.toString.contains ',') "invalid candidate mount"
          mounts := #["--mount", s!"type=bind,src={path},dst=/lojita-candidate,readonly"]
        pure ("docker", #["run"] ++ mounts ++ #["--rm", "-i", "--pull=never", "--network=none", "--cap-drop=ALL",
          "--security-opt=no-new-privileges", "--user", user, "--tmpfs", "/tmp:rw,nosuid,noexec,size=64m", "--read-only", "--pids-limit=64",
          "--name", container, "--mount", s!"type=bind,src={bin},dst=/relay,readonly", "--mount",
          s!"type=bind,src={work},dst=/work", "--workdir", "/work", "--entrypoint", "/relay", img] ++ args)
    let p : Pipe ← IO.Process.spawn {
      cmd := cmd
      args := argv
      cwd := some work
      inheritEnv := docker
      stdin := .piped
      stdout := .piped
      stderr := .inherit }
    let reaped ← IO.mkRef false
    let cleanup := do
      if docker then discard <| IO.Process.output {cmd := "docker", args := #["rm", "-f", container]}
      unless ← reaped.get do
        if (← p.tryWait).isNone then
          try p.kill catch _ => pure ()
          discard p.wait
        reaped.set true
      removeScratch root
    try
      requireWire ((← readLine p) == "READY") "relay handshake failed"
      setup p
      RunningIO.machine () (fun _ q => do
        try
          return (← turn p q, ())
        catch e =>
          cleanup
          throw e)
        (fun _ => do
          try
            finish p
            let code ← p.wait
            reaped.set true
            requireWire (code == 0) "relay exited unsuccessfully"
            return ⟨(), ← loadFiles decode work names⟩
          finally cleanup)
    catch e =>
      cleanup
      throw e
  try launch catch e =>
    removeScratch root
    throw e

def openBytes {Q R : Type} (bin scratch : FilePath) (target : SandboxTarget) (ns : List String)
    (owned : ModelsIO (filesCtx Bytes ns)) (args : Array String) (setup : Pipe → IO Unit)
    (turn : Pipe → Q → IO R) (finish : Pipe → IO Unit) (seedOnDisk := true) (candidate : Option FilePath := none) :=
  openRelay bin scratch target ns owned List.toByteArray (fun b => pure b.data.toList) args setup turn finish seedOnDisk candidate

end Lojita.Ownership.Tools
