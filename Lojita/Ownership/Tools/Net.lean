import Lojita.Ownership.Tools.Relay
import LojitaCtx.NetSandbox

namespace Lojita.Ownership.Tools.Net
open LojitaCtx.Terminal LojitaCtx.NetSandbox

def netSpec := OwnedSpec "netbox" NetConfig Bytes NetStep RawNetObs NetConfig.ownedFiles

def command : NetStep → String
  | .runClient exe args input ms => runRequest exe args input ms
  | .waitPortReady ms => s!"P {ms}"
  | .tcpProbe bs ms => s!"C {ms} {hex bs}"
  | .httpProbe method path headers body ms => s!"J {ms} {hex (encodeHttpReq method path headers body)}"
  | .udpProbe bs ms => s!"G {ms} {hex bs}"
  | .sleepNetMs ms => s!"S {ms}"
  | .drainNet => "N"

def request (p : Pipe) (line : String) : IO RawNetObs := do
  let ["O", out, err, wire, code, timed, count] ← exchange p line | throw (IO.userError "invalid network reply")
  let mut captures := #[]
  for _ in [:← natural count] do
    let ["C", data] := (← readLine p).splitOn " " | throw (IO.userError "invalid network capture")
    captures := captures.push (← unhex data)
  return ⟨← unhex out, ← unhex err, ← unhex wire, captures.toList, ← status code, ← flag timed⟩

private def setup (cfg : NetConfig) (owned : ModelsIO (filesCtx Bytes cfg.ownedFiles)) (p : Pipe) : IO Unit := do
  let send := fun line => do
    let obs ← request p line
    requireWire (obs.exitStatus.getD 0 == 0 && !obs.timedOut) "network setup rejected"
  let http := fun (routes : List HttpRoute) => do
    send ("H " ++ hex (encodeHttpResp 404 "Not Found" [] []))
    for r in routes do
      let resp := encodeHttpResp r.routeStatus r.routeReason r.routeHeaders r.routeBody
      send s!"A {hexText r.routeMethod} {hexText r.routePath} {hex resp}"
  let raw := fun mode (rules : List RawStubRule) => do
    send mode
    for r in rules do send s!"B {hex r.matchPrefix} {hex r.replyPayload}"
  for (k, v) in cfg.envVars do send ("E " ++ hexText (k ++ "=" ++ v))
  visitFiles (fun path bs => send s!"W {hexText path} {hex bs}") cfg.ownedFiles owned
  match cfg.topology with
  | .httpStubMode rs => http rs
  | .httpDelayedStubMode ms rs => send s!"Z {ms}" *> http rs
  | .tcpStubMode rs => raw "T" rs
  | .tcpDelayedStubMode ms rs => send s!"Z {ms}" *> raw "T" rs
  | .udpStubMode rs => raw "U" rs
  | .daemonProbeMode exe args => send (String.intercalate " " (["D", hexText exe, toString args.length] ++ args.map hexText))

def netToolWithMount (bin scratch : System.FilePath) (candidate : Option System.FilePath) : HandlerIO netSpec := fun cfg owned => do
  checkEnv cfg.envVars
  openBytes bin scratch cfg.target cfg.ownedFiles owned #[] (setup cfg owned)
    (fun p q => request p (command q)) (fun p => discard (request p "Q")) false candidate

def netTool (bin scratch : System.FilePath) : HandlerIO netSpec :=
  netToolWithMount bin scratch none

end Lojita.Ownership.Tools.Net
