import Lojita.Session.SessionEnv
namespace Gen.Probes.Relays
open Lojita.Ownership Lojita.Session.SessionEnv LojitaCtx.Terminal

def network : Script Bool :=
  .step (.mkdir "net" rfl) fun _ =>
  .exec (.here rfl) netSlot ⟨.localSandbox,.tcpStubMode [],[],[]⟩ rfl <|
  .step (.call (.here rfl) rfl (.runClient "ref" [] (bytes "net") 3000)) fun obs =>
  .step (.stop (.here rfl) rfl) fun _ => .step (.rmdir (.here rfl) rfl) fun _ =>
  .done (obs.stdoutOut == bytes "<p>net</p>\n" && obs.exitStatus == some 0)

def git : Script Bool :=
  .step (.mkdir "git" rfl) fun _ =>
  .exec (.here rfl) gitSlot ⟨.localSandbox,"main","Fixture","fixture@example.test",1,[],[]⟩ rfl <|
  .step (.call (.here rfl) rfl (.gitRunTarget "ref" [] (bytes "git") 3000)) fun obs =>
  .step (.stop (.here rfl) rfl) fun _ => .step (.rmdir (.here rfl) rfl) fun _ =>
  .done (obs.stdoutOut == bytes "<p>git</p>\n" && obs.exitStatus == some 0)

def web : Script Bool :=
  .step (.mkdir "web" rfl) fun _ =>
  .exec (.here rfl) webSlot ⟨.localSandbox,2,2,[]⟩ rfl <|
  .step (.call (.here rfl) rfl (.pixel 0 0)) fun obs =>
  .step (.stop (.here rfl) rfl) fun _ => .step (.rmdir (.here rfl) rfl) fun _ =>
  .done (obs matches .pixelObs ..)

def probe : Probe := do
  let n ← network
  let g ← git
  let w ← web
  return {exitCode := if n && g && w then 0 else 1}

end Gen.Probes.Relays
