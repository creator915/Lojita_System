import Lojita.Session.SessionEnv
namespace Gen.Probes.Gron
open Lojita.Session.SessionEnv LojitaCtx.Terminal
def probe : Probe := do
  let input := bytes "{\"a\":1}\n"
  let expected := bytes "json = {};\njson.a = 1;\n"
  let first ← batch "ref" [] input
  let again ← batch "ref" [] input
  if first.timedOut || again.timedOut || first.exitStatus != some 0 || again.exitStatus != some 0 ||
      first.stdoutOut != expected || again.stdoutOut != expected ||
      !first.stderrOut.isEmpty || !again.stderrOut.isEmpty then
    return {exitCode := 1, stderr := "unexpected gron observation: " ++ text again.stderrOut ++ text again.stdoutOut}
  return {stdout := text again.stdoutOut}
end Gen.Probes.Gron
