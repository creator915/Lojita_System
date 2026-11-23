import LojitaCtx.World

namespace Gen.FzfTTY
open LojitaCtx.World

def app : CliApp CliCaps := do
  writeStdoutStrW stdioInCli "OUT"
  writeStderrStrW stdioInCli "ERR"
  match ← writeTTYStrW ttyInCli "UI" with
  | true => pure 0
  | false => pure 25

end Gen.FzfTTY
