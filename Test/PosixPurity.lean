import Lean
import LojitaCtx

open Lean Elab Command

/- Audit the compiled environment, including dependencies defined in Init and Std. -/
run_cmd do
  let env ← getEnv
  for dir in ["LojitaCtx/Posix","LojitaCtx/Io"] do
    for file in ← (System.FilePath.mk dir).walkDir do
      if file.extension == some "lean" then
        let mod := ((file.withExtension "").components).foldl Name.str Name.anonymous
        unless env.header.moduleNames.contains mod do throwError "G1 module missing from environment: {mod}"
  let mut todo : Array (Name × List Name) := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if [`LojitaCtx.Io, `LojitaCtx.Posix].any (·.isPrefixOf mod) then
      todo := todo.push (n, [])
  if todo.isEmpty then throwError "no audited constants"
  let roots := todo.size
  let mut seen : NameSet := {}
  let mut violations := 0
  let mut counters : Std.TreeMap String Nat := {}
  let mut examples : Array String := #[]
  let mut queueIndex := 0
  let mut names : Std.TreeMap String (List Name) := {}
  while let some (n, parents) := todo[queueIndex]? do
    queueIndex := queueIndex + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | throwError "missing declaration {n}"
    let badAx := (info matches .axiomInfo _) && ![``propext, ``Quot.sound, ``Classical.choice].contains n
    let reason := if n == ``sorryAx then "sorry" else if badAx then "axiom"
      else if isExtern env n then "extern" else if info.isUnsafe then "unsafe" else ""
    if !reason.isEmpty then
      violations := violations + 1
      counters := counters.insert reason (counters[reason]?.getD 0 + 1)
      names := names.insert reason (n :: names[reason]?.getD [])
      if reason != "extern" || counters[reason]?.getD 0 ≤ 8 then
        examples := examples.push (reason ++ "  " ++ String.intercalate " -> " ((n :: parents).reverse.map toString))
    let mut deps := info.getUsedConstantsAsSet
    if let some impl := Compiler.getImplementedBy? env n then deps := deps.insert impl
    for dep in deps do
      unless seen.contains dep do todo := todo.push (dep, n :: parents)
  logInfo m!"G1 audited {roots} project declarations, {seen.size} reachable constants"
  for (kind, ns) in names.toList do logInfo m!"{kind}: {ns}"
  unless violations == 0 do
    throwError "G1 strict purity failed at {violations} constants {counters.toList}\n{String.intercalate "\n" examples.toList}"
