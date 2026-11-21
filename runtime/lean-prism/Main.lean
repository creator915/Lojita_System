import Prism.CatStructure
import Prism.Driver
import Prism.Conservativity
import Prism.MCPServer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `agda2lean` CLI Entrypoint (v2 Unit-SCC Optic Lens + Unified Native Linker)

Subcommands:
- `agda2lean translate --main <Main.agda> [--dep <Dep.agda> ...]`
- `agda2lean inspect-slice --main <Main.agda> [--dep <Dep.agda> ...]`
- `agda2lean prism-dump --main <Main.agda> [--dep <Dep.agda> ...] [--write-bundle <bundle>]`
- `agda2lean prism-check|prism-build --sexpr-bundle <bundle> ...`
- `agda2lean prism-check --lib-dir <dir> --work-dir <dir> --main <Main.agda> [--dep <Dep.agda> ...]`
- `agda2lean prism-build --lib-dir <dir> --ir-dir <dir> --work-dir <dir> --out <bin> --main <Main.agda> [--dep <Dep.agda> ...]`

Exit codes:
- `0`  : Translated & Verified OK
- `10` : Agda frontend syntax or scope error
- `11` : Kernel Type / Termination / Productivity / Axiom Error (Lean 4 Fast OR Agda SlowSlice)
- `20` : Module-Level `⊥` (`BOT`) -> Route seamlessly to `LegacyAgda`
-/

open Prism

structure CLIOpts : Type where
  cmd            : String := ""
  libDir         : String := ""
  irDir          : String := ""
  workDir        : String := ""
  outBin         : String := ""
  dumpBin        : Option String := none
  independenceSpec : Option String := none
  trustedCodegen : Bool := false
  sexprBundle    : Bool := false
  writeBundle    : Option String := none
  mainSrc        : String := ""
  deps           : List String := []

private partial def parseCLI (args : List String) (acc : CLIOpts) : Option CLIOpts :=
  match args with
  | [] =>
      if acc.cmd.isEmpty || acc.mainSrc.isEmpty ||
        (acc.writeBundle.isSome && acc.cmd != "prism-dump") ||
        (acc.sexprBundle && (!acc.deps.isEmpty || !(["prism-check", "prism-build"].contains acc.cmd))) then none
      else some acc
  | "--lib-dir" :: v :: rest     => parseCLI rest { acc with libDir := v }
  | "--ir-dir" :: v :: rest      => parseCLI rest { acc with irDir := v }
  | "--work-dir" :: v :: rest    => parseCLI rest { acc with workDir := v }
  | "--out" :: v :: rest         => parseCLI rest { acc with outBin := v }
  | "--dump-bin" :: v :: rest    => parseCLI rest { acc with dumpBin := some v }
  | "--independence-spec" :: v :: rest => parseCLI rest { acc with independenceSpec := some v }
  | "--trusted-codegen" :: rest  => parseCLI rest { acc with trustedCodegen := true }
  | "--write-bundle" :: v :: rest => parseCLI rest { acc with writeBundle := some v }
  | "--sexpr-bundle" :: v :: rest => parseCLI rest { acc with mainSrc := v, sexprBundle := true }
  | "--main" :: v :: rest        => parseCLI rest { acc with mainSrc := v }
  | "--dep" :: v :: rest         => parseCLI rest { acc with deps := acc.deps ++ [v] }
  | c :: rest =>
      if acc.cmd.isEmpty then parseCLI rest { acc with cmd := c } else none

private def unitDisplayName (u : ModUnit) : String :=
  match u.kind with
  | .dataUnit nm _ _ _ _    => s!"data:{nm}"
  | .recUnit nm _ _ _ rd _  => if rd.coind then s!"coind:{nm}" else s!"rec:{nm}"
  | .patSynUnit nm _ _ _    => s!"pattern:{nm}"
  | .postulateUnit _ nm _   => s!"postulate:{nm}"
  | .funUnit _ nm _ _       => nm
  | .anonUnit idx _ _       => s!"_#{idx}"

private partial def parseMCPArgs (args : List String) (acc : Prism.MCP.MCPConfig) : Option Prism.MCP.MCPConfig :=
  match args with
  | [] => if acc.ctxDir.isEmpty then none else some acc
  | "--mode" :: v :: rest       => parseMCPArgs rest { acc with mode := v }
  | "--repo" :: v :: rest       => parseMCPArgs rest { acc with repoDir := v }
  | "--lib-dir" :: v :: rest    => parseMCPArgs rest { acc with libDir := v }
  | "--ir-dir" :: v :: rest     => parseMCPArgs rest { acc with irDir := v }
  | "--dump-bin" :: v :: rest   => parseMCPArgs rest { acc with dumpBin := some v }
  | "--ctx-dir" :: v :: rest    => parseMCPArgs rest { acc with ctxDir := v }
  | "--workspace" :: v :: rest  => parseMCPArgs rest { acc with workspace := v }
  | "--ref-file" :: v :: rest   => parseMCPArgs rest { acc with refFile := v }
  | "--narrow-log" :: v :: rest => parseMCPArgs rest { acc with narrowLog := v }
  | _                           => none

def main (args : List String) : IO UInt32 := withFrontendSession do
  match args with
  | ["cat-self-check"] => do
    Prism.CatStructure.runCatSelfChecks
    let lib := (← IO.appPath).parent.get!.parent.get! / "lib/lean"
    Prism.Conservativity.verify lib.toString
    return 0
  | "mcp" :: rest =>
      match parseMCPArgs rest {} with
      | none =>
          IO.eprintln "usage: agda2lean mcp --mode (node|session) --repo R --lib-dir L --ir-dir I [--dump-bin D] --ctx-dir C [--workspace W --ref-file F]"
          pure 2
      | some mcfg => Prism.MCP.runMCPServer mcfg
  | _ =>
  match parseCLI args {} with
  | none =>
      IO.eprintln "usage: agda2lean (translate|inspect-slice|prism-dump|prism-check|prism-build) [--lib-dir D] [--ir-dir D] [--work-dir D] [--out BIN] [--dump-bin DUMP] [--trusted-codegen] [--write-bundle FILE] (--main Main.agda [--dep F.agda ...] | --sexpr-bundle FILE)"
      pure 2
  | some opts =>
      match opts.cmd with
      | "translate" => do
          let res ← parseAndSliceBundle opts.deps opts.mainSrc opts.libDir
            (if opts.workDir.isEmpty then "" else opts.workDir) opts.dumpBin true
          match res with
          | .syntaxErr e =>
              IO.eprintln s!"SYNTAX_ERROR: {e}"
              pure exitSyntaxErr
          | .bot r =>
              IO.eprintln s!"BOT: {r}"
              pure exitBot
          | .translated (deps, sm) =>
              let fields := ExecFields.layout ((sm :: deps).map (fun m => (m.codeMod, m.plan)))
              match transcodeExec sm.depMods sm.codeMod sm.expMod sm.plan fields with
              | .error e =>
                  IO.eprintln s!"BOT: {e}"
                  pure exitBot
              | .ok cmds => do
                  let lib ← if opts.libDir.isEmpty then do
                    let bin := (← IO.appPath).parent.getD "."
                    pure (bin / "../lib/lean").toString
                  else pure opts.libDir
                  IO.println (← KernelDriver.renderCommands lib cmds)
                  pure exitOK
      | "inspect-slice" => do
          let res ← parseAndSliceBundle opts.deps opts.mainSrc opts.libDir
            (if opts.workDir.isEmpty then "" else opts.workDir) opts.dumpBin
          match res with
          | .syntaxErr e =>
              IO.eprintln s!"SYNTAX_ERROR: {e}"
              pure exitSyntaxErr
          | .bot r =>
              IO.eprintln s!"BOT: {r}"
              pure exitBot
          | .translated (_, mainSm) =>
              let fastNames := mainSm.plan.units.filter (fun u => mainSm.plan.fastUnitIds.contains u.uid) |>.map unitDisplayName
              let slowNames := mainSm.plan.units.filter (fun u => mainSm.plan.slowUnitIds.contains u.uid) |>.map unitDisplayName
              IO.println s!"FAST_UNITS ({fastNames.length}): {String.intercalate ", " fastNames}"
              IO.println s!"SLOW_UNITS ({slowNames.length}): {String.intercalate ", " slowNames}"
              if mainSm.plan.hasSlowUnits then
                IO.println "--- SLOW_SLICE_AGDA ---"
                if let some residual := residualFor mainSm then
                  IO.print (← renderCode opts.libDir opts.workDir residual.residualCode)
              pure exitOK
      | "prism-dump" => do
          match ← dumpSurfaceBundle opts.deps opts.mainSrc opts.libDir opts.workDir opts.dumpBin with
          | .error e => IO.eprintln s!"SYNTAX_ERROR: {e}"; return exitSyntaxErr
          | .ok (deps, unit, cm) =>
            let mainWire := renderTopSExpr (encodeCodeMod cm)
            if let some output := opts.writeBundle then
              if !unit.checkErrors.isEmpty then
                IO.eprintln (String.intercalate "\n" unit.checkErrors)
                return exitSyntaxErr
              let wires := deps.map fun (_, dep) => renderTopSExpr (encodeCodeMod dep)
              let tmp := s!"{output}.{← IO.monoNanosNow}.tmp"
              try
                IO.FS.writeFile tmp ("(bundle\n" ++ String.intercalate "\n" (wires ++ [mainWire]) ++ "\n)\n")
                IO.FS.rename tmp output
              finally
                if ← System.FilePath.pathExists tmp then IO.FS.removeFile tmp
            IO.println mainWire
            return exitOK
      | "prism-check" => do
          let (code, msg) ← runPrismCheck opts.libDir opts.workDir opts.deps opts.mainSrc opts.dumpBin opts.independenceSpec opts.sexprBundle
          if code == exitOK then
            pure exitOK
          else do
            IO.eprintln msg
            pure code
      | "prism-build" => do
          let (code, msg) ← runPrismBuildExe opts.libDir opts.irDir opts.workDir opts.outBin opts.deps opts.mainSrc opts.dumpBin opts.trustedCodegen opts.sexprBundle
          if code == exitOK then
            pure exitOK
          else do
            IO.eprintln msg
            pure code
      | _ =>
          IO.eprintln s!"unknown command '{opts.cmd}'"
          pure 2
