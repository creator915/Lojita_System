import Lake
open Lake DSL
open System (FilePath)

package «lean-prism» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

target lean_cli_host_o pkg : FilePath := do
  let oFile := pkg.buildDir / "cbits" / "lean_cli_host.o"
  let srcJob ← inputTextFile <| pkg.dir / "cbits" / "lean_cli_host.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"]
  let depTrace := do
    let tLean ← getLeanTrace
    let tHdr  ← computeTrace (pkg.dir / ".." / "cli_host.h")
    let tSrc  ← computeTrace (pkg.dir / ".." / "cli_host.c")
    pure (mixTrace tLean (mixTrace tHdr tSrc))
  buildO oFile srcJob weakArgs #[] "cc" depTrace

extern_lib «liblean_cli_host» pkg := do
  let name := nameToStaticLib "lean_cli_host"
  let oJob ← lean_cli_host_o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

@[default_target]
lean_lib «AgdaMirror» where
  roots := #[`AgdaMirror.CharClass, `AgdaMirror.Utf8, `AgdaMirror.Core, `AgdaMirror.Context, `AgdaMirror.World, `AgdaMirror.Protocol, `AgdaMirror.AxiomGuard, `AgdaMirror.VerifySelf]

lean_lib «Prism» where
  roots := #[
    `Prism.Outcome,
    `Prism.StdScope,
    `Prism.DecodeSExpr,
    `Prism.TermMatrix,
    `Prism.LensSlice,
    `Prism.AxiomFootprint,
    `Prism.CatStructure,
    `Prism.LoweringContext,
    `Prism.ExecFields,
    `Prism.ExecRecords,
    `Prism.ExecPorts,
    `Prism.ExecGhost,
    `Prism.TranscodeExec,
    `Prism.KernelDriver,
    `Prism.FactorMutual,
    `Prism.TranscodeChk,
    `Prism.Conservativity,
    `Prism.Driver,
    `Prism.MCPServer
  ]

@[default_target]
lean_exe «agda2lean» where
  root := `Main
  supportInterpreter := true
