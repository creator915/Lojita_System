import Lake
open Lake DSL System

package lojita where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  moreLinkArgs := #["-lssl", "-lcrypto"]

target lean_cli_host_o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "runtime/cbits/lean_cli_host.c")
  let trace := do
    let h ← computeTrace (pkg.dir / "runtime/cli_host.h")
    let c ← computeTrace (pkg.dir / "runtime/cli_host.c")
    return mixTrace (← getLeanTrace) (mixTrace h c)
  buildO (pkg.buildDir / "cbits/lean_cli_host.o") src
    #["-I", (← getLeanIncludeDir).toString]
    #["-O2", "-Wall", "-Wextra", "-Werror", "-fPIC", "-DCT_HAVE_OPENSSL=1"] "cc" trace

target eval_guard_o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "runtime/cbits/eval_guard.cpp")
  buildO (pkg.buildDir / "cbits/eval_guard.o") src
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c++17", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC", "-fexceptions"]
    "c++" getLeanTrace

extern_lib liblean_cli_host pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "lean_cli_host")
    #[← lean_cli_host_o.fetch, ← eval_guard_o.fetch]

@[default_target] lean_lib LojitaCtx where
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticFacet]
  leanOptions := #[⟨`genCtorIdx, false⟩]

@[default_target] lean_lib Lojita where
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticFacet]

lean_lib TestKernelTaboos where
  globs := #[.submodules `Test.KernelTaboos]

@[default_target] lean_exe «test-kernel-taboos» where
  root := `Test.KernelTaboos
  supportInterpreter := true
