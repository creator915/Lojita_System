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
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-Wall", "-Wextra", "-Werror", "-fPIC", "-DCT_HAVE_OPENSSL=1"] "cc" trace

extern_lib liblean_cli_host pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "lean_cli_host") #[← lean_cli_host_o.fetch]

@[default_target] lean_lib LojitaCtx where
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticFacet]
  -- The foundation audit requires every constant in this precompiled library
  -- to be free of native overrides, including compiler-generated tag readers.
  leanOptions := #[⟨`genCtorIdx, false⟩]
@[default_target] lean_lib Lojita where
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.staticFacet]

@[default_target] lean_exe «test-s1-foundation» where
  root := `Test.S1Foundation

@[default_target] lean_exe «test-s2-kernel» where
  root := `Test.S2Kernel
  supportInterpreter := true

@[default_target] lean_exe «test-s3-harness» where
  root := `Test.S3Harness
  supportInterpreter := true

@[default_target] lean_exe «lojita» where
  root := `Lojita.Main
  supportInterpreter := true

lean_exe «test-s4-session» where
  root := `Test.S4Session
  supportInterpreter := true

lean_lib PosixFixtures where
  srcDir := "Test/Posix"
  globs := #[.submodules `Gen]

lean_exe «test-posix-channels» where
  root := `Test.PosixChannelConformance
  supportInterpreter := true

lean_exe «test-concurrent-dialectica» where
  root := `Test.ConcurrentDialecticaReplay
  supportInterpreter := true

lean_exe «io-diff-model» where
  root := `Test.Posix.Diff

target posix_host_o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "runtime/posix_host.c")
  let trace := do return mixTrace (← getLeanTrace) (← computeTrace (pkg.dir / "runtime/posix_host.h"))
  buildO (pkg.buildDir / "cbits/posix_host.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"] "cc" trace

target posix_start_o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "runtime/posix_start.c")
  buildO (pkg.buildDir / "cbits/posix_start.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"] "cc" getLeanTrace

extern_lib libposix_host pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "posix_host") #[← posix_host_o.fetch, ← posix_start_o.fetch]

lean_exe «test-io-showcase» where
  root := `Test.LiftIoShowcase
  supportInterpreter := true

lean_exe «test-posix-host» where
  root := `Test.Posix.Host

lean_exe «test-sandbox-owned» where
  root := `Test.scripts.SandboxOwned
