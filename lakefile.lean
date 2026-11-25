import Lake
open Lake DSL System

package lojita where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  moreLinkArgs := #["-lcrypto"]

target eval_guard_o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "runtime/cbits/eval_guard.cpp")
  buildO (pkg.buildDir / "cbits/eval_guard.o") src
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c++17", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC", "-fexceptions"]
    "c++" getLeanTrace

extern_lib libeval_guard pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "eval_guard") #[← eval_guard_o.fetch]

target tree_cas_o pkg : FilePath := do
  let src ← inputTextFile (pkg.dir / "runtime/tree_cas.c")
  buildO (pkg.buildDir / "cbits/tree_cas.o") src
    #["-I", (← getLeanIncludeDir).toString] #["-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"] "cc" getLeanTrace

extern_lib libtree_cas pkg := do
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "tree_cas") #[← tree_cas_o.fetch]

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

lean_lib PosixFixtures where
  srcDir := "Test/Posix"
  globs := #[.submodules `Gen]

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

lean_exe treeCasNativeTest where
  root := `Test.TreeCasNative

lean_exe «test-vfs-twin» where
  root := `Test.VfsTwin
