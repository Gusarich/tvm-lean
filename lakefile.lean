import Lake
open System Lake DSL

package "tvm-lean" where
  version := v!"0.1.0"
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-L/opt/homebrew/lib", "-L/usr/local/lib", "-lsodium"]
    else
      -- Avoid `-L/usr/lib...` because it can reorder libc/glibc resolution for Lean's sysroot toolchain on CI.
      -- Link against the system `libsodium` by full path (Ubuntu x86_64).
      #["/usr/lib/x86_64-linux-gnu/libsodium.so"]

lean_lib «TvmLean» where
  -- add library configuration options here

target tvmlean_crypto.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_crypto.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "tvmlean_crypto.c"
  let weakArgs :=
    #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "c").toString, "-I", "/opt/homebrew/include", "-I",
      "/usr/local/include"]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target tvmlean_hash.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_hash.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "tvmlean_hash.cpp"
  let weakArgs :=
    #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "c").toString, "-I", "/opt/homebrew/include", "-I",
      "/usr/local/include"]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target tvmlean_keccak.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_keccak.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "keccak.cpp"
  let weakArgs := #["-I", (pkg.dir / "c").toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib libtvmlean_crypto pkg := do
  let o ← tvmlean_crypto.o.fetch
  let oHash ← tvmlean_hash.o.fetch
  let oKeccak ← tvmlean_keccak.o.fetch
  let name := nameToStaticLib "tvmlean_crypto"
  buildStaticLib (pkg.staticLibDir / name) #[o, oHash, oKeccak]

@[default_target]
lean_exe "tvm-lean" where
  root := `Main

lean_exe "tvm-lean-tests" where
  root := `Tests

lean_exe "tvm-lean-diff-test" where
  root := `DiffTestMain

lean_exe "tvm-lean-actions-debug" where
  root := `ActionsDebugMain

lean_exe "tvm-lean-trace-inspect" where
  root := `TraceInspectMain

lean_exe "tvm-lean-precompiled-snapshot" where
  root := `PrecompiledSnapshotMain
