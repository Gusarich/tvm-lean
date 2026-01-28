import Lake
open System Lake DSL

package "tvm-lean" where
  version := v!"0.1.0"
  moreLinkArgs := #["-L/opt/homebrew/lib", "-L/usr/local/lib", "-lsodium"]

lean_lib «TvmLean» where
  -- add library configuration options here

target tvmlean_crypto.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_crypto.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "tvmlean_crypto.c"
  let weakArgs :=
    #["-I", (← getLeanIncludeDir).toString, "-I", "/opt/homebrew/include", "-I", "/usr/local/include"]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib libtvmlean_crypto pkg := do
  let o ← tvmlean_crypto.o.fetch
  let name := nameToStaticLib "tvmlean_crypto"
  buildStaticLib (pkg.staticLibDir / name) #[o]

@[default_target]
lean_exe "tvm-lean" where
  root := `Main

lean_exe "tvm-lean-tests" where
  root := `Tests

lean_exe "tvm-lean-diff-test" where
  root := `DiffTestMain
