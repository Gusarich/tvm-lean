import Lake
open System Lake DSL

package "tvm-lean" where
  version := v!"0.1.0"
  moreLinkArgs :=
    if System.Platform.isOSX then
      #[
        "-L/opt/homebrew/lib",
        "-L/usr/local/lib",
        "-lsodium",
        "/Users/daniil/Coding/ton/build/third-party/secp256k1/lib/libsecp256k1.a",
        "/Users/daniil/Coding/ton/build/third-party/openssl/lib/libssl.a",
        "/Users/daniil/Coding/ton/build/third-party/openssl/lib/libcrypto.a",
        "/Users/daniil/Coding/ton/build/third-party/blst/libblst.a"
      ]
    else
      -- Link libsodium statically to avoid glibc version mismatches between the system `libsodium.so`
      -- and Lean's sysroot toolchain on CI (Ubuntu x86_64).
      #["/usr/lib/x86_64-linux-gnu/libsodium.a"]

@[default_target]
lean_lib TvmLeanModel where
  roots := #[`TvmLean.Model, `TvmLean.Boc, `TvmLean.Spec]

@[default_target]
lean_lib TvmLeanSemantics where
  roots := #[`TvmLean.Semantics]

lean_lib TvmLean where
  roots := #[`TvmLean]

lean_lib TvmLeanNative where
  roots := #[`TvmLean.Native]
  needs := #[`@/libtvmlean_crypto]
  extraDepTargets := #[`libtvmlean_crypto]
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.extraDepFacet]

lean_lib TvmLeanValidation where
  roots := #[`TvmLean.Validation]

lean_lib TvmLeanTests where
  srcDir := "."
  roots := #[
    `Tests.Tests,
    `Tests.All,
    `Tests.Instr,
    `Tests.Harness.Registry,
    `Tests.Harness.OracleHarness,
    `Tests.Harness.FuzzHarness,
    `Tests.Harness.Runner,
    `Tests.Harness.Cli,
    `Tests.Harness.Coverage,
    `Tests.Harness.Gen.Arith
  ]

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
  buildO oFile srcJob weakArgs #["-fPIC", "-std=c++11"] "cc" getLeanTrace

target tvmlean_crypto_ext.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_crypto_ext.o"
  let leanIncludeDir := (← getLeanIncludeDir).toString
  let srcPath :=
    if System.Platform.isOSX then
      pkg.dir / "c" / "tvmlean_crypto_ext.c"
    else
      pkg.dir / "c" / "tvmlean_crypto_ext_stub.c"
  let srcJob ← inputTextFile srcPath
  let weakArgs :=
    if System.Platform.isOSX then
      #[
        "-I", leanIncludeDir,
        "-I", (pkg.dir / "c").toString,
        "-I", "/opt/homebrew/include",
        "-I", "/usr/local/include",
        "-I", "/Users/daniil/Coding/ton/build/third-party/secp256k1/include",
        "-I", "/Users/daniil/Coding/ton/build/third-party/openssl/include",
        "-I", "/Users/daniil/Coding/ton/third-party/blst/bindings"
      ]
    else
      #[
        "-I", leanIncludeDir,
        "-I", (pkg.dir / "c").toString
      ]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target tvmlean_keccak.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_keccak.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "keccak.cpp"
  let weakArgs := #["-I", (pkg.dir / "c").toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-std=c++11"] "cc" getLeanTrace

extern_lib libtvmlean_crypto pkg := do
  let o ← tvmlean_crypto.o.fetch
  let oHash ← tvmlean_hash.o.fetch
  let oKeccak ← tvmlean_keccak.o.fetch
  let oExt ← tvmlean_crypto_ext.o.fetch
  let name := nameToStaticLib "tvmlean_crypto"
  buildStaticLib (pkg.staticLibDir / name) #[o, oHash, oKeccak, oExt]

lean_exe "tvm-lean" where
  root := `Apps.Demo

lean_exe "tvm-lean-tests" where
  root := `Apps.Tests

lean_exe "tvm-lean-diff-test" where
  root := `Apps.DiffTest

lean_exe "tvm-lean-actions-debug" where
  root := `Apps.ActionsDebug

lean_exe "tvm-lean-trace-inspect" where
  root := `Apps.TraceInspect

lean_exe "tvm-lean-precompiled-snapshot" where
  root := `Apps.PrecompiledSnapshot

lean_exe "tvm-lean-progress" where
  root := `Apps.Progress

lean_exe "tvm-lean-coverage" where
  root := `Apps.Coverage

lean_exe "tvm-lean-oracle" where
  root := `Apps.Oracle

lean_exe "tvm-lean-oracle-validate" where
  root := `Apps.Oracle
