import Lake
open System Lake DSL

private unsafe def getEnv? (name : String) : Option String :=
  match unsafeIO (IO.getEnv name) with
  | .ok v => v
  | .error _ => none

private def envOr (name fallback : String) : String :=
  (unsafe getEnv? name).getD fallback

private def envEnabled (name : String) : Bool :=
  match unsafe getEnv? name with
  | some "1" | some "true" | some "TRUE" | some "yes" | some "on" => true
  | _ => false

private def tonSrcDir : String :=
  if System.Platform.isOSX then
    envOr "TVMLEAN_TON_SRC" "/Users/daniil/Coding/ton"
  else
    (unsafe getEnv? "TVMLEAN_TON_SRC").getD ""

private def tonBuildDir : String :=
  match unsafe getEnv? "TVMLEAN_TON_BUILD" with
  | some path => path
  | none =>
      if tonSrcDir = "" then
        ""
      else
        s!"{tonSrcDir}/build"

private def hasTonCryptoEnv : Bool :=
  (unsafe getEnv? "TVMLEAN_TON_SRC").isSome &&
  (unsafe getEnv? "TVMLEAN_TON_BUILD").isSome

private def useRealCryptoExt : Bool :=
  if System.Platform.isOSX then
    true
  else
    envEnabled "TVMLEAN_USE_REAL_CRYPTO_EXT" && hasTonCryptoEnv

package "tvm-lean" where
  version := v!"0.1.0"
  moreLinkArgs :=
    if System.Platform.isOSX then
      #[
        "-L/opt/homebrew/lib",
        "-L/usr/local/lib",
        "-L", s!"{tonBuildDir}/third-party/secp256k1/lib",
        "-L", s!"{tonBuildDir}/third-party/openssl/lib",
        "-lsodium",
        "-lsecp256k1",
        "-lssl",
        "-lcrypto",
        s!"{tonBuildDir}/third-party/blst/libblst.a"
      ]
    else if useRealCryptoExt then
      #[
        "/usr/lib/x86_64-linux-gnu/libsodium.a",
        "-L", s!"{tonBuildDir}/third-party/secp256k1/lib",
        "-L", "/usr/lib/x86_64-linux-gnu",
        "-lsecp256k1",
        "-lssl",
        "-lcrypto",
        s!"{tonBuildDir}/third-party/blst/libblst.a",
        "-ldl",
        "-pthread",
        "-lm",
        "-lz"
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
  let oFile :=
    if useRealCryptoExt then
      pkg.buildDir / "c" / "tvmlean_crypto_ext_real.o"
    else
      pkg.buildDir / "c" / "tvmlean_crypto_ext_stub.o"
  let leanIncludeDir := (← getLeanIncludeDir).toString
  let srcPath :=
    if useRealCryptoExt then
      pkg.dir / "c" / "tvmlean_crypto_ext.c"
    else
      pkg.dir / "c" / "tvmlean_crypto_ext_stub.c"
  let srcJob ← inputTextFile srcPath
  let weakArgs :=
    if useRealCryptoExt then
      #[
        "-I", leanIncludeDir,
        "-I", (pkg.dir / "c").toString,
        "-I", "/opt/homebrew/include",
        "-I", "/usr/local/include",
        "-I", s!"{tonSrcDir}/third-party/secp256k1/include",
        "-I", s!"{tonBuildDir}/third-party/secp256k1/include",
        "-I", s!"{tonSrcDir}/third-party/blst/bindings"
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
