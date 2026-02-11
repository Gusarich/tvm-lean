import Lean
import Tests.Harness.Registry
import Tests.Harness.OracleHarness

namespace Tests

open Lean

structure FuzzFailure where
  iteration : Nat
  result : OracleRunResult
  artifact? : Option System.FilePath := none
  deriving Repr

structure FuzzRunResult where
  seed : UInt64
  total : Nat
  failures : Array FuzzFailure
  artifacts : Array System.FilePath
  deriving Repr

private def sanitizeFileToken (s : String) : String :=
  String.map (fun c => if c.isAlphanum || c = '_' || c = '-' then c else '_') s

private def fuzzArtifactDir : IO System.FilePath := do
  let dir := (← IO.getEnv "TVMLEAN_FUZZ_FAILURE_DIR").getD "build/fuzz-failures"
  pure dir

private def oracleCaseJson (c : OracleCase) : Json :=
  Json.mkObj
    [ ("name", Json.str c.name)
    , ("instr", Json.str c.instr.name)
    , ("program", Json.str (reprStr c.program))
    , ("initStack", Json.str (reprStr c.initStack))
    , ("initCregs", Json.str (reprStr c.initCregs))
    , ("initC7", Json.str (reprStr c.initC7))
    , ("gasLimits", Json.mkObj
        [ ("gasLimit", ToJson.toJson c.gasLimits.gasLimit)
        , ("gasMax", ToJson.toJson c.gasLimits.gasMax)
        , ("gasCredit", ToJson.toJson c.gasLimits.gasCredit)
        ])
    , ("fuel", ToJson.toJson c.fuel)
    ]

private def dumpFailureArtifact
    (seed : UInt64)
    (iteration : Nat)
    (oracleCase : OracleCase)
    (runResult : OracleRunResult) : IO (Option System.FilePath) := do
  try
    let dir ← fuzzArtifactDir
    IO.FS.createDirAll dir
    let fileName :=
      s!"{sanitizeFileToken oracleCase.instr.name}_seed_{seed.toNat}_iter_{iteration}.json"
    let outPath := dir / fileName
    let body :=
      Json.mkObj
        [ ("instruction", Json.str oracleCase.instr.name)
        , ("seed", ToJson.toJson seed.toNat)
        , ("iteration", ToJson.toJson iteration)
        , ("case", oracleCaseJson oracleCase)
        , ("comparison",
            match runResult.comparison? with
            | some cmp => ToJson.toJson cmp
            | none => Json.null)
        , ("error",
            match runResult.error? with
            | some e => Json.str e
            | none => Json.null)
        ]
    IO.FS.writeFile outPath body.pretty
    pure (some outPath)
  catch _ =>
    pure none

private def replayCaseName (baseName : String) (iteration : Nat) (tag : Nat) : String :=
  s!"{baseName}/replay-{iteration}-{tag}"

private def nextFuzzOracleCase
    (spec : FuzzSpec)
    (oraclePool : Array OracleCase)
    (iteration : Nat)
    (gen : StdGen) : OracleCase × StdGen :=
  if spec.replayOracle then
    if oraclePool.isEmpty then
      spec.gen gen
    else
      let (idx, gen1) := randNat gen 0 (oraclePool.size - 1)
      let (tag, gen2) := randNat gen1 0 999_999
      match oraclePool[idx]? with
      | some oracleCase =>
          ({ oracleCase with name := replayCaseName oracleCase.name iteration tag }, gen2)
      | none =>
          let (fallback, gen3) := spec.gen gen2
          ({ fallback with name := replayCaseName fallback.name iteration tag }, gen3)
  else
    spec.gen gen

def runFuzzSpec (spec : FuzzSpec) (oraclePool : Array OracleCase := #[]) : IO FuzzRunResult := do
  let mut gen := mkStdGen spec.seed.toNat
  let mut i : Nat := 0
  let mut failures : Array FuzzFailure := #[]
  let mut artifacts : Array System.FilePath := #[]
  while i < spec.count do
    let (oracleCase, gen') := nextFuzzOracleCase spec oraclePool i gen
    gen := gen'
    let out ← runOracleCase oracleCase
    if !out.ok then
      let artifact? ← dumpFailureArtifact spec.seed i oracleCase out
      failures := failures.push { iteration := i, result := out, artifact? := artifact? }
      match artifact? with
      | some p => artifacts := artifacts.push p
      | none => pure ()
    i := i + 1
  pure { seed := spec.seed, total := spec.count, failures := failures, artifacts := artifacts }

end Tests
