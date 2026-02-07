import TvmLean.OracleValidate
import Tests.Registry
import Tests.Util

namespace Tests

def getEnvTrim? (name : String) : IO (Option String) := do
  match (← IO.getEnv name) with
  | none => pure none
  | some raw =>
      let v := raw.trim
      if v == "" then pure none else pure (some v)

def parseNatEnv (name : String) (default : Nat) : IO Nat := do
  match (← getEnvTrim? name) with
  | none => pure default
  | some v =>
      match v.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"invalid Nat in {name}={v}")

def parseBoolEnv (name : String) (default : Bool) : IO Bool := do
  match (← getEnvTrim? name) with
  | none => pure default
  | some "1" => pure true
  | some "true" => pure true
  | some "TRUE" => pure true
  | some "yes" => pure true
  | some "YES" => pure true
  | some "on" => pure true
  | some "ON" => pure true
  | some "0" => pure false
  | some "false" => pure false
  | some "FALSE" => pure false
  | some "no" => pure false
  | some "NO" => pure false
  | some "off" => pure false
  | some "OFF" => pure false
  | some v => throw (IO.userError s!"invalid Bool in {name}={v}")

def testOracleParity : IO Unit := do
  let enabled ← parseBoolEnv "TVMLEAN_ORACLE_ENABLED" true
  if !enabled then
    IO.println "oracle/parity: skipped (TVMLEAN_ORACLE_ENABLED=0)"
    return ()

  let variants ← parseNatEnv "TVMLEAN_ORACLE_VARIANTS" 20
  let codeVariants ← parseNatEnv "TVMLEAN_ORACLE_CODE_VARIANTS" 8
  let cases ← parseNatEnv "TVMLEAN_ORACLE_CASES" 20
  let minCases ← parseNatEnv "TVMLEAN_ORACLE_MIN_CASES" 10
  let maxNoSigDepth ← parseNatEnv "TVMLEAN_ORACLE_MAX_NOSIG_DEPTH" 64
  let randomCases ← parseNatEnv "TVMLEAN_ORACLE_RANDOM_CASES" 0
  let seed ← parseNatEnv "TVMLEAN_ORACLE_SEED" 1
  let verbose ← parseBoolEnv "TVMLEAN_ORACLE_VERBOSE" false
  let onlyName? ← getEnvTrim? "TVMLEAN_ORACLE_ONLY"
  let limit? ← parseNatEnv "TVMLEAN_ORACLE_LIMIT" 0

  assert (cases >= minCases)
    s!"oracle/parity: TVMLEAN_ORACLE_CASES={cases} must be >= TVMLEAN_ORACLE_MIN_CASES={minCases}"

  let mut args : Array String :=
    #[
      "--variants", toString variants,
      "--code-variants", toString codeVariants,
      "--cases", toString cases,
      "--max-nosig-depth", toString maxNoSigDepth,
      "--min-cases", toString minCases,
      "--random-cases", toString randomCases,
      "--seed", toString seed
    ]
  match onlyName? with
  | some n => args := args ++ #["--only", n]
  | none => pure ()
  if limit? > 0 then
    args := args ++ #["--limit", toString limit?]
  if verbose then
    args := args.push "--verbose"

  IO.println s!"oracle/parity: variants={variants} code_variants={codeVariants} cases={cases} min_cases={minCases} random_cases={randomCases} seed={seed}"
  let rc ← TvmLeanOracleValidate.main args.toList
  assert (rc == 0) s!"oracle/parity: validator exited with code {rc}"

initialize
  Tests.registerTest "oracle/parity_all_instructions" testOracleParity

end Tests
