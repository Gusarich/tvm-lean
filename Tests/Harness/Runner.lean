import Tests.Harness.Registry
import Tests.Harness.OracleHarness
import Tests.Harness.FuzzHarness

namespace Tests

structure RunnerOpts where
  filter? : Option String := none
  unitOnly : Bool := false
  oracleOnly : Bool := false
  fuzzOnly : Bool := false
  deriving Repr

structure RunnerSummary where
  suites : Nat := 0
  unitCases : Nat := 0
  oracleCases : Nat := 0
  fuzzCases : Nat := 0
  failures : Nat := 0
  deriving Repr

def suiteSelected (opts : RunnerOpts) (suite : InstrSuite) : Bool :=
  match opts.filter? with
  | none => true
  | some needle => suite.id.name = needle

def runUnitCase (suite : InstrSuite) (c : UnitCase) : IO (Option String) := do
  try
    c.run
    pure none
  catch e =>
    pure (some s!"{suite.id.name}/{c.name}: {e.toString}")

def runSuites (opts : RunnerOpts) : IO RunnerSummary := do
  let suites ← registeredSuites
  let mut summary : RunnerSummary := {}

  for suite in suites do
    if suiteSelected opts suite then
      summary := { summary with suites := summary.suites + 1 }

      if !opts.oracleOnly && !opts.fuzzOnly then
        for c in suite.unit do
          summary := { summary with unitCases := summary.unitCases + 1 }
          let err? ← runUnitCase suite c
          if err?.isSome then
            summary := { summary with failures := summary.failures + 1 }

      if !opts.unitOnly && !opts.fuzzOnly then
        for c in suite.oracle do
          summary := { summary with oracleCases := summary.oracleCases + 1 }
          let out ← runOracleCase c
          if !out.ok then
            summary := { summary with failures := summary.failures + 1 }

      if !opts.unitOnly && !opts.oracleOnly then
        for spec in suite.fuzz do
          let out ← runFuzzSpec spec
          summary := { summary with fuzzCases := summary.fuzzCases + out.total }
          summary := { summary with failures := summary.failures + out.failures.size }

  pure summary

def printSummary (s : RunnerSummary) : IO Unit := do
  IO.println s!"suites={s.suites} unit={s.unitCases} oracle={s.oracleCases} fuzz={s.fuzzCases} failures={s.failures}"

/-- Returns 0 on success, 1 when at least one case failed. -/
def runAndReport (opts : RunnerOpts) : IO UInt32 := do
  let summary ← runSuites opts
  printSummary summary
  if summary.failures = 0 then
    pure 0
  else
    pure 1

end Tests
