import Tests.Harness.Registry
import Tests.Harness.OracleHarness

namespace Tests

structure FuzzRunResult where
  seed : UInt64
  total : Nat
  failures : Array OracleRunResult
  deriving Repr

def runFuzzSpec (spec : FuzzSpec) : IO FuzzRunResult := do
  let mut gen := mkStdGen spec.seed.toNat
  let mut i : Nat := 0
  let mut failures : Array OracleRunResult := #[]
  while i < spec.count do
    let (oracleCase, gen') := spec.gen gen
    gen := gen'
    let out ← runOracleCase oracleCase
    if !out.ok then
      failures := failures.push out
    i := i + 1
  pure { seed := spec.seed, total := spec.count, failures := failures }

end Tests
