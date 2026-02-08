import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULADDRSHIFT_HASH_MOD

def suite : InstrSuite where
  id := { name := "MULADDRSHIFT#MOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFT_HASH_MOD
