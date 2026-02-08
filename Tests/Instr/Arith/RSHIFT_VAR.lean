import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.RSHIFT_VAR

def suite : InstrSuite where
  id := { name := "RSHIFT_VAR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFT_VAR
