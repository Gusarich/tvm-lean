import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULMODPOW2C_HASH

def suite : InstrSuite where
  id := { name := "MULMODPOW2C#" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2C_HASH
