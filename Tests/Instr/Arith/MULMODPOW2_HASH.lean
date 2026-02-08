import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULMODPOW2_HASH

def suite : InstrSuite where
  id := { name := "MULMODPOW2#" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULMODPOW2_HASH
