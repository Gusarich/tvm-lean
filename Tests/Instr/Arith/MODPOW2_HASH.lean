import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MODPOW2_HASH

def suite : InstrSuite where
  id := { name := "MODPOW2#" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2_HASH
