import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MODPOW2C

def suite : InstrSuite where
  id := { name := "MODPOW2C" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MODPOW2C
