import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.PUSHPOW2DEC

def suite : InstrSuite where
  id := { name := "PUSHPOW2DEC" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHPOW2DEC
