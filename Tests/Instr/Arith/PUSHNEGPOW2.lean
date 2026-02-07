import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.PUSHNEGPOW2

def suite : InstrSuite where
  id := { name := "PUSHNEGPOW2" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHNEGPOW2
