import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.LDOPTSTDADDRQ

def suite : InstrSuite where
  id := { name := "LDOPTSTDADDRQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.LDOPTSTDADDRQ
