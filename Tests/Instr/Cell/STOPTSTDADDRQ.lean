import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.STOPTSTDADDRQ

def suite : InstrSuite where
  id := { name := "STOPTSTDADDRQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.STOPTSTDADDRQ
