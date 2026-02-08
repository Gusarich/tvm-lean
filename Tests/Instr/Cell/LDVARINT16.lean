import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.LDVARINT16

def suite : InstrSuite where
  id := { name := "LDVARINT16" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.LDVARINT16
