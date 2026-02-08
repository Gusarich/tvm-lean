import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.SSKIPLAST

def suite : InstrSuite where
  id := { name := "SSKIPLAST" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SSKIPLAST
