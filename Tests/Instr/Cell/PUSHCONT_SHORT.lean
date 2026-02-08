import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.PUSHCONT_SHORT

def suite : InstrSuite where
  id := { name := "PUSHCONT_SHORT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.PUSHCONT_SHORT
