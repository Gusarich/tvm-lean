import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWIFNOT_SHORT

def suite : InstrSuite where
  id := { name := "THROWIFNOT_SHORT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWIFNOT_SHORT
