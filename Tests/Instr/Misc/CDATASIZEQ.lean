import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Misc.CDATASIZEQ

def suite : InstrSuite where
  id := { name := "CDATASIZEQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Misc.CDATASIZEQ
