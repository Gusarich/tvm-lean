import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Misc.SDATASIZE

def suite : InstrSuite where
  id := { name := "SDATASIZE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Misc.SDATASIZE
