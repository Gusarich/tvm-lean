import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.CALLXVARARGS

def suite : InstrSuite where
  id := { name := "CALLXVARARGS" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.CALLXVARARGS
