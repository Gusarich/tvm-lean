import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SAVEBOTHCTR

def suite : InstrSuite where
  id := { name := "SAVEBOTHCTR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SAVEBOTHCTR
