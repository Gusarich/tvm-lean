import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SETALTCTR

def suite : InstrSuite where
  id := { name := "SETALTCTR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SETALTCTR
