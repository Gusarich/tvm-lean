import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.EXTCALL

def suite : InstrSuite where
  id := { name := "EXTCALL" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.EXTCALL
