import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.STRDUMP

def suite : InstrSuite where
  id := { name := "STRDUMP" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.STRDUMP
