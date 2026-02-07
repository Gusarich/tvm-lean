import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DEBUG_1

def suite : InstrSuite where
  id := { name := "DEBUG_1" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DEBUG_1
