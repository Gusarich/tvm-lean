import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.DICTREPLACEGET

def suite : InstrSuite where
  id := { name := "DICTREPLACEGET" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.DICTREPLACEGET
