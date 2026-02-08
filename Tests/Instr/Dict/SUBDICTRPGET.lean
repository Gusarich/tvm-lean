import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.SUBDICTRPGET

def suite : InstrSuite where
  id := { name := "SUBDICTRPGET" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTRPGET
