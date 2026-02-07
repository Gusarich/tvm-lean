import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.SUBDICTURPGET

def suite : InstrSuite where
  id := { name := "SUBDICTURPGET" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.SUBDICTURPGET
