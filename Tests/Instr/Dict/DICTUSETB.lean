import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.DICTUSETB

def suite : InstrSuite where
  id := { name := "DICTUSETB" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUSETB
