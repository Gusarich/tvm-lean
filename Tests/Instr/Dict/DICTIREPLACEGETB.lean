import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.DICTIREPLACEGETB

def suite : InstrSuite where
  id := { name := "DICTIREPLACEGETB" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEGETB
