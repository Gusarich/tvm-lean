import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.DICTIREPLACEB

def suite : InstrSuite where
  id := { name := "DICTIREPLACEB" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.DICTIREPLACEB
