import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_MAP_TO_G2

def suite : InstrSuite where
  id := { name := "BLS_MAP_TO_G2" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_MAP_TO_G2
