import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.RIST255_VALIDATE

def suite : InstrSuite where
  id := { name := "RIST255_VALIDATE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.RIST255_VALIDATE
