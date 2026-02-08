import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSGPARAM

def suite : InstrSuite where
  id := { name := "INMSGPARAM" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSGPARAM
