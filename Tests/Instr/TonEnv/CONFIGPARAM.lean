import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.CONFIGPARAM

def suite : InstrSuite where
  id := { name := "CONFIGPARAM" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.CONFIGPARAM
