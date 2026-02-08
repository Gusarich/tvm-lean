import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSG_STATEINIT

def suite : InstrSuite where
  id := { name := "INMSG_STATEINIT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSG_STATEINIT
