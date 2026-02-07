import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSG_VALUEEXTRA

def suite : InstrSuite where
  id := { name := "INMSG_VALUEEXTRA" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSG_VALUEEXTRA
