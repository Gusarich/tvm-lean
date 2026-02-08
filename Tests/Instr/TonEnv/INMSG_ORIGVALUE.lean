import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INMSG_ORIGVALUE

def suite : InstrSuite where
  id := { name := "INMSG_ORIGVALUE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INMSG_ORIGVALUE
