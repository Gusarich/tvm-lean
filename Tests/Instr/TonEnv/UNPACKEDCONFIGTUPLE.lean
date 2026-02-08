import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.UNPACKEDCONFIGTUPLE

def suite : InstrSuite where
  id := { name := "UNPACKEDCONFIGTUPLE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.UNPACKEDCONFIGTUPLE
