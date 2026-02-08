import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PARSEMSGADDR

def suite : InstrSuite where
  id := { name := "PARSEMSGADDR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PARSEMSGADDR
