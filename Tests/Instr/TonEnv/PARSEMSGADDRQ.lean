import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PARSEMSGADDRQ

def suite : InstrSuite where
  id := { name := "PARSEMSGADDRQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PARSEMSGADDRQ
