import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVMCBLOCKS

def suite : InstrSuite where
  id := { name := "PREVMCBLOCKS" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVMCBLOCKS
