import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVMCBLOCKS_100

def suite : InstrSuite where
  id := { name := "PREVMCBLOCKS_100" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVMCBLOCKS_100
