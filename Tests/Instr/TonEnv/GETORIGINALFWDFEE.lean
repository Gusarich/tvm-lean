import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETORIGINALFWDFEE

def suite : InstrSuite where
  id := { name := "GETORIGINALFWDFEE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETORIGINALFWDFEE
