import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.INCOMINGVALUE

def suite : InstrSuite where
  id := { name := "INCOMINGVALUE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.INCOMINGVALUE
