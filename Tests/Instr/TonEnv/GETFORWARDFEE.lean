import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETFORWARDFEE

def suite : InstrSuite where
  id := { name := "GETFORWARDFEE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETFORWARDFEE
