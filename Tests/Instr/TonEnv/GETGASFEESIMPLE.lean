import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETGASFEESIMPLE

def suite : InstrSuite where
  id := { name := "GETGASFEESIMPLE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETGASFEESIMPLE
