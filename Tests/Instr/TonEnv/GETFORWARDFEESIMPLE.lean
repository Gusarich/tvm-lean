import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.GETFORWARDFEESIMPLE

def suite : InstrSuite where
  id := { name := "GETFORWARDFEESIMPLE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.GETFORWARDFEESIMPLE
