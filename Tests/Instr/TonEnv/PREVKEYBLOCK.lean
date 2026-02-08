import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.PREVKEYBLOCK

def suite : InstrSuite where
  id := { name := "PREVKEYBLOCK" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.PREVKEYBLOCK
