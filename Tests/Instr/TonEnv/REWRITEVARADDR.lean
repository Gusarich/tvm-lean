import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.REWRITEVARADDR

def suite : InstrSuite where
  id := { name := "REWRITEVARADDR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.REWRITEVARADDR
