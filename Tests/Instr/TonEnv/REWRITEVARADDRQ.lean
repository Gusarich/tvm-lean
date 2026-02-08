import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.TonEnv.REWRITEVARADDRQ

def suite : InstrSuite where
  id := { name := "REWRITEVARADDRQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.TonEnv.REWRITEVARADDRQ
