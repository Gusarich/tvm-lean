import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_G1_MULTIEXP

def suite : InstrSuite where
  id := { name := "BLS_G1_MULTIEXP" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_G1_MULTIEXP
