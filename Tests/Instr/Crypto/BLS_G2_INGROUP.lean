import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_G2_INGROUP

def suite : InstrSuite where
  id := { name := "BLS_G2_INGROUP" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_G2_INGROUP
