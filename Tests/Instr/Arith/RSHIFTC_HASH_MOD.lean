import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.RSHIFTC_HASH_MOD

def suite : InstrSuite where
  id := { name := "RSHIFTC#MOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.RSHIFTC_HASH_MOD
