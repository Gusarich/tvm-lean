import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.ADDRSHIFTR_HASH_MOD

def suite : InstrSuite where
  id := { name := "ADDRSHIFTR#MOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTR_HASH_MOD
