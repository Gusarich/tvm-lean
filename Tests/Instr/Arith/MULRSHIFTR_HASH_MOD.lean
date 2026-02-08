import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULRSHIFTR_HASH_MOD

def suite : InstrSuite where
  id := { name := "MULRSHIFTR#MOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTR_HASH_MOD
