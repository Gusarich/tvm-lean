import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.LSHIFT_HASH_DIV

def suite : InstrSuite where
  id := { name := "LSHIFT#DIV" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_DIV
