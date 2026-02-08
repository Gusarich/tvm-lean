import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.LSHIFT_HASH_DIVMOD

def suite : InstrSuite where
  id := { name := "LSHIFT#DIVMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFT_HASH_DIVMOD
