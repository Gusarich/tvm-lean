import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_AGGREGATEVERIFY

def suite : InstrSuite where
  id := { name := "BLS_AGGREGATEVERIFY" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_AGGREGATEVERIFY
