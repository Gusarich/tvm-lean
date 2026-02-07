import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.BLS_FASTAGGREGATEVERIFY

def suite : InstrSuite where
  id := { name := "BLS_FASTAGGREGATEVERIFY" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.BLS_FASTAGGREGATEVERIFY
