import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLROTRIF

def suite : InstrSuite where
  id := { name := "NULLROTRIF" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLROTRIF
