import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.BCHKBITSQ_VAR

def suite : InstrSuite where
  id := { name := "BCHKBITSQ_VAR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKBITSQ_VAR
