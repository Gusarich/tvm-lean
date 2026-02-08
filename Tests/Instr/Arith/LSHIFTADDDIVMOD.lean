import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.LSHIFTADDDIVMOD

def suite : InstrSuite where
  id := { name := "LSHIFTADDDIVMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTADDDIVMOD
