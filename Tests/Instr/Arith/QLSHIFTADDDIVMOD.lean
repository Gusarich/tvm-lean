import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QLSHIFTADDDIVMOD

def suite : InstrSuite where
  id := { name := "QLSHIFTADDDIVMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTADDDIVMOD
