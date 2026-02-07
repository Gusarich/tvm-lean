import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QMULRSHIFTRMOD

def suite : InstrSuite where
  id := { name := "QMULRSHIFTRMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTRMOD
