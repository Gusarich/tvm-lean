import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QMULRSHIFTCMOD

def suite : InstrSuite where
  id := { name := "QMULRSHIFTCMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTCMOD
