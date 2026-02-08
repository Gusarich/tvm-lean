import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QMULRSHIFTC

def suite : InstrSuite where
  id := { name := "QMULRSHIFTC" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QMULRSHIFTC
