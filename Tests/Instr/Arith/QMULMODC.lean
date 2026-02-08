import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QMULMODC

def suite : InstrSuite where
  id := { name := "QMULMODC" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QMULMODC
