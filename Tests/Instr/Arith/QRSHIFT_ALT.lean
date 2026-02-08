import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QRSHIFT_ALT

def suite : InstrSuite where
  id := { name := "QRSHIFT_ALT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QRSHIFT_ALT
