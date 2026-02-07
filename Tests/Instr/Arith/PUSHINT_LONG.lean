import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.PUSHINT_LONG

def suite : InstrSuite where
  id := { name := "PUSHINT_LONG" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.PUSHINT_LONG
