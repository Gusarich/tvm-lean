import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Stack.PUSH_LONG

def suite : InstrSuite where
  id := { name := "PUSH_LONG" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Stack.PUSH_LONG
