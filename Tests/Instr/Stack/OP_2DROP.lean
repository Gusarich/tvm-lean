import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Stack.OP_2DROP

def suite : InstrSuite where
  id := { name := "2DROP" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Stack.OP_2DROP
