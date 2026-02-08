import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.CALLCCVARARGS

def suite : InstrSuite where
  id := { name := "CALLCCVARARGS" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.CALLCCVARARGS
