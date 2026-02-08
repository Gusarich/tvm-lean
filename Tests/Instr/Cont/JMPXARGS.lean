import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.JMPXARGS

def suite : InstrSuite where
  id := { name := "JMPXARGS" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.JMPXARGS
