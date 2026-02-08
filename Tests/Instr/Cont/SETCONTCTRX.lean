import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SETCONTCTRX

def suite : InstrSuite where
  id := { name := "SETCONTCTRX" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTRX
