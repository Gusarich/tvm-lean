import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SETCONTCTRMANY

def suite : InstrSuite where
  id := { name := "SETCONTCTRMANY" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTRMANY
