import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.SETINDEXVAR

def suite : InstrSuite where
  id := { name := "SETINDEXVAR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.SETINDEXVAR
