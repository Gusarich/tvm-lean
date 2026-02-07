import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.UNPACKFIRSTVAR

def suite : InstrSuite where
  id := { name := "UNPACKFIRSTVAR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.UNPACKFIRSTVAR
