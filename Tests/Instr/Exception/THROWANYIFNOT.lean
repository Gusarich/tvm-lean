import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWANYIFNOT

def suite : InstrSuite where
  id := { name := "THROWANYIFNOT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWANYIFNOT
