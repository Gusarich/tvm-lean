import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.UNPACKFIRST

def suite : InstrSuite where
  id := { name := "UNPACKFIRST" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.UNPACKFIRST
