import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLROTRIFNOT

def suite : InstrSuite where
  id := { name := "NULLROTRIFNOT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLROTRIFNOT
