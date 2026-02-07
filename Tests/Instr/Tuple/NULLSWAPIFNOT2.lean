import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.NULLSWAPIFNOT2

def suite : InstrSuite where
  id := { name := "NULLSWAPIFNOT2" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.NULLSWAPIFNOT2
