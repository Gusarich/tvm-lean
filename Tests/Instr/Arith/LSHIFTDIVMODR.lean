import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.LSHIFTDIVMODR

def suite : InstrSuite where
  id := { name := "LSHIFTDIVMODR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.LSHIFTDIVMODR
