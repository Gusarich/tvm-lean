import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QLSHIFTDIVMODR

def suite : InstrSuite where
  id := { name := "QLSHIFTDIVMODR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QLSHIFTDIVMODR
