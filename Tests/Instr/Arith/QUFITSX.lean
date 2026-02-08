import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QUFITSX

def suite : InstrSuite where
  id := { name := "QUFITSX" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QUFITSX
