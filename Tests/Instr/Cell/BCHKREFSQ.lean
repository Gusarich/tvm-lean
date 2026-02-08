import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.BCHKREFSQ

def suite : InstrSuite where
  id := { name := "BCHKREFSQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.BCHKREFSQ
