import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.SCHKBITREFSQ

def suite : InstrSuite where
  id := { name := "SCHKBITREFSQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SCHKBITREFSQ
