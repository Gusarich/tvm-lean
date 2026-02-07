import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cell.SDCNTTRAIL1

def suite : InstrSuite where
  id := { name := "SDCNTTRAIL1" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cell.SDCNTTRAIL1
