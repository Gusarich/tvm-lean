import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SAMEALTSAVE

def suite : InstrSuite where
  id := { name := "SAMEALTSAVE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SAMEALTSAVE
