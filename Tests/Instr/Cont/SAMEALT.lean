import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SAMEALT

def suite : InstrSuite where
  id := { name := "SAMEALT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SAMEALT
