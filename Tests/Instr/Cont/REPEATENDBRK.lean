import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.REPEATENDBRK

def suite : InstrSuite where
  id := { name := "REPEATENDBRK" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.REPEATENDBRK
