import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Cont.SETCONTCTRMANYX

def suite : InstrSuite where
  id := { name := "SETCONTCTRMANYX" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Cont.SETCONTCTRMANYX
