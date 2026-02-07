import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.PFXDICTSWITCH

def suite : InstrSuite where
  id := { name := "PFXDICTSWITCH" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTSWITCH
