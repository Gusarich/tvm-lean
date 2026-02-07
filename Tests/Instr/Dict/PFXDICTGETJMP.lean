import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.PFXDICTGETJMP

def suite : InstrSuite where
  id := { name := "PFXDICTGETJMP" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.PFXDICTGETJMP
