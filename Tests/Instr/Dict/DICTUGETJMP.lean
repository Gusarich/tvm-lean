import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Dict.DICTUGETJMP

def suite : InstrSuite where
  id := { name := "DICTUGETJMP" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Dict.DICTUGETJMP
