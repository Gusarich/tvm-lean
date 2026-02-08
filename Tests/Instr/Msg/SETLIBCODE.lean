import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.SETLIBCODE

def suite : InstrSuite where
  id := { name := "SETLIBCODE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.SETLIBCODE
