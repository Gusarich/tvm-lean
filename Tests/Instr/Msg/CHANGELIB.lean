import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.CHANGELIB

def suite : InstrSuite where
  id := { name := "CHANGELIB" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.CHANGELIB
