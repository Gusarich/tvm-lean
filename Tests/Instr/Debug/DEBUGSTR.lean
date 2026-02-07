import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Debug.DEBUGSTR

def suite : InstrSuite where
  id := { name := "DEBUGSTR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Debug.DEBUGSTR
