import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Tuple.SETINDEXVARQ

def suite : InstrSuite where
  id := { name := "SETINDEXVARQ" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Tuple.SETINDEXVARQ
