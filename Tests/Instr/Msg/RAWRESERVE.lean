import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Msg.RAWRESERVE

def suite : InstrSuite where
  id := { name := "RAWRESERVE" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Msg.RAWRESERVE
