import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Exception.THROWARGIF

def suite : InstrSuite where
  id := { name := "THROWARGIF" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Exception.THROWARGIF
