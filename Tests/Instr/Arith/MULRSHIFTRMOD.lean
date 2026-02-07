import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULRSHIFTRMOD

def suite : InstrSuite where
  id := { name := "MULRSHIFTRMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTRMOD
