import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULRSHIFTCMOD

def suite : InstrSuite where
  id := { name := "MULRSHIFTCMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULRSHIFTCMOD
