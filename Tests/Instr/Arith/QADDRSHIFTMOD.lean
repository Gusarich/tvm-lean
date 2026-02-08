import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QADDRSHIFTMOD

def suite : InstrSuite where
  id := { name := "QADDRSHIFTMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QADDRSHIFTMOD
