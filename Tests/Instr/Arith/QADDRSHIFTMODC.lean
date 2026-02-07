import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QADDRSHIFTMODC

def suite : InstrSuite where
  id := { name := "QADDRSHIFTMODC" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QADDRSHIFTMODC
