import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.ADDRSHIFTMODC

def suite : InstrSuite where
  id := { name := "ADDRSHIFTMODC" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTMODC
