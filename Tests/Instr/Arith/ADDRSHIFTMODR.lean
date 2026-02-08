import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.ADDRSHIFTMODR

def suite : InstrSuite where
  id := { name := "ADDRSHIFTMODR" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTMODR
