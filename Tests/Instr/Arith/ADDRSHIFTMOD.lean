import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.ADDRSHIFTMOD

def suite : InstrSuite where
  id := { name := "ADDRSHIFTMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.ADDRSHIFTMOD
