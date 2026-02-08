import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.QMULADDRSHIFTRMOD

def suite : InstrSuite where
  id := { name := "QMULADDRSHIFTRMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.QMULADDRSHIFTRMOD
