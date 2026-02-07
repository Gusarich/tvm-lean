import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULADDRSHIFTRMOD

def suite : InstrSuite where
  id := { name := "MULADDRSHIFTRMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFTRMOD
