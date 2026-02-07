import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULADDRSHIFTCMOD

def suite : InstrSuite where
  id := { name := "MULADDRSHIFTCMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFTCMOD
