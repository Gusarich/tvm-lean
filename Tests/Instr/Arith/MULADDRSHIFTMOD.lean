import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Arith.MULADDRSHIFTMOD

def suite : InstrSuite where
  id := { name := "MULADDRSHIFTMOD" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Arith.MULADDRSHIFTMOD
