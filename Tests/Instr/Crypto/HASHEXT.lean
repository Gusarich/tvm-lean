import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.HASHEXT

def suite : InstrSuite where
  id := { name := "HASHEXT" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.HASHEXT
