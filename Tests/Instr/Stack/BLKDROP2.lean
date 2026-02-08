import Tests.Harness.Registry
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Stack.BLKDROP2

def suite : InstrSuite where
  id := { name := "BLKDROP2" }
  unit := #[]
  oracle := #[]
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Stack.BLKDROP2
