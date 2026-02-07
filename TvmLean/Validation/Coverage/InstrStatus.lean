import TvmLean.Model

namespace TvmLean

inductive InstrImplStatus where
  | ok
  | stub
  | missing
  deriving Repr, BEq

structure InstrCoverageRow where
  id : String
  impl : InstrImplStatus
  unitCases : Nat
  oracleCases : Nat
  fuzzSpecs : Nat
  deriving Repr

end TvmLean
