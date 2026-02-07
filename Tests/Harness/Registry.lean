import Std
import TvmLean
import TvmLean.Spec.Index

open TvmLean

namespace Tests

structure UnitCase where
  name : String
  run : IO Unit

structure OracleCase where
  name : String
  instr : InstrId
  program : Array Instr := #[]
  initStack : Array Value := #[]
  fuel : Nat := 1_000_000

structure FuzzSpec where
  seed : UInt64
  count : Nat
  gen : StdGen → OracleCase × StdGen

structure InstrSuite where
  id : InstrId
  unit : Array UnitCase := #[]
  oracle : Array OracleCase := #[]
  fuzz : Array FuzzSpec := #[]

initialize instrSuiteRegistry : IO.Ref (Array InstrSuite) ← IO.mkRef #[]

def registerSuite (suite : InstrSuite) : IO Unit := do
  instrSuiteRegistry.modify (·.push suite)

def registeredSuites : IO (Array InstrSuite) :=
  instrSuiteRegistry.get

end Tests
