import Std
import TvmLean
import TvmLean.Spec.Index

open TvmLean

namespace Tests

structure UnitCase where
  name : String
  run : IO Unit

structure OracleInitCregs where
  c0 : Option Continuation := none
  c1 : Option Continuation := none
  c2 : Option Continuation := none
  c3 : Option Continuation := none
  c4 : Option Cell := none
  c5 : Option Cell := none
  deriving Repr

structure OracleGasLimits where
  gasLimit : Int := 1_000_000
  gasMax : Int := 1_000_000
  gasCredit : Int := 0
  deriving Repr

structure OracleCase where
  name : String
  instr : InstrId
  program : Array Instr := #[]
  /-- Optional pre-assembled cp0 code cell (used for instructions with inline refs/consts that `assembleCp0` rejects). -/
  codeCell? : Option Cell := none
  initStack : Array Value := #[]
  initCregs : OracleInitCregs := {}
  initC7 : Array Value := #[]
  /-- Optional library collection cells used by `XLOAD{Q}` (mirrors C++ `VmState.libraries`). -/
  initLibraries : Array Cell := #[]
  gasLimits : OracleGasLimits := {}
  fuel : Nat := 1_000_000
  deriving Repr

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
