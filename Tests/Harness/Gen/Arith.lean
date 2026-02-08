import Tests.Harness.Registry
import TvmLean

open TvmLean

namespace Tests.Harness.Gen.Arith

def pow2 (n : Nat) : Int :=
  (2 : Int) ^ n

def minInt257 : Int :=
  -(pow2 256)

def maxInt257 : Int :=
  (pow2 256) - 1

def intV (n : Int) : Value :=
  .int (.num n)

def intFitsSigned257 (n : Int) : Bool :=
  minInt257 ≤ n && n ≤ maxInt257

def intValOracleSerializable : IntVal → Bool
  | .nan => false
  | .num n => intFitsSigned257 n

def oracleIntInputsToStackOrProgram (vals : Array IntVal) : Array Value × Array Instr :=
  if vals.all intValOracleSerializable then
    let stack : Array Value := vals.map (fun v =>
      match v with
      | .num n => intV n
      | .nan => .int .nan)
    (stack, #[])
  else
    (#[], vals.map Instr.pushInt)

def int257BoundaryPool : Array Int :=
  #[
    0, 1, -1, 2, -2, 3, -3,
    pow2 32, -(pow2 32),
    pow2 64, -(pow2 64),
    pow2 128, -(pow2 128),
    pow2 255, -(pow2 255),
    maxInt257, maxInt257 - 1, maxInt257 - 2,
    minInt257, minInt257 + 1, minInt257 + 2
  ]

def pickInt257Boundary (rng : StdGen) : Int × StdGen :=
  let (idx, rng') := randNat rng 0 (int257BoundaryPool.size - 1)
  (int257BoundaryPool[idx]!, rng')

def pickLogUniformSigned257ish (rng0 : StdGen) : Int × StdGen := Id.run do
  let (k, rng1) := randNat rng0 0 256
  if k = 0 then
    return (0, rng1)
  else
    let lo : Nat := 1 <<< (k - 1)
    let hi : Nat := (1 <<< k) - 1
    let (magnitude, rng2) := randNat rng1 lo hi
    let (neg, rng3) := randBool rng2
    let n := Int.ofNat magnitude
    return (if neg then -n else n, rng3)

def randLogUniformSigned (rng : StdGen) : Int × StdGen :=
  pickLogUniformSigned257ish rng

/--
  10% boundary sampling, 90% log-uniform signed values with magnitudes up to `2^256 - 1`.
-/
def pickSigned257ish (rng0 : StdGen) : Int × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode = 0 then
    pickInt257Boundary rng1
  else
    pickLogUniformSigned257ish rng1

def singleInstrCp0GasBudget (instr : Instr) : Except Excno Int := do
  let code ← assembleCp0 [instr]
  let (decoded, totBits, _) ← decodeCp0WithBits (Slice.ofCell code)
  pure (instrGas decoded totBits)

def oracleGasLimitsExact (budget : Int) : OracleGasLimits :=
  { gasLimit := budget
    gasMax := budget
    gasCredit := 0 }

def oracleGasLimitsExactMinusOne (budget : Int) : OracleGasLimits :=
  let budget' := if budget > 0 then budget - 1 else 0
  oracleGasLimitsExact budget'

def singleInstrCp0OracleGasExact (instr : Instr) : Except Excno OracleGasLimits := do
  let budget ← singleInstrCp0GasBudget instr
  pure (oracleGasLimitsExact budget)

def singleInstrCp0OracleGasExactMinusOne (instr : Instr) : Except Excno OracleGasLimits := do
  let budget ← singleInstrCp0GasBudget instr
  pure (oracleGasLimitsExactMinusOne budget)

def singleInstrCp0OracleGasPair (instr : Instr) : Except Excno (OracleGasLimits × OracleGasLimits) := do
  let budget ← singleInstrCp0GasBudget instr
  pure (oracleGasLimitsExact budget, oracleGasLimitsExactMinusOne budget)

private def gasForInstrWithFallback (instr : Instr) : Int :=
  match singleInstrCp0GasBudget instr with
  | .ok budget => budget
  | .error _ => instrGas instr 16

private def setGasNeedForInstr (instr : Instr) (n : Int) : Int :=
  gasForInstrWithFallback (.pushInt (.num n))
    + gasForInstrWithFallback (.tonEnvOp .setGasLimit)
    + gasForInstrWithFallback instr
    + implicitRetGasPrice

private def exactGasBudgetFixedPoint (instr : Instr) (n : Int) : Nat → Int
  | 0 => n
  | k + 1 =>
      let n' := setGasNeedForInstr instr n
      if n' = n then n else exactGasBudgetFixedPoint instr n' k

def computeExactGasBudget (instr : Instr) : Int :=
  exactGasBudgetFixedPoint instr 64 16

def computeExactGasBudgetMinusOne (instr : Instr) : Int :=
  let budget := computeExactGasBudget instr
  if budget > 0 then budget - 1 else 0

def runHandlerDirectWithNext
    (handler : Instr → VM Unit → VM Unit)
    (instr : Instr)
    (next : VM Unit)
    (stack : Array Value) : Except Excno (Array Value) :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  let (res, st1) := (handler instr next).run st0
  match res with
  | .ok _ => .ok st1.stack
  | .error e => .error e

def runHandlerDirect
    (handler : Instr → VM Unit → VM Unit)
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext handler instr (pure ()) stack

def expectOkStack
    (label : String)
    (res : Except Excno (Array Value))
    (expected : Array Value) : IO Unit := do
  match res with
  | .ok st =>
      if st == expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected stack {reprStr expected}, got {reprStr st}")
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got error {e}")

def expectErr
    (label : String)
    (res : Except Excno (Array Value))
    (expected : Excno) : IO Unit := do
  match res with
  | .ok st =>
      throw (IO.userError s!"{label}: expected error {expected}, got stack {reprStr st}")
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected error {expected}, got {e}")

end Tests.Harness.Gen.Arith
