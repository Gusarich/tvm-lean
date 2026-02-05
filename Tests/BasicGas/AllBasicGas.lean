import Tests.Registry

open TvmLean Tests

namespace Tests.BasicGas

def runInstr (i : Instr) (stack : Stack := #[]) (gas : GasLimits := GasLimits.ofLimit 1_000) (fuel : Nat := 50) :
    IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack, gas := gas }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def assertExitOk (label : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{label}: unexpected exitCode={code}"

def assertExitExc (label : String) (code : Int) (e : Excno) : IO Unit := do
  -- Unhandled out-of-gas is special-cased in C++ `VmState::run()` and returns a positive errno (13),
  -- rather than the bitwise-not wrapper used by `ExcQuit`.
  let expected : Int :=
    match e with
    | .outOfGas => e.toInt
    | _ => ~~~ e.toInt
  assert (code == expected) s!"{label}: expected {reprStr e}, got exitCode={code}"

def testBasicGas : IO Unit := do
  -- ACCEPT: change gas limit to infinity (2^63-1).
  let gas0 : GasLimits := GasLimits.ofLimit 123
  let (codeA, stA) ← runInstr (.tonEnvOp .accept) (gas := gas0)
  assertExitOk "basic_gas/accept" codeA
  assert (stA.gas.gasLimit == GasLimits.infty) s!"basic_gas/accept: expected gasLimit=infty, got {stA.gas.gasLimit}"

  -- SETGASLIMIT: set explicit limit from stack.
  let (codeS, stS) ← runInstr (.tonEnvOp .setGasLimit) (stack := #[vInt 200]) (gas := GasLimits.ofLimit 1000)
  assertExitOk "basic_gas/setgaslimit(200)" codeS
  assert (stS.gas.gasLimit == 200) s!"basic_gas/setgaslimit: expected gasLimit=200, got {stS.gas.gasLimit}"

  -- Negative => newLimit=0, which is always < already-consumed gas (instruction base gas), so outOfGas.
  let (codeS2, _stS2) ← runInstr (.tonEnvOp .setGasLimit) (stack := #[vInt (-5)]) (gas := GasLimits.ofLimit 1000)
  assertExitExc "basic_gas/setgaslimit(-5)" codeS2 .outOfGas

  -- Very large => infinity (clamped).
  let big : Int := Int.ofNat (1 <<< (63 : Nat))
  let (codeS3, stS3) ← runInstr (.tonEnvOp .setGasLimit) (stack := #[vInt big]) (gas := GasLimits.ofLimit 1000)
  assertExitOk "basic_gas/setgaslimit(big)" codeS3
  assert (stS3.gas.gasLimit == GasLimits.infty) s!"basic_gas/setgaslimit(big): expected gasLimit=infty, got {stS3.gas.gasLimit}"

  -- If new limit < gas consumed => outOfGas.
  let gasConsumed10 : GasLimits := { GasLimits.ofLimit 100 with gasRemaining := 90 }
  let (codeS4, _stS4) ← runInstr (.tonEnvOp .setGasLimit) (stack := #[vInt 5]) (gas := gasConsumed10)
  assertExitExc "basic_gas/setgaslimit(outOfGas)" codeS4 .outOfGas

  -- GASCONSUMED: push gas consumed.
  let (codeG, stG) ← runInstr (.tonEnvOp .gasConsumed) (gas := gasConsumed10)
  assertExitOk "basic_gas/gasconsumed" codeG
  assert (stG.stack.size == 1) s!"basic_gas/gasconsumed: unexpected stack size={stG.stack.size}"
  -- The returned value includes the base per-instruction gas charged by `step` (gasPerInstr + totBits).
  -- Here totBits is 16 for a 16-bit cp0 opcode, so expected = 10 (initial) + (10 + 16) = 36.
  assert (stG.stack[0]! == vInt 36) s!"basic_gas/gasconsumed: expected 36, got {stG.stack[0]!.pretty}"

  -- COMMIT: set committed state to c4/c5 (defaults are empty).
  let (codeC, stC) ← runInstr (.tonEnvOp .commit)
  assertExitOk "basic_gas/commit" codeC
  assert (stC.cstate.committed) s!"basic_gas/commit: expected committed=true"

initialize
  Tests.registerTest "basic_gas/all" testBasicGas
  Tests.registerRoundtrip (.tonEnvOp .accept)
  Tests.registerRoundtrip (.tonEnvOp .setGasLimit)
  Tests.registerRoundtrip (.tonEnvOp .gasConsumed)
  Tests.registerRoundtrip (.tonEnvOp .commit)

end Tests.BasicGas
