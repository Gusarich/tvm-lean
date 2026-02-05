-- Auto-generated stub for TVM instruction SETLIBCODE (category: message).
import Tests.Registry

open TvmLean Tests

def runSetLibCode (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp .setLibCode] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "setlibcode: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testSetLibCode : IO Unit := do
  let libCode : Cell := cellOfBytes #[0xde, 0xad]

  -- mode=2: creates an action and appends it to c5.
  let (code0, st0) ← runSetLibCode #[.cell libCode, .int (.num 2)]
  assert (code0 == -1) s!"setlibcode: unexpected exitCode={code0}"
  assert (st0.stack.isEmpty) s!"setlibcode: unexpected stack size={st0.stack.size}"
  let expectedBits : BitString := natToBits 0x26fa1dd4 32 ++ natToBits (2 * 2 + 1) 8
  let expectedC5 : Cell := Cell.mkOrdinary expectedBits #[Cell.empty, libCode]
  assert (st0.regs.c5 == expectedC5) s!"setlibcode: unexpected c5"

  -- mode=17 is allowed for global_version >= 4 semantics.
  let (code1, st1) ← runSetLibCode #[.cell libCode, .int (.num 17)]
  assert (code1 == -1) s!"setlibcode(mode=17): unexpected exitCode={code1}"
  let expectedBits1 : BitString := natToBits 0x26fa1dd4 32 ++ natToBits (17 * 2 + 1) 8
  let expectedC51 : Cell := Cell.mkOrdinary expectedBits1 #[Cell.empty, libCode]
  assert (st1.regs.c5 == expectedC51) s!"setlibcode(mode=17): unexpected c5"

  -- mode=3 is invalid: rangeChk.
  let (code2, _st2) ← runSetLibCode #[.cell libCode, .int (.num 3)]
  assert (code2 == (~~~ Excno.rangeChk.toInt)) s!"setlibcode(mode=3): expected rangeChk, got exitCode={code2}"

initialize
  Tests.registerTest "message/setlibcode" testSetLibCode
  Tests.registerRoundtrip (.tonEnvOp .setLibCode)
