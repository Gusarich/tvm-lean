-- Auto-generated stub for TVM instruction CHANGELIB (category: message).
import Tests.Registry

open TvmLean Tests

def runChangeLib (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [.tonEnvOp .changeLib] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError "changelib: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testChangeLib : IO Unit := do
  -- mode=1, hash=5
  let (code0, st0) ← runChangeLib #[.int (.num 5), .int (.num 1)]
  assert (code0 == -1) s!"changelib: unexpected exitCode={code0}"
  assert (st0.stack.isEmpty) s!"changelib: unexpected stack size={st0.stack.size}"
  let expectedBits : BitString :=
    natToBits 0x26fa1dd4 32 ++
    natToBits (1 * 2) 8 ++
    natToBits 5 256
  let expectedC5 : Cell := Cell.mkOrdinary expectedBits #[Cell.empty]
  assert (st0.regs.c5 == expectedC5) s!"changelib: unexpected c5"

  -- mode=18 is allowed for global_version >= 4 semantics.
  let (code1, st1) ← runChangeLib #[.int (.num 123), .int (.num 18)]
  assert (code1 == -1) s!"changelib(mode=18): unexpected exitCode={code1}"
  let expectedBits1 : BitString :=
    natToBits 0x26fa1dd4 32 ++
    natToBits (18 * 2) 8 ++
    natToBits 123 256
  let expectedC51 : Cell := Cell.mkOrdinary expectedBits1 #[Cell.empty]
  assert (st1.regs.c5 == expectedC51) s!"changelib(mode=18): unexpected c5"

  -- Invalid mode: rangeChk.
  let (code2, _st2) ← runChangeLib #[.int (.num 0), .int (.num 4)]
  assert (code2 == (~~~ Excno.rangeChk.toInt)) s!"changelib(mode=4): expected rangeChk, got exitCode={code2}"

  -- Negative hash: rangeChk.
  let (code3, _st3) ← runChangeLib #[.int (.num (-1)), .int (.num 0)]
  assert (code3 == (~~~ Excno.rangeChk.toInt)) s!"changelib(hash=-1): expected rangeChk, got exitCode={code3}"

  -- Too-large hash (>= 2^256): rangeChk.
  let (code4, _st4) ← runChangeLib #[.int (.num (intPow2 256)), .int (.num 0)]
  assert (code4 == (~~~ Excno.rangeChk.toInt)) s!"changelib(hash=2^256): expected rangeChk, got exitCode={code4}"

initialize
  Tests.registerTest "message/changelib" testChangeLib
  Tests.registerRoundtrip (.tonEnvOp .changeLib)
