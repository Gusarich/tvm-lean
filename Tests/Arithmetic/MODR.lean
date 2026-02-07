-- Auto-generated stub for TVM instruction MODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testModr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .divMod 2 0 false false ])
  expectExitOk "modr(8,3)" exitCode1
  assert (st1.stack.size == 1) s!"modr(8,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"modr(8,3): expected -1, got {n}"
  | v => throw (IO.userError s!"modr(8,3): unexpected stack value {v.pretty}")

  -- tie (0.5) rounds toward +∞ (TON `BigInt::mod_div` semantics)
  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 3), .pushInt (.num 2), .divMod 2 0 false false ])
  expectExitOk "modr(3,2)" exitCode2
  assert (st2.stack.size == 1) s!"modr(3,2): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"modr(3,2): expected -1, got {n}"
  | v => throw (IO.userError s!"modr(3,2): unexpected stack value {v.pretty}")

  let (exitCode3, st3) ←
    expectHalt (← runProg [ .pushInt (.num (-3)), .pushInt (.num 2), .divMod 2 0 false false ])
  expectExitOk "modr(-3,2)" exitCode3
  assert (st3.stack.size == 1) s!"modr(-3,2): unexpected stack size={st3.stack.size}"
  match st3.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"modr(-3,2): expected -1, got {n}"
  | v => throw (IO.userError s!"modr(-3,2): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 2 0 false false ])
  -- MODR is non-quiet: division by zero returns NaN internally, then `push_int_quiet` raises int overflow.
  expectExitExc "modr(1,0)" .intOv exitCodeZ
  assert (stZ.stack.size == 1) s!"modr(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"modr(1,0): expected 0, got {n}"
  | v => throw (IO.userError s!"modr(1,0): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/modr" testModr
  Tests.registerRoundtrip (.divMod 2 0 false false)
