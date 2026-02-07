-- Auto-generated stub for TVM instruction MULMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMulmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-5)), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 2 (-1) false false ])
  expectExitOk "mulmod(-5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"mulmod(-5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 1) s!"mulmod(-5,4,3): expected 1, got {n}"
  | v => throw (IO.userError s!"mulmod(-5,4,3): unexpected stack value {v.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 2 (-1) false false ])
  expectExitOk "mulmod(5,4,3)" exitCode2
  assert (st2.stack.size == 1) s!"mulmod(5,4,3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == 2) s!"mulmod(5,4,3): expected 2, got {n}"
  | v => throw (IO.userError s!"mulmod(5,4,3): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 0), .mulDivMod 2 (-1) false false ])
  -- MULMOD is non-quiet: division by zero returns NaN internally, then `push_int_quiet` raises int overflow.
  expectExitExc "mulmod(5,4,0)" .intOv exitCodeZ
  assert (stZ.stack.size == 1) s!"mulmod(5,4,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"mulmod(5,4,0): expected 0, got {n}"
  | v => throw (IO.userError s!"mulmod(5,4,0): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/mulmod" testMulmod
  Tests.registerRoundtrip (.mulDivMod 2 (-1) false false)
