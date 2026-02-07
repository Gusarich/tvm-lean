-- Auto-generated stub for TVM instruction DIVC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testDivc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 1 1 false false ])
  expectExitOk "divc(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"divc(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"divc(-7,3): expected -2, got {n}"
  | v => throw (IO.userError s!"divc(-7,3): unexpected stack value {v.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num (-3)), .divMod 1 1 false false ])
  expectExitOk "divc(7,-3)" exitCode2
  assert (st2.stack.size == 1) s!"divc(7,-3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"divc(7,-3): expected -2, got {n}"
  | v => throw (IO.userError s!"divc(7,-3): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 1 1 false false ])
  -- DIVC is non-quiet: division by zero returns NaN internally, then `push_int_quiet` raises int overflow.
  expectExitExc "divc(1,0)" .intOv exitCodeZ
  assert (stZ.stack.size == 1) s!"divc(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"divc(1,0): expected 0, got {n}"
  | v => throw (IO.userError s!"divc(1,0): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/divc" testDivc
  Tests.registerRoundtrip (.divMod 1 1 false false)
