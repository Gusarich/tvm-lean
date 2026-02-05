-- Auto-generated stub for TVM instruction MULMODC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMulmodc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-5)), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 2 1 false false ])
  expectExitOk "mulmodc(-5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"mulmodc(-5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -2) s!"mulmodc(-5,4,3): expected -2, got {n}"
  | v => throw (IO.userError s!"mulmodc(-5,4,3): unexpected stack value {v.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 2 1 false false ])
  expectExitOk "mulmodc(5,4,3)" exitCode2
  assert (st2.stack.size == 1) s!"mulmodc(5,4,3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == -1) s!"mulmodc(5,4,3): expected -1, got {n}"
  | v => throw (IO.userError s!"mulmodc(5,4,3): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/mulmodc" testMulmodc
  Tests.registerRoundtrip (.mulDivMod 2 1 false false)
