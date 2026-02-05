-- Auto-generated stub for TVM instruction DIVMODC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testDivmodc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 3), .divMod 3 1 false false ])
  expectExitOk "divmodc(7,3)" exitCode1
  assert (st1.stack.size == 2) s!"divmodc(7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 3) s!"divmodc(7,3): expected q=3, got {q}"
      assert (r == -2) s!"divmodc(7,3): expected r=-2, got {r}"
  | a, b =>
      throw (IO.userError s!"divmodc(7,3): unexpected stack values {a.pretty}, {b.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 3 1 false false ])
  expectExitOk "divmodc(-7,3)" exitCode2
  assert (st2.stack.size == 2) s!"divmodc(-7,3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]!, st2.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == -2) s!"divmodc(-7,3): expected q=-2, got {q}"
      assert (r == -1) s!"divmodc(-7,3): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"divmodc(-7,3): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/divmodc" testDivmodc
  Tests.registerRoundtrip (.divMod 3 1 false false)
