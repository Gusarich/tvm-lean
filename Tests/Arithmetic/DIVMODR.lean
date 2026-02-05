-- Auto-generated stub for TVM instruction DIVMODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testDivmodr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .divMod 3 0 false false ])
  expectExitOk "divmodr(8,3)" exitCode1
  assert (st1.stack.size == 2) s!"divmodr(8,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 3) s!"divmodr(8,3): expected q=3, got {q}"
      assert (r == -1) s!"divmodr(8,3): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"divmodr(8,3): unexpected stack values {a.pretty}, {b.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 3), .pushInt (.num 2), .divMod 3 0 false false ])
  expectExitOk "divmodr(3,2)" exitCode2
  assert (st2.stack.size == 2) s!"divmodr(3,2): unexpected stack size={st2.stack.size}"
  match st2.stack[0]!, st2.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 2) s!"divmodr(3,2): expected q=2, got {q}"
      assert (r == -1) s!"divmodr(3,2): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"divmodr(3,2): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/divmodr" testDivmodr
  Tests.registerRoundtrip (.divMod 3 0 false false)
