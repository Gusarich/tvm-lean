-- Auto-generated stub for TVM instruction QMULDIVMODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQmuldivmodr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 1), .pushInt (.num 3), .mulDivMod 3 0 false true ])
  expectExitOk "qmuldivmodr(8,1,3)" exitCode1
  assert (st1.stack.size == 2) s!"qmuldivmodr(8,1,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 3) s!"qmuldivmodr(8,1,3): expected q=3, got {q}"
      assert (r == -1) s!"qmuldivmodr(8,1,3): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"qmuldivmodr(8,1,3): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qmuldivmodr" testQmuldivmodr
  Tests.registerRoundtrip (.mulDivMod 3 0 false true)
