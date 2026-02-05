-- Auto-generated stub for TVM instruction MULDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMuldivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 3 (-1) false false ])
  expectExitOk "muldivmod(5,4,3)" exitCode1
  assert (st1.stack.size == 2) s!"muldivmod(5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 6) s!"muldivmod(5,4,3): expected q=6, got {q}"
      assert (r == 2) s!"muldivmod(5,4,3): expected r=2, got {r}"
  | a, b =>
      throw (IO.userError s!"muldivmod(5,4,3): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/muldivmod" testMuldivmod
  Tests.registerRoundtrip (.mulDivMod 3 (-1) false false)
