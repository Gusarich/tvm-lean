-- Auto-generated stub for TVM instruction ADDDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testAdddivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .pushInt (.num 2), .divMod 3 (-1) true false ])
  expectExitOk "adddivmod(1,0,2)" exitCode1
  assert (st1.stack.size == 2) s!"adddivmod(1,0,2): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 0) s!"adddivmod(1,0,2): expected q=0, got {q}"
      assert (r == 1) s!"adddivmod(1,0,2): expected r=1, got {r}"
  | a, b =>
      throw (IO.userError s!"adddivmod(1,0,2): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/adddivmod" testAdddivmod
  Tests.registerRoundtrip (.divMod 3 (-1) true false)
