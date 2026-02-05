-- Auto-generated stub for TVM instruction ADDDIVMODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testAdddivmodr : IO Unit := do
  -- (1 + 0) / 2 = 0.5 -> rounds away from zero => q=1, r=-1
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .pushInt (.num 2), .divMod 3 0 true false ])
  expectExitOk "adddivmodr(1,0,2)" exitCode1
  assert (st1.stack.size == 2) s!"adddivmodr(1,0,2): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 1) s!"adddivmodr(1,0,2): expected q=1, got {q}"
      assert (r == -1) s!"adddivmodr(1,0,2): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"adddivmodr(1,0,2): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/adddivmodr" testAdddivmodr
  Tests.registerRoundtrip (.divMod 3 0 true false)
