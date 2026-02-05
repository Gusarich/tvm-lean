-- Auto-generated stub for TVM instruction MULADDDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMuladddivmod : IO Unit := do
  -- (1*1 + 0) / 2 = 0.5 -> floor => q=0, r=1
  let (exitCode1, st1) ←
    expectHalt
      (← runProg
        [ .pushInt (.num 1), .pushInt (.num 1), .pushInt (.num 0), .pushInt (.num 2)
        , .mulDivMod 3 (-1) true false
        ])
  expectExitOk "muladddivmod(1,1,0,2)" exitCode1
  assert (st1.stack.size == 2) s!"muladddivmod(1,1,0,2): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 0) s!"muladddivmod(1,1,0,2): expected q=0, got {q}"
      assert (r == 1) s!"muladddivmod(1,1,0,2): expected r=1, got {r}"
  | a, b =>
      throw (IO.userError s!"muladddivmod(1,1,0,2): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/muladddivmod" testMuladddivmod
  Tests.registerRoundtrip (.mulDivMod 3 (-1) true false)
