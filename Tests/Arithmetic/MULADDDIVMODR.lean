-- Auto-generated stub for TVM instruction MULADDDIVMODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testMuladddivmodr : IO Unit := do
  -- (1*1 + 0) / 2 = 0.5 -> rounds away from zero => q=1, r=-1
  let (exitCode1, st1) ←
    expectHalt
      (← runProg
        [ .pushInt (.num 1), .pushInt (.num 1), .pushInt (.num 0), .pushInt (.num 2)
        , .mulDivMod 3 0 true false
        ])
  expectExitOk "muladddivmodr(1,1,0,2)" exitCode1
  assert (st1.stack.size == 2) s!"muladddivmodr(1,1,0,2): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 1) s!"muladddivmodr(1,1,0,2): expected q=1, got {q}"
      assert (r == -1) s!"muladddivmodr(1,1,0,2): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"muladddivmodr(1,1,0,2): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/muladddivmodr" testMuladddivmodr
  Tests.registerRoundtrip (.mulDivMod 3 0 true false)
