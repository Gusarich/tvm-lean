-- Auto-generated stub for TVM instruction QDIVMODR (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQdivmodr : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .divMod 3 0 false true ])
  expectExitOk "qdivmodr(8,3)" exitCode1
  assert (st1.stack.size == 2) s!"qdivmodr(8,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 3) s!"qdivmodr(8,3): expected q=3, got {q}"
      assert (r == -1) s!"qdivmodr(8,3): expected r=-1, got {r}"
  | a, b =>
      throw (IO.userError s!"qdivmodr(8,3): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qdivmodr" testQdivmodr
  Tests.registerRoundtrip (.divMod 3 0 false true)
