-- Auto-generated stub for TVM instruction QDIVMODC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testQdivmodc : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num 3), .divMod 3 1 false true ])
  expectExitOk "qdivmodc(7,3)" exitCode1
  assert (st1.stack.size == 2) s!"qdivmodc(7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 3) s!"qdivmodc(7,3): expected q=3, got {q}"
      assert (r == -2) s!"qdivmodc(7,3): expected r=-2, got {r}"
  | a, b =>
      throw (IO.userError s!"qdivmodc(7,3): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qdivmodc" testQdivmodc
  Tests.registerRoundtrip (.divMod 3 1 false true)
