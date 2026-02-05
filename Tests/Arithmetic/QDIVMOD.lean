-- Auto-generated stub for TVM instruction QDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testQdivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .divMod 3 (-1) false true ])
  expectExitOk "qdivmod(8,3)" exitCode1
  assert (st1.stack.size == 2) s!"qdivmod(8,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 2) s!"qdivmod(8,3): expected q=2, got {q}"
      assert (r == 2) s!"qdivmod(8,3): expected r=2, got {r}"
  | a, b =>
      throw (IO.userError s!"qdivmod(8,3): unexpected stack values {a.pretty}, {b.pretty}")

  -- quotient overflows, remainder fits: MIN_INT / -1.
  let (exitCodeOv, stOv) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 3 (-1) false true ])
  expectExitOk "qdivmod(minInt257,-1)" exitCodeOv
  assert (stOv.stack.size == 2) s!"qdivmod(minInt257,-1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]!, stOv.stack[1]! with
  | .int .nan, .int (.num r) =>
      assert (r == 0) s!"qdivmod(minInt257,-1): expected r=0, got {r}"
  | a, b =>
      throw (IO.userError s!"qdivmod(minInt257,-1): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qdivmod" testQdivmod
  Tests.registerRoundtrip (.divMod 3 (-1) false true)
