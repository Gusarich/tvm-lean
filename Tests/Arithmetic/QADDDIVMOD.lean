-- Auto-generated stub for TVM instruction QADDDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testQadddivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .pushInt (.num 2), .divMod 3 (-1) true true ])
  expectExitOk "qadddivmod(1,0,2)" exitCode1
  assert (st1.stack.size == 2) s!"qadddivmod(1,0,2): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 0) s!"qadddivmod(1,0,2): expected q=0, got {q}"
      assert (r == 1) s!"qadddivmod(1,0,2): expected r=1, got {r}"
  | a, b =>
      throw (IO.userError s!"qadddivmod(1,0,2): unexpected stack values {a.pretty}, {b.pretty}")

  -- overflow is quiet (quotient becomes NaN, remainder still computed): MIN_INT / -1.
  let (exitCodeOv, stOv) ←
    expectHalt
      (← runProg [ .pushInt (.num minInt257), .pushInt (.num 0), .pushInt (.num (-1)), .divMod 3 (-1) true true ])
  expectExitOk "qadddivmod(minInt257,0,-1)" exitCodeOv
  assert (stOv.stack.size == 2) s!"qadddivmod(minInt257,0,-1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]!, stOv.stack[1]! with
  | .int .nan, .int (.num r) =>
      assert (r == 0) s!"qadddivmod(minInt257,0,-1): expected r=0, got {r}"
  | a, b =>
      throw (IO.userError s!"qadddivmod(minInt257,0,-1): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qadddivmod" testQadddivmod
  Tests.registerRoundtrip (.divMod 3 (-1) true true)
