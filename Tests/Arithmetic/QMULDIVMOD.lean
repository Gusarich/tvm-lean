-- Auto-generated stub for TVM instruction QMULDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def bigMulA : Int :=
  pow2 200

private def bigMulB : Int :=
  pow2 100

def testQmuldivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 3 (-1) false true ])
  expectExitOk "qmuldivmod(5,4,3)" exitCode1
  assert (st1.stack.size == 2) s!"qmuldivmod(5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 6) s!"qmuldivmod(5,4,3): expected q=6, got {q}"
      assert (r == 2) s!"qmuldivmod(5,4,3): expected r=2, got {r}"
  | a, b =>
      throw (IO.userError s!"qmuldivmod(5,4,3): unexpected stack values {a.pretty}, {b.pretty}")

  -- quotient overflows, remainder fits
  let (exitCodeOv, stOv) ←
    expectHalt (← runProg [ .pushInt (.num bigMulA), .pushInt (.num bigMulB), .pushInt (.num 1), .mulDivMod 3 (-1) false true ])
  expectExitOk "qmuldivmod(2^200,2^100,1)" exitCodeOv
  assert (stOv.stack.size == 2) s!"qmuldivmod(2^200,2^100,1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]!, stOv.stack[1]! with
  | .int .nan, .int (.num r) =>
      assert (r == 0) s!"qmuldivmod(2^200,2^100,1): expected r=0, got {r}"
  | a, b =>
      throw (IO.userError s!"qmuldivmod(2^200,2^100,1): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qmuldivmod" testQmuldivmod
  Tests.registerRoundtrip (.mulDivMod 3 (-1) false true)
