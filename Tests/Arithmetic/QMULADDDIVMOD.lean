-- Auto-generated stub for TVM instruction QMULADDDIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def bigMulA : Int :=
  pow2 200

private def bigMulB : Int :=
  pow2 100

def testQmuladddivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt
      (← runProg
        [ .pushInt (.num 2), .pushInt (.num 3), .pushInt (.num 1), .pushInt (.num 2)
        , .mulDivMod 3 (-1) true true
        ])
  expectExitOk "qmuladddivmod(2,3,1,2)" exitCode1
  assert (st1.stack.size == 2) s!"qmuladddivmod(2,3,1,2): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 3) s!"qmuladddivmod(2,3,1,2): expected q=3, got {q}"
      assert (r == 1) s!"qmuladddivmod(2,3,1,2): expected r=1, got {r}"
  | a, b =>
      throw (IO.userError s!"qmuladddivmod(2,3,1,2): unexpected stack values {a.pretty}, {b.pretty}")

  let (exitCodeOv, stOv) ←
    expectHalt
      (← runProg
        [ .pushInt (.num bigMulA), .pushInt (.num bigMulB), .pushInt (.num 0), .pushInt (.num 1)
        , .mulDivMod 3 (-1) true true
        ])
  expectExitOk "qmuladddivmod(2^200,2^100,0,1)" exitCodeOv
  assert (stOv.stack.size == 2) s!"qmuladddivmod(2^200,2^100,0,1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]!, stOv.stack[1]! with
  | .int .nan, .int (.num r) =>
      assert (r == 0) s!"qmuladddivmod(2^200,2^100,0,1): expected r=0, got {r}"
  | a, b =>
      throw (IO.userError s!"qmuladddivmod(2^200,2^100,0,1): unexpected stack values {a.pretty}, {b.pretty}")

initialize
  Tests.registerTest "arith/qmuladddivmod" testQmuladddivmod
  Tests.registerRoundtrip (.mulDivMod 3 (-1) true true)
