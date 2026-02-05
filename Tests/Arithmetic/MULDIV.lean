-- Auto-generated stub for TVM instruction MULDIV (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def bigMulA : Int :=
  pow2 200

private def bigMulB : Int :=
  pow2 100

def testMuldiv : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-5)), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 1 (-1) false false ])
  expectExitOk "muldiv(-5,4,3)" exitCode1
  assert (st1.stack.size == 1) s!"muldiv(-5,4,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -7) s!"muldiv(-5,4,3): expected -7, got {n}"
  | v => throw (IO.userError s!"muldiv(-5,4,3): unexpected stack value {v.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 3), .mulDivMod 1 (-1) false false ])
  expectExitOk "muldiv(5,4,3)" exitCode2
  assert (st2.stack.size == 1) s!"muldiv(5,4,3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == 6) s!"muldiv(5,4,3): expected 6, got {n}"
  | v => throw (IO.userError s!"muldiv(5,4,3): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 5), .pushInt (.num 4), .pushInt (.num 0), .mulDivMod 1 (-1) false false ])
  expectExitOk "muldiv(5,4,0)" exitCodeZ
  assert (stZ.stack.size == 1) s!"muldiv(5,4,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"muldiv(5,4,0): expected NaN, got {v.pretty}")

  let (exitCodeOv, _) ←
    expectHalt (← runProg [ .pushInt (.num bigMulA), .pushInt (.num bigMulB), .pushInt (.num 1), .mulDivMod 1 (-1) false false ])
  expectExitExc "muldiv(2^200,2^100,1)" .intOv exitCodeOv

initialize
  Tests.registerTest "arith/muldiv" testMuldiv
  Tests.registerRoundtrip (.mulDivMod 1 (-1) false false)
