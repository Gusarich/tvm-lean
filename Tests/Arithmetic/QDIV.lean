-- Auto-generated stub for TVM instruction QDIV (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testQdiv : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 1 (-1) false true ])
  expectExitOk "qdiv(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"qdiv(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -3) s!"qdiv(-7,3): expected -3, got {n}"
  | v => throw (IO.userError s!"qdiv(-7,3): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 1 (-1) false true ])
  expectExitOk "qdiv(1,0)" exitCodeZ
  assert (stZ.stack.size == 1) s!"qdiv(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qdiv(1,0): expected NaN, got {v.pretty}")

  let (exitCodeOv, stOv) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 1 (-1) false true ])
  expectExitOk "qdiv(minInt257,-1)" exitCodeOv
  assert (stOv.stack.size == 1) s!"qdiv(minInt257,-1): unexpected stack size={stOv.stack.size}"
  match stOv.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"qdiv(minInt257,-1): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/qdiv" testQdiv
  Tests.registerRoundtrip (.divMod 1 (-1) false true)
