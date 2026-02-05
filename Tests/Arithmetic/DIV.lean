-- Auto-generated stub for TVM instruction DIV (category: arithmetic).
import Tests.Registry

open TvmLean Tests

private def pow2 (n : Nat) : Int :=
  Int.ofNat (Nat.shiftLeft 1 n)

private def minInt257 : Int :=
  -pow2 256

def testDiv : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num (-7)), .pushInt (.num 3), .divMod 1 (-1) false false ])
  expectExitOk "div(-7,3)" exitCode1
  assert (st1.stack.size == 1) s!"div(-7,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == -3) s!"div(-7,3): expected -3, got {n}"
  | v => throw (IO.userError s!"div(-7,3): unexpected stack value {v.pretty}")

  let (exitCode2, st2) ←
    expectHalt (← runProg [ .pushInt (.num 7), .pushInt (.num (-3)), .divMod 1 (-1) false false ])
  expectExitOk "div(7,-3)" exitCode2
  assert (st2.stack.size == 1) s!"div(7,-3): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == -3) s!"div(7,-3): expected -3, got {n}"
  | v => throw (IO.userError s!"div(7,-3): unexpected stack value {v.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 1 (-1) false false ])
  expectExitOk "div(1,0)" exitCodeZ
  assert (stZ.stack.size == 1) s!"div(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"div(1,0): expected NaN, got {v.pretty}")

  let (exitCodeNan, stNan) ←
    expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 3), .divMod 1 (-1) false false ])
  expectExitOk "div(nan,3)" exitCodeNan
  assert (stNan.stack.size == 1) s!"div(nan,3): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int .nan => pure ()
  | v => throw (IO.userError s!"div(nan,3): expected NaN, got {v.pretty}")

  -- The only in-range division overflow case: MIN_INT / -1.
  let (exitCodeOv, _) ←
    expectHalt (← runProg [ .pushInt (.num minInt257), .pushInt (.num (-1)), .divMod 1 (-1) false false ])
  expectExitExc "div(minInt257,-1)" .intOv exitCodeOv

initialize
  Tests.registerTest "arith/div" testDiv
  Tests.registerRoundtrip (.divMod 1 (-1) false false)
