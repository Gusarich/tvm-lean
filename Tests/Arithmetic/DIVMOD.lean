-- Auto-generated stub for TVM instruction DIVMOD (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testDivmod : IO Unit := do
  let (exitCode1, st1) ←
    expectHalt (← runProg [ .pushInt (.num 8), .pushInt (.num 3), .divMod 3 (-1) false false ])
  expectExitOk "divmod(8,3)" exitCode1
  assert (st1.stack.size == 2) s!"divmod(8,3): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]! with
  | .int (.num q), .int (.num r) =>
      assert (q == 2) s!"divmod(8,3): expected q=2, got {q}"
      assert (r == 2) s!"divmod(8,3): expected r=2, got {r}"
  | a, b =>
      throw (IO.userError s!"divmod(8,3): unexpected stack values {a.pretty}, {b.pretty}")

  let (exitCodeZ, stZ) ←
    expectHalt (← runProg [ .pushInt (.num 1), .pushInt (.num 0), .divMod 3 (-1) false false ])
  -- DIVMOD is non-quiet: division by zero yields NaN results internally, then `push_int_quiet` raises int overflow.
  expectExitExc "divmod(1,0)" .intOv exitCodeZ
  assert (stZ.stack.size == 1) s!"divmod(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"divmod(1,0): expected 0, got {n}"
  | v => throw (IO.userError s!"divmod(1,0): expected 0, got {v.pretty}")

  let (exitCodeNan, stNan) ←
    expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 3), .divMod 3 (-1) false false ])
  -- DIVMOD is non-quiet: NaN inputs propagate and trigger int overflow on the first push.
  expectExitExc "divmod(nan,3)" .intOv exitCodeNan
  assert (stNan.stack.size == 1) s!"divmod(nan,3): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"divmod(nan,3): expected 0, got {n}"
  | v => throw (IO.userError s!"divmod(nan,3): expected 0, got {v.pretty}")

initialize
  Tests.registerTest "arith/divmod" testDivmod
  Tests.registerRoundtrip (.divMod 3 (-1) false false)
