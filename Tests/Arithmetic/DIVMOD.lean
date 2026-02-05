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
  expectExitOk "divmod(1,0)" exitCodeZ
  assert (stZ.stack.size == 2) s!"divmod(1,0): unexpected stack size={stZ.stack.size}"
  match stZ.stack[0]!, stZ.stack[1]! with
  | .int .nan, .int .nan => pure ()
  | a, b =>
      throw (IO.userError s!"divmod(1,0): expected NaN,NaN got {a.pretty},{b.pretty}")

  let (exitCodeNan, stNan) ←
    expectHalt (← runProg [ .pushInt .nan, .pushInt (.num 3), .divMod 3 (-1) false false ])
  expectExitOk "divmod(nan,3)" exitCodeNan
  assert (stNan.stack.size == 2) s!"divmod(nan,3): unexpected stack size={stNan.stack.size}"
  match stNan.stack[0]!, stNan.stack[1]! with
  | .int .nan, .int .nan => pure ()
  | a, b =>
      throw (IO.userError s!"divmod(nan,3): expected NaN,NaN got {a.pretty},{b.pretty}")

initialize
  Tests.registerTest "arith/divmod" testDivmod
  Tests.registerRoundtrip (.divMod 3 (-1) false false)
