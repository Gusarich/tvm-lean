-- Auto-generated stub for TVM instruction CDATASIZEQ (category: misc).
import Tests.Registry

open TvmLean Tests

def runCdataSizeQInstr (i : Instr) (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testCdataSizeQ : IO Unit := do
  let child1 : Cell := cellOfBytes #[0x01]
  let child2 : Cell := cellOfBytes #[0x01]
  let root : Cell := Cell.mkOrdinary #[] #[child1, child2]

  -- Success: pushes x y z -1.
  let (code0, st0) ← runCdataSizeQInstr (.cellExt (.cdataSize true)) #[.cell root, .int (.num 10)]
  assert (code0 == -1) s!"cdatasizeq: unexpected exitCode={code0}"
  assert (st0.stack.size == 4) s!"cdatasizeq: unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]!, st0.stack[2]!, st0.stack[3]! with
  | .int (.num x), .int (.num y), .int (.num z), .int (.num status) =>
      assert (x == 2) s!"cdatasizeq: expected x=2, got {x}"
      assert (y == 8) s!"cdatasizeq: expected y=8, got {y}"
      assert (z == 2) s!"cdatasizeq: expected z=2, got {z}"
      assert (status == -1) s!"cdatasizeq: expected status=-1, got {status}"
  | a, b, c, d =>
      throw (IO.userError s!"cdatasizeq: unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}, {d.pretty}")

  -- Null cell: succeeds with 0 0 0 -1.
  let (code1, st1) ← runCdataSizeQInstr (.cellExt (.cdataSize true)) #[.null, .int (.num 0)]
  assert (code1 == -1) s!"cdatasizeq(null): unexpected exitCode={code1}"
  assert (st1.stack.size == 4) s!"cdatasizeq(null): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]!, st1.stack[2]!, st1.stack[3]! with
  | .int (.num x), .int (.num y), .int (.num z), .int (.num status) =>
      assert (x == 0) s!"cdatasizeq(null): expected x=0, got {x}"
      assert (y == 0) s!"cdatasizeq(null): expected y=0, got {y}"
      assert (z == 0) s!"cdatasizeq(null): expected z=0, got {z}"
      assert (status == -1) s!"cdatasizeq(null): expected status=-1, got {status}"
  | a, b, c, d =>
      throw (IO.userError s!"cdatasizeq(null): unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}, {d.pretty}")

  -- Overflow: returns 0 (quiet) instead of throwing.
  let root2 : Cell := Cell.mkOrdinary #[] #[cellOfBytes #[0x02]]
  let (code2, st2) ← runCdataSizeQInstr (.cellExt (.cdataSize true)) #[.cell root2, .int (.num 1)]
  assert (code2 == -1) s!"cdatasizeq(ov): unexpected exitCode={code2}"
  assert (st2.stack.size == 1) s!"cdatasizeq(ov): unexpected stack size={st2.stack.size}"
  match st2.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"cdatasizeq(ov): expected 0, got {n}"
  | v => throw (IO.userError s!"cdatasizeq(ov): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "misc/cdatasizeq" testCdataSizeQ
  Tests.registerRoundtrip (.cellExt (.cdataSize true))
