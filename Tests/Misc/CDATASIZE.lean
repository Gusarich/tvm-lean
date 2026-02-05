-- Auto-generated stub for TVM instruction CDATASIZE (category: misc).
import Tests.Registry

open TvmLean Tests

def runCdataSizeInstr (i : Instr) (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testCdataSize : IO Unit := do
  let child1 : Cell := cellOfBytes #[0x01]
  let child2 : Cell := cellOfBytes #[0x01]
  let root : Cell := Cell.mkOrdinary #[] #[child1, child2]

  -- Success: counts distinct cells, bits, refs.
  let (code0, st0) ← runCdataSizeInstr (.cellExt (.cdataSize false)) #[.cell root, .int (.num 10)]
  assert (code0 == -1) s!"cdatasize: unexpected exitCode={code0}"
  assert (st0.stack.size == 3) s!"cdatasize: unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]!, st0.stack[2]! with
  | .int (.num x), .int (.num y), .int (.num z) =>
      assert (x == 2) s!"cdatasize: expected x=2, got {x}"
      assert (y == 8) s!"cdatasize: expected y=8, got {y}"
      assert (z == 2) s!"cdatasize: expected z=2, got {z}"
  | a, b, c => throw (IO.userError s!"cdatasize: unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}")

  -- Null cell: always succeeds with zeros.
  let (code1, st1) ← runCdataSizeInstr (.cellExt (.cdataSize false)) #[.null, .int (.num 0)]
  assert (code1 == -1) s!"cdatasize(null): unexpected exitCode={code1}"
  assert (st1.stack.size == 3) s!"cdatasize(null): unexpected stack size={st1.stack.size}"
  match st1.stack[0]!, st1.stack[1]!, st1.stack[2]! with
  | .int (.num x), .int (.num y), .int (.num z) =>
      assert (x == 0) s!"cdatasize(null): expected x=0, got {x}"
      assert (y == 0) s!"cdatasize(null): expected y=0, got {y}"
      assert (z == 0) s!"cdatasize(null): expected z=0, got {z}"
  | a, b, c => throw (IO.userError s!"cdatasize(null): unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}")

  -- Overflow: throws cellOv (8) if more than `n` distinct cells would be visited.
  let root2 : Cell := Cell.mkOrdinary #[] #[cellOfBytes #[0x02]]
  let (code2, _st2) ← runCdataSizeInstr (.cellExt (.cdataSize false)) #[.cell root2, .int (.num 1)]
  assert (code2 == (~~~ Excno.cellOv.toInt)) s!"cdatasize(ov): expected cellOv, got exitCode={code2}"

initialize
  Tests.registerTest "misc/cdatasize" testCdataSize
  Tests.registerRoundtrip (.cellExt (.cdataSize false))
