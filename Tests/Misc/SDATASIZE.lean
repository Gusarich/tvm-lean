-- Auto-generated stub for TVM instruction SDATASIZE (category: misc).
import Tests.Registry

open TvmLean Tests

def runSdataSizeInstr (i : Instr) (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testSdataSize : IO Unit := do
  let child : Cell := cellOfBytes #[0x01]
  let base : Cell := Cell.mkOrdinary (natToBits 0xabcd 16) #[child]
  let slice : Slice := Slice.ofCell base

  -- Success: x excludes the slice's own cell; y and z include the slice view itself.
  let (code0, st0) ← runSdataSizeInstr (.cellExt (.sdataSize false)) #[.slice slice, .int (.num 10)]
  assert (code0 == -1) s!"sdatasize: unexpected exitCode={code0}"
  assert (st0.stack.size == 3) s!"sdatasize: unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]!, st0.stack[2]! with
  | .int (.num x), .int (.num y), .int (.num z) =>
      assert (x == 1) s!"sdatasize: expected x=1, got {x}"
      assert (y == 24) s!"sdatasize: expected y=24, got {y}"
      assert (z == 1) s!"sdatasize: expected z=1, got {z}"
  | a, b, c => throw (IO.userError s!"sdatasize: unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}")

  -- Overflow: throws cellOv (8) if more than `n` distinct cells would be visited.
  let (code1, _st1) ← runSdataSizeInstr (.cellExt (.sdataSize false)) #[.slice slice, .int (.num 0)]
  assert (code1 == (~~~ Excno.cellOv.toInt)) s!"sdatasize(ov): expected cellOv, got exitCode={code1}"

initialize
  Tests.registerTest "misc/sdatasize" testSdataSize
  Tests.registerRoundtrip (.cellExt (.sdataSize false))
