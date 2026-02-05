-- Auto-generated stub for TVM instruction SDATASIZEQ (category: misc).
import Tests.Registry

open TvmLean Tests

def runSdataSizeQInstr (i : Instr) (stack : Stack) (fuel : Nat := 50) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def testSdataSizeQ : IO Unit := do
  let child : Cell := cellOfBytes #[0x01]
  let base : Cell := Cell.mkOrdinary (natToBits 0xabcd 16) #[child]
  let slice : Slice := Slice.ofCell base

  -- Success: pushes x y z -1.
  let (code0, st0) ← runSdataSizeQInstr (.cellExt (.sdataSize true)) #[.slice slice, .int (.num 10)]
  assert (code0 == -1) s!"sdatasizeq: unexpected exitCode={code0}"
  assert (st0.stack.size == 4) s!"sdatasizeq: unexpected stack size={st0.stack.size}"
  match st0.stack[0]!, st0.stack[1]!, st0.stack[2]!, st0.stack[3]! with
  | .int (.num x), .int (.num y), .int (.num z), .int (.num status) =>
      assert (x == 1) s!"sdatasizeq: expected x=1, got {x}"
      assert (y == 24) s!"sdatasizeq: expected y=24, got {y}"
      assert (z == 1) s!"sdatasizeq: expected z=1, got {z}"
      assert (status == -1) s!"sdatasizeq: expected status=-1, got {status}"
  | a, b, c, d =>
      throw (IO.userError s!"sdatasizeq: unexpected stack values {a.pretty}, {b.pretty}, {c.pretty}, {d.pretty}")

  -- Overflow: returns 0 (quiet) instead of throwing.
  let (code1, st1) ← runSdataSizeQInstr (.cellExt (.sdataSize true)) #[.slice slice, .int (.num 0)]
  assert (code1 == -1) s!"sdatasizeq(ov): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"sdatasizeq(ov): unexpected stack size={st1.stack.size}"
  match st1.stack[0]! with
  | .int (.num n) => assert (n == 0) s!"sdatasizeq(ov): expected 0, got {n}"
  | v => throw (IO.userError s!"sdatasizeq(ov): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "misc/sdatasizeq" testSdataSizeQ
  Tests.registerRoundtrip (.cellExt (.sdataSize true))
