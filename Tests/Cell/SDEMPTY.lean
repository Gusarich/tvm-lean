-- Auto-generated stub for TVM instruction SDEMPTY (category: cell).
import Tests.Registry

open TvmLean Tests

def runUnarySliceInstr (instr : Instr) (slice : Slice) (fuel : Nat := 20) : IO Int := do
  let prog : List Instr := [instr]
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let st0 : VmState := { VmState.initial codeCell with stack := #[.slice slice] }
  match VmState.run fuel st0 with
  | .continue _ =>
      throw (IO.userError s!"{instr.pretty}: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"{instr.pretty}: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"{instr.pretty}: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => pure n
      | v => throw (IO.userError s!"{instr.pretty}: unexpected stack value {v.pretty}")

def testSliceEmptyChecks : IO Unit := do
  let emptyBits : BitString := #[]
  let oneBit := natToBits 1 1
  let emptyCell : Cell := Cell.mkOrdinary emptyBits #[]
  let refsCell : Cell := Cell.mkOrdinary emptyBits #[Cell.ofUInt 1 1]
  let bitsCell : Cell := Cell.mkOrdinary oneBit #[]
  let sliceEmpty := Slice.ofCell emptyCell
  let sliceRefs := Slice.ofCell refsCell
  let sliceBits := Slice.ofCell bitsCell

  assert ((← runUnarySliceInstr .sdempty sliceEmpty) == -1) "sdempty: expected empty slice -> -1"
  assert ((← runUnarySliceInstr .sdempty sliceRefs) == -1) "sdempty: expected refs-only slice -> -1"
  assert ((← runUnarySliceInstr .sdempty sliceBits) == 0) "sdempty: expected data slice -> 0"

  assert ((← runUnarySliceInstr .sempty sliceEmpty) == -1) "sempty: expected empty slice -> -1"
  assert ((← runUnarySliceInstr .sempty sliceRefs) == 0) "sempty: expected refs-only slice -> 0"
  assert ((← runUnarySliceInstr .sempty sliceBits) == 0) "sempty: expected data slice -> 0"

  assert ((← runUnarySliceInstr .srempty sliceEmpty) == -1) "srempty: expected empty slice -> -1"
  assert ((← runUnarySliceInstr .srempty sliceRefs) == 0) "srempty: expected refs-only slice -> 0"
  assert ((← runUnarySliceInstr .srempty sliceBits) == -1) "srempty: expected data-only slice -> -1"

initialize
  Tests.registerTest "cell/slice_empty_checks" testSliceEmptyChecks
  Tests.registerRoundtrip (.sdempty)
  Tests.registerRoundtrip (.sempty)
  Tests.registerRoundtrip (.srempty)
