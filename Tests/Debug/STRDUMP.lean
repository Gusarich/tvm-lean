-- Auto-generated stub for TVM instruction STRDUMP (category: debug).
import Tests.Registry

open TvmLean Tests

def testStrDump : IO Unit := do
  let prog : List Instr := [(.debugOp .strDump)]
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")

  let runCase (ctx : String) (stack0 : Stack) (check : VmState → IO Unit) : IO Unit := do
    let st0 : VmState := { VmState.initial codeCell with stack := stack0 }
    match VmState.run 20 st0 with
    | .continue _ => throw (IO.userError s!"{ctx}: did not halt")
    | .halt exitCode st =>
        expectExitOk ctx exitCode
        check st

  let bs : Array UInt8 := #[0x68, 0x69] -- "hi"
  let slice : Slice := Slice.ofCell (cellOfBytes bs)
  runCase "strdump(slice)" #[.slice slice] fun st => do
    assert (st.stack.size == 1) s!"strdump: unexpected stack size={st.stack.size}"
    match st.stack[0]! with
    | .slice s =>
        assert (s.bitPos == slice.bitPos) "strdump: unexpected bitPos"
        assert (s.refPos == slice.refPos) "strdump: unexpected refPos"
        assert (s.cell == slice.cell) "strdump: unexpected slice contents"
    | v => throw (IO.userError s!"strdump: unexpected stack value {v.pretty}")

  -- STRDUMP is a pure debug opcode: it must never throw on missing/ill-typed s0.
  runCase "strdump(empty)" #[] fun st => do
    assert (st.stack.isEmpty) s!"strdump: expected empty stack, got size={st.stack.size}"

  runCase "strdump(type)" #[.int (.num 123)] fun st => do
    assert (st.stack.size == 1) s!"strdump: unexpected stack size={st.stack.size}"
    match st.stack[0]! with
    | .int (.num n) => assert (n == 123) s!"strdump: expected 123, got {n}"
    | v => throw (IO.userError s!"strdump: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "debug/strdump" testStrDump
  Tests.registerRoundtrip (.debugOp .strDump)
