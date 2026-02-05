-- Auto-generated stub for TVM instruction DUMP (category: debug).
import Tests.Registry

open TvmLean Tests

def testDump : IO Unit := do
  let runCase (idx : Nat) (stack0 : Stack) (check : VmState → IO Unit) : IO Unit := do
    let prog : List Instr := [(.debugOp (.dump idx))]
    let codeCell ←
      match assembleCp0 prog with
      | .ok c => pure c
      | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
    let st0 : VmState := { VmState.initial codeCell with stack := stack0 }
    match VmState.run 20 st0 with
    | .continue _ => throw (IO.userError s!"dump({idx}): did not halt")
    | .halt exitCode st =>
        expectExitOk s!"dump({idx})" exitCode
        check st

  runCase 1 #[.int (.num 5), .int (.num 7)] fun st => do
    assert (st.stack.size == 2) s!"dump: unexpected stack size={st.stack.size}"
    match st.stack[0]!, st.stack[1]! with
    | .int (.num a), .int (.num b) =>
        assert (a == 5) s!"dump: expected 5 at depth 1, got {a}"
        assert (b == 7) s!"dump: expected 7 on top, got {b}"
    | v0, v1 =>
        throw (IO.userError s!"dump: unexpected stack values {v0.pretty}, {v1.pretty}")

  -- DUMP is a pure debug opcode: it must never throw on missing stack entries.
  runCase 0 #[] fun st => do
    assert (st.stack.isEmpty) s!"dump: expected empty stack, got size={st.stack.size}"

  runCase 3 #[.int (.num 42)] fun st => do
    assert (st.stack.size == 1) s!"dump: unexpected stack size={st.stack.size}"
    match st.stack[0]! with
    | .int (.num n) => assert (n == 42) s!"dump: expected 42, got {n}"
    | v => throw (IO.userError s!"dump: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "debug/dump" testDump
  Tests.registerRoundtrip (.debugOp (.dump 0))
