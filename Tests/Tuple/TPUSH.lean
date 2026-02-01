-- Auto-generated stub for TVM instruction TPUSH (category: tuple).
import Tests.Registry

open TvmLean Tests

def testTuplePush : IO Unit := do
  let prog : List Instr :=
    [ .pushInt (.num 1)
    , .pushInt (.num 2)
    , .tupleOp (.mktuple 2)
    , .pushInt (.num 3)
    , .tupleOp .tpush
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "tpush: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"tpush: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"tpush: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .tuple items =>
          assert (items.size == 3) s!"tpush: expected tuple size=3, got {items.size}"
          match items[0]!, items[1]!, items[2]! with
          | .int (.num a), .int (.num b), .int (.num c) =>
              assert (a == 1 ∧ b == 2 ∧ c == 3) s!"tpush: expected [1,2,3], got {items.map (·.pretty)}"
          | _, _, _ =>
              throw (IO.userError s!"tpush: unexpected tuple contents {items.map (·.pretty)}")
      | v =>
          throw (IO.userError s!"tpush: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "tuple/tpush" testTuplePush
  Tests.registerRoundtrip (.tupleOp .tpush)
