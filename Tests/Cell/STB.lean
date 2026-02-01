-- Auto-generated stub for TVM instruction STB (category: cell).
import Tests.Registry

open TvmLean Tests

def testStb : IO Unit := do
  let prog : List Instr :=
    [ .pushInt (.num 0xAA)
    , .newc
    , .stu 8
    , .pushInt (.num 0xBB)
    , .newc
    , .stu 8
    , .xchg0 1
    , .stb false false
    , .endc
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stb: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stb: unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"stb: unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .cell c =>
          assert (c.bits.size == 16) s!"stb: expected 16 bits, got {c.bits.size}"
          assert (bitsToNat c.bits == 0xAABB) s!"stb: expected 0xAABB, got {bitsToNat c.bits}"
          assert (c.refs.size == 0) s!"stb: expected 0 refs, got {c.refs.size}"
      | v => throw (IO.userError s!"stb: unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "cell/stb" testStb
  Tests.registerRoundtrip (.stb false false)
