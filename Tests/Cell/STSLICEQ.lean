-- Auto-generated stub for TVM instruction STSLICEQ (category: cell).
import Tests.Registry

open TvmLean Tests

def testStSliceQ : IO Unit := do
  let slice := Slice.ofCell (Cell.ofUInt 8 0xab)
  let prog : List Instr := [ .pushSliceConst slice, .newc, .stSlice false true ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stsliceq: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stsliceq: unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"stsliceq: unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .builder b, .int (.num status) =>
          assert (status == 0) s!"stsliceq: expected status=0, got {status}"
          assert (b.bits == natToBits 0xab 8) s!"stsliceq: unexpected builder bits"
          assert (b.refs.size == 0) s!"stsliceq: unexpected builder refs={b.refs.size}"
      | v0, v1 =>
          throw (IO.userError s!"stsliceq: unexpected stack values {v0.pretty}, {v1.pretty}")

initialize
  Tests.registerTest "cell/stsliceq" testStSliceQ
  Tests.registerRoundtrip (.stSlice false true)
