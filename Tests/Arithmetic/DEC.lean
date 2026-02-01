-- Auto-generated stub for TVM instruction DEC (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testDec : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 10), .dec ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "dec(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"dec(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"dec(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 9) s!"dec(pos): expected 9, got {n}"
      | v => throw (IO.userError s!"dec(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-1)), .dec ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "dec(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"dec(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"dec(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == -2) s!"dec(neg): expected -2, got {n}"
      | v => throw (IO.userError s!"dec(neg): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/dec" testDec
  Tests.registerRoundtrip (.dec)
