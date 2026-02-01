-- Auto-generated stub for TVM instruction ABS (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testAbs : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num (-7)), .abs false ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "abs(-7): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"abs(-7): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"abs(-7): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 7) s!"abs(-7): expected 7, got {n}"
      | v => throw (IO.userError s!"abs(-7): unexpected stack value {v.pretty}")

  let overflowVal : Int := -intPow2 256
  let progOverflow : List Instr := [ .pushInt (.num overflowVal), .abs false ]
  match (← runProg progOverflow) with
  | .continue _ => throw (IO.userError "abs(overflow): did not halt")
  | .halt exitCode _ =>
      assert (exitCode == -5) s!"abs(overflow): expected exitCode=-5, got {exitCode}"

  let progQabs : List Instr := [ .pushInt (.num overflowVal), .abs true ]
  match (← runProg progQabs) with
  | .continue _ => throw (IO.userError "qabs(overflow): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"qabs(overflow): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"qabs(overflow): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int .nan => pure ()
      | v => throw (IO.userError s!"qabs(overflow): unexpected stack value {v.pretty}")

initialize
  Tests.registerTest "arith/abs" testAbs
  Tests.registerRoundtrip (.abs false)
  Tests.registerRoundtrip (.abs true)
