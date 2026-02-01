-- Auto-generated stub for TVM instruction ABS (category: arithmetic).
import Tests.Registry

open TvmLean Tests

def testAbs : IO Unit := do
  let progPos : List Instr := [ .pushInt (.num 7), .abs false ]
  match (← runProg progPos) with
  | .continue _ => throw (IO.userError "abs(pos): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"abs(pos): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"abs(pos): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 7) s!"abs(pos): expected 7, got {n}"
      | v => throw (IO.userError s!"abs(pos): unexpected stack value {v.pretty}")

  let progNeg : List Instr := [ .pushInt (.num (-13)), .abs false ]
  match (← runProg progNeg) with
  | .continue _ => throw (IO.userError "abs(neg): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"abs(neg): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"abs(neg): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int (.num n) => assert (n == 13) s!"abs(neg): expected 13, got {n}"
      | v => throw (IO.userError s!"abs(neg): unexpected stack value {v.pretty}")

  let overflow : Int := -intPow2 256
  let progOverflow : List Instr := [ .pushInt (.num overflow), .abs false ]
  match (← runProg progOverflow) with
  | .continue _ => throw (IO.userError "abs(overflow): did not halt")
  | .halt exitCode _ =>
      assert (exitCode == -5) s!"abs(overflow): expected exitCode=-5, got {exitCode}"

  let progQuiet : List Instr := [ .pushInt (.num overflow), .abs true ]
  match (← runProg progQuiet) with
  | .continue _ => throw (IO.userError "qabs(overflow): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"qabs(overflow): unexpected exitCode={exitCode}"
      assert (st.stack.size == 1) s!"qabs(overflow): unexpected stack size={st.stack.size}"
      match st.stack[0]! with
      | .int .nan => pure ()
      | v => throw (IO.userError s!"qabs(overflow): expected NaN, got {v.pretty}")

initialize
  Tests.registerTest "arith/abs" testAbs
  Tests.registerRoundtrip (.abs false)
  Tests.registerRoundtrip (.abs true)
