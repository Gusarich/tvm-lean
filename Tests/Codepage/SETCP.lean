-- Auto-generated stub for TVM instruction SETCP (category: codepage).
import Tests.Registry

open TvmLean Tests

def testSetCp : IO Unit := do
  -- SETCP 1 is unsupported in our MVP and must raise inv_opcode (6), i.e. exit ~6 = -7.
  let prog : List Instr := [ .setcp 1 ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "setcp: did not halt")
  | .halt exitCode _ =>
      assert (exitCode == -7) s!"setcp: expected exitCode=-7, got {exitCode}"

initialize
  Tests.registerTest "codepage/setcp" testSetCp
  Tests.registerRoundtrip (.setcp 0)
