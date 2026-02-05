-- Auto-generated stub for TVM instruction SETCP (category: codepage).
import Tests.Registry

open TvmLean Tests

def testSetCp : IO Unit := do
  -- SETCP 1 is unsupported in TON (only cp0 exists) and must raise inv_opcode (6).
  let prog : List Instr := [ .setcp 1 ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "setcp: did not halt")
  | .halt exitCode _ =>
      assert (exitCode == (~~~ Excno.invOpcode.toInt)) s!"setcp: expected invOpcode, got exitCode={exitCode}"

initialize
  Tests.registerTest "codepage/setcp" testSetCp
  Tests.registerRoundtrip (.setcp 0)
  Tests.registerRoundtrip (.setcp (-1))
  Tests.registerRoundtrip (.setcp 239)
