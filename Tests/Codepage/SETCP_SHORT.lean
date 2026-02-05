-- Auto-generated stub for TVM instruction SETCP_SHORT (category: codepage).
import Tests.Registry

open TvmLean Tests

def testSetCpShort : IO Unit := do
  -- Short SETCP encodes negative codepages -15..-1 as 0xfff1..0xffff.
  let prog : List Instr := [ .setcp (-1) ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "setcp_short: did not halt")
  | .halt exitCode _ =>
      -- TON supports only cp=0; unsupported codepages raise inv_opcode.
      assert (exitCode == (~~~ Excno.invOpcode.toInt)) s!"setcp_short: expected invOpcode, got exitCode={exitCode}"

initialize
  -- Roundtrip ensures encode produces the short form and decode returns the same `setcp` value.
  Tests.registerTest "codepage/setcp_short" testSetCpShort
  Tests.registerRoundtrip (.setcp (-1))
  Tests.registerRoundtrip (.setcp (-15))
