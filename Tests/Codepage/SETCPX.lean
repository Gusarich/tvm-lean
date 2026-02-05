-- Auto-generated stub for TVM instruction SETCPX (category: codepage).
import Tests.Registry

open TvmLean Tests

def testSetCpX : IO Unit := do
  -- SETCPX pops a smallint-range cp and selects that codepage.
  -- TON supports only cp=0 (cp0); other in-range values raise invOpcode.
  let progOk : List Instr := [ .pushInt (.num 0), .setcpX ]
  match (← runProg progOk) with
  | .continue _ => throw (IO.userError "setcpx(ok): did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"setcpx(ok): unexpected exitCode={exitCode}"
      assert (st.cp == 0) s!"setcpx(ok): expected cp=0, got cp={st.cp}"
      assert (st.stack.isEmpty) s!"setcpx(ok): expected empty stack, got size={st.stack.size}"

  let progBad : List Instr := [ .pushInt (.num 1), .setcpX ]
  match (← runProg progBad) with
  | .continue _ => throw (IO.userError "setcpx(bad): did not halt")
  | .halt exitCode _ =>
      assert (exitCode == (~~~ Excno.invOpcode.toInt)) s!"setcpx(bad): expected invOpcode, got exitCode={exitCode}"

  let progRange : List Instr := [ .pushInt (.num 40000), .setcpX ]
  match (← runProg progRange) with
  | .continue _ => throw (IO.userError "setcpx(range): did not halt")
  | .halt exitCode _ =>
      assert (exitCode == (~~~ Excno.rangeChk.toInt)) s!"setcpx(range): expected rangeChk, got exitCode={exitCode}"

initialize
  Tests.registerTest "codepage/setcpx" testSetCpX
  Tests.registerRoundtrip .setcpX
