-- Auto-generated stub for TVM instruction IFNOTRET (category: continuation).
import Tests.Registry

open TvmLean Tests

def testIfNotRet : IO Unit := do
  -- IFNOTRET returns when flag is false (0); the following PUSHINT must not execute.
  let prog : List Instr := [ .pushInt (.num 0), .ifnotret, .pushInt (.num 99) ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "ifnotret: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"ifnotret: unexpected exitCode={exitCode}"
      assert (st.stack.size == 0) s!"ifnotret: expected empty stack, got {Stack.pretty st.stack}"

initialize
  Tests.registerTest "cont/ifnotret" testIfNotRet
  Tests.registerRoundtrip (.ifnotret)
