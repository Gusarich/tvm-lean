-- Auto-generated stub for TVM instruction STBR (category: cell).
import Tests.Registry

open TvmLean Tests

def testStbr : IO Unit := do
  let prog : List Instr :=
    [ .pushInt (.num 1)
    , .newc
    , .stu 1
    , .pushInt (.num 0)
    , .newc
    , .stu 1
    , .stb true false
    , .endc
    , .ctos
    , .ldu 2
    ]
  match (← runProg prog) with
  | .continue _ => throw (IO.userError "stbr: did not halt")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"stbr: unexpected exitCode={exitCode}"
      assert (st.stack.size == 2) s!"stbr: unexpected stack size={st.stack.size}"
      match st.stack[0]!, st.stack[1]! with
      | .slice s, .int (.num n) =>
          assert (n == 2) s!"stbr: expected 2, got {n}"
          assert (s.bitsRemaining == 0) s!"stbr: expected empty slice, got bitsRemaining={s.bitsRemaining}"
      | v0, v1 =>
          throw (IO.userError s!"stbr: unexpected stack values {v0.pretty}, {v1.pretty}")

initialize
  Tests.registerTest "cell/stbr" testStbr
  Tests.registerRoundtrip (.stb true false)
