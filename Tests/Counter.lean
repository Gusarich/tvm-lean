import Tests.Registry

open TvmLean Tests

def testCounter : IO Unit := do
  let prog : List Instr :=
    [ .pushCtr 4
    , .ctos
    , .ldu 32
    , .ends
    , .inc
    , .newc
    , .stu 32
    , .endc
    , .popCtr 4
    ]
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let initC4 : Cell := Cell.ofUInt 32 41
  let base := VmState.initial codeCell
  let st0 : VmState := { base with regs := { base.regs with c4 := initC4 } }
  match VmState.run 200 st0 with
  | .continue _ =>
      throw (IO.userError "counter: did not halt (fuel exhausted?)")
  | .halt exitCode st =>
      assert (exitCode == -1) s!"counter: unexpected exitCode={exitCode}"
      assert (bitsToNat st.regs.c4.bits == 42) s!"counter: unexpected c4={bitsToNat st.regs.c4.bits}"

initialize
  Tests.registerTest "counter" testCounter
