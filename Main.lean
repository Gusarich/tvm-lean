import TvmLean

def runWithTrace (fuel : Nat) (st : TvmLean.VmState) : IO TvmLean.StepResult := do
  match fuel with
  | 0 =>
      pure (.halt (TvmLean.Excno.fatal.toInt) st)
  | fuel + 1 =>
      match st.cc with
      | .ordinary (i :: _) =>
          IO.println s!"gas={st.gas.gasRemaining} instr={reprStr i} stack={TvmLean.Stack.pretty st.stack}"
      | .ordinary [] =>
          IO.println s!"gas={st.gas.gasRemaining} instr=<implicit RET> stack={TvmLean.Stack.pretty st.stack}"
      | .quit n =>
          IO.println s!"gas={st.gas.gasRemaining} cont=<quit {n}> stack={TvmLean.Stack.pretty st.stack}"
      | .excQuit =>
          IO.println s!"gas={st.gas.gasRemaining} cont=<excQuit> stack={TvmLean.Stack.pretty st.stack}"
      let r := st.step
      match r with
      | .continue st' => runWithTrace fuel st'
      | .halt _ _ => pure r

def main (args : List String) : IO Unit := do
  let trace := args.any (fun a => a == "--trace")

  let prog : List TvmLean.Instr :=
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
  let initC4 : TvmLean.Cell := TvmLean.Cell.ofUInt 32 41
  let st0 : TvmLean.VmState :=
    { (TvmLean.VmState.initial prog) with regs := { (TvmLean.Regs.initial) with c4 := initC4 } }
  let res ←
    if trace then
      runWithTrace 100 st0
    else
      pure (TvmLean.VmState.run 100 st0)
  match res with
  | .halt exitCode st => do
      IO.println s!"exitCode={exitCode}"
      IO.println s!"stack={TvmLean.Stack.pretty st.stack}"
      IO.println s!"c4(bits={st.regs.c4.bits.size})={TvmLean.bitsToNat st.regs.c4.bits}"
  | .continue _ => do
      IO.println "did not halt (fuel exhausted?)"
