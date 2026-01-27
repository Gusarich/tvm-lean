import TvmLean

def main : IO Unit := do
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
  match TvmLean.VmState.run 100 st0 with
  | .halt exitCode st => do
      IO.println s!"exitCode={exitCode}"
      IO.println s!"stack={TvmLean.Stack.pretty st.stack}"
      IO.println s!"c4(bits={st.regs.c4.bits.size})={TvmLean.bitsToNat st.regs.c4.bits}"
  | .continue _ => do
      IO.println "did not halt (fuel exhausted?)"
