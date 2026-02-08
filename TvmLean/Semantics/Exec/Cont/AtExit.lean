import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def mkPushIntCont (n : Int) : Except Excno Continuation := do
  let bs ← encodeCp0 (.pushInt (.num n))
  let cell : Cell := Cell.mkOrdinary bs #[]
  let code : Slice := Slice.ofCell cell
  return .ordinary code (.quit 0) OrdCregs.empty OrdCdata.empty

set_option maxHeartbeats 1000000 in
def execInstrContAtExit (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt .atexit =>
      let c ← VM.popCont
      modify fun st => { st with regs := { st.regs with c0 := c.defineC0 st.regs.c0 } }
  | .contExt .atexitAlt =>
      let c ← VM.popCont
      modify fun st => { st with regs := { st.regs with c1 := c.defineC1 st.regs.c1 } }
  | .contExt .thenret =>
      let c ← VM.popCont
      let st ← get
      VM.push (.cont (c.defineC0 st.regs.c0))
  | .contExt .thenretAlt =>
      let c ← VM.popCont
      let st ← get
      VM.push (.cont (c.defineC0 st.regs.c1))
  | .contExt .invert =>
      modify fun st => { st with regs := { st.regs with c0 := st.regs.c1, c1 := st.regs.c0 } }
  | .contExt .booleval =>
      let c ← VM.popCont
      let st ← get
      let cc : Continuation := st.cc
      let pushNeg ←
        match mkPushIntCont (-1) with
        | .ok k => pure (k.defineC0 cc)
        | .error e => throw e
      let pushZero ←
        match mkPushIntCont 0 with
        | .ok k => pure (k.defineC0 cc)
        | .error e => throw e
      let newCc : Continuation := (c.defineC0 pushNeg).defineC1 pushZero
      set { st with cc := newCc }
  | _ => next

end TvmLean
