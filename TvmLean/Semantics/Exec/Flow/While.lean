import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowWhile (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .while_ =>
      -- Stack effect: ... cond body -- ...
      -- Control flow: execute `cond`; if true then execute `body` and repeat.
      let body ← VM.popCont
      let cond ← VM.popCont
      let st ← get
      -- Capture the "after" continuation as the rest of the current code,
      -- but remember the current return continuation in `savedC0` so we can restore it when the loop terminates.
      let after :=
        match st.cc with
        | .ordinary rest _ _ _ => .ordinary rest st.regs.c0 OrdCregs.empty OrdCdata.empty
        | _ => st.cc
      set { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | _ => next

end TvmLean
