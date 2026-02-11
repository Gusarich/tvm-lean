import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowWhile (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .while_ =>
      -- Stack effect: ... cond body -- ...
      -- Control flow: execute `cond`; if true then execute `body` and repeat.
      -- Match C++ `exec_while`: underflow check happens before type checks from pops.
      VM.checkUnderflow 2
      let body ← VM.popCont
      let cond ← VM.popCont
      -- Match C++ `exec_while`: `after := extract_cc(1)` (save/reset c0) before `loop_while`.
      let after ← VM.extractCc 1
      let st ← get
      -- Match C++ `VmState::loop_while`: install loop continuation into c0 only if `cond` has no c0.
      if cond.hasC0 then
        set { st with cc := cond }
      else
        set { st with regs := { st.regs with c0 := .whileCond cond body after }, cc := cond }
  | _ => next

end TvmLean
