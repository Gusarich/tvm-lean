import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowUntil (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .until =>
      -- Stack effect: ... body -- ...
      -- Control flow: execute `body`; if it returns `true` then continue, otherwise repeat.
      let body ← VM.popCont
      -- Match C++ `exec_until`: capture `after := extract_cc(1)` first.
      -- This also resets current `c0 := quit0` as a side-effect of save_cr=1.
      let after ← VM.extractCc 1
      let st ← get
      -- C++ `VmState::until`: only installs the loop continuation into `c0`
      -- if `body` doesn't already have `c0`.
      if body.hasC0 then
        set { st with cc := body }
      else
        set { st with regs := { st.regs with c0 := .untilBody body after }, cc := body }
  | _ => next

end TvmLean
