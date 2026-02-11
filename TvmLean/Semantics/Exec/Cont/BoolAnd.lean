import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContBoolAnd (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .boolAnd =>
      -- Mirrors C++ `BOOLAND` (`exec_compos` with mask=1).
      -- C++ performs `check_underflow(2)` before any `pop_cont`.
      VM.checkUnderflow 2
      let val ← VM.popCont
      let cont ← VM.popCont
      VM.push (.cont (cont.defineC0 val))
  | _ => next

end TvmLean
