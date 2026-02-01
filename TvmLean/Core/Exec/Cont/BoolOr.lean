import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContBoolOr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .boolOr =>
      -- Mirrors C++ `BOOLOR` (`exec_compos` with mask=2).
      let val ← VM.popCont
      let cont ← VM.popCont
      VM.push (.cont (cont.defineC1 val))
  | _ => next

end TvmLean
