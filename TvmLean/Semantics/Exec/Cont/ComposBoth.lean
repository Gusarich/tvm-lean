import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContComposBoth (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .composBoth =>
      -- Mirrors C++ `COMPOSBOTH` (`exec_compos` with mask=3).
      let val ← VM.popCont
      let cont ← VM.popCont
      let cont := cont.defineC0 val
      VM.push (.cont (cont.defineC1 val))
  | _ => next

end TvmLean
