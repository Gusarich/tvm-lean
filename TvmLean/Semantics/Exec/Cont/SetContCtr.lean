import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContSetContCtr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .setContCtr idx =>
      -- Mirrors `SETCONTCTR c<idx>` from `crypto/vm/contops.cpp` (`exec_setcont_ctr`):
      -- define `c<idx>` inside a continuation popped from the stack (wrapping with an envelope if needed).
      VM.checkUnderflow 2
      let cont ← VM.popCont
      let v ← VM.pop
      let cont ←
        match cont.defineCtr idx v with
        | .ok k => pure k
        | .error e => throw e
      VM.push (.cont cont)
  | _ => next

end TvmLean
