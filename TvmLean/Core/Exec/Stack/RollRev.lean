import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackRollRev (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .rollRev =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        if x > 255 then
          modify fun st => st.consumeGas (Int.ofNat (x - 255))
        for i in [0:x] do
          VM.swap i (i + 1)
      else
        throw .stkUnd
  | _ => next

end TvmLean
