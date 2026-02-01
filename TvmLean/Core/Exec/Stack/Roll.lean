import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackRoll (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .roll =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x < st.stack.size then
        if x > 255 then
          modify fun st => st.consumeGas (Int.ofNat (x - 255))
        for i in [0:x] do
          let k : Nat := x - 1 - i
          VM.swap k (k + 1)
      else
        throw .stkUnd
  | _ => next

end TvmLean
