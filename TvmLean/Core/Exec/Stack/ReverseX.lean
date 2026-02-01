import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackReverseX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .reverseX =>
      let y ← VM.popNatUpTo ((1 <<< 30) - 1)
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        if x > 255 then
          modify fun st => st.consumeGas (Int.ofNat (x - 255))
        let st ← get
        let n := st.stack.size
        let front := st.stack.take (n - total)
        let revPart := st.stack.extract (n - total) (n - y)
        let top := st.stack.extract (n - y) n
        set { st with stack := front ++ revPart.reverse ++ top }
      else
        throw .stkUnd
  | _ => next

end TvmLean
