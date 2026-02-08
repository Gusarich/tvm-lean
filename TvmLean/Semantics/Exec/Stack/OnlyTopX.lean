import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackOnlyTopX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .onlyTopX =>
      let x ← VM.popNatUpTo ((1 <<< 30) - 1)
      let st ← get
      if x ≤ st.stack.size then
        let n := st.stack.size
        let d : Nat := n - x
        if d > 0 then
          if x > 255 then
            modify fun st => st.consumeGas (Int.ofNat (x - 255))
          let st ← get
          set { st with stack := st.stack.extract d n }
        else
          pure ()
      else
        throw .stkUnd
  | _ => next

end TvmLean
