import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrStackReverse (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .reverse x y =>
      let st ← get
      let total : Nat := x + y
      if total ≤ st.stack.size then
        let n := st.stack.size
        let start : Nat := n - total
        let stop : Nat := n - y
        let arr := Id.run do
          let mut a := st.stack
          for i in [0:(x / 2)] do
            let i1 : Nat := start + i
            let i2 : Nat := stop - 1 - i
            let v1 := a[i1]!
            let v2 := a[i2]!
            a := a.set! i1 v2
            a := a.set! i2 v1
          return a
        set { st with stack := arr }
      else
        throw .stkUnd
  | _ => next

end TvmLean
