import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithAdd (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .add =>
      -- C++ `exec_add` performs `check_underflow(2)` before typed pops.
      -- This preserves `stkUnd` precedence over `typeChk` on depth-1 stacks.
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.add y) false
  | _ => next

end TvmLean
