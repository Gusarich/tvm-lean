import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowJmpxArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .jmpxArgs params =>
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let depth : Nat := st.stack.size
      let start : Nat := depth - params
      let args : Stack := st.stack.extract start depth
      set { st with stack := args }
      -- C++ `jump(..., pass_args=params)` charges stack gas for the new stack depth.
      modify fun st => st.consumeStackGas args.size
      VM.jump cont (Int.ofNat params)
  | _ => next

end TvmLean
