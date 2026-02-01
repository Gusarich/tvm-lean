import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallxArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callxArgs params retVals =>
      let cont ← VM.popCont
      let st ← get
      if params > st.stack.size then
        throw .stkUnd
      let depth : Nat := st.stack.size
      let split : Nat := depth - params
      let saved : Stack := st.stack.take split
      let args : Stack := st.stack.extract split depth
      let frame : CallFrame := { savedStack := saved, retArgs := retVals }
      set { st with stack := args }
      -- C++ `call(..., pass_args=params, ...)` charges stack gas for the new stack depth.
      modify fun st => st.consumeStackGas args.size
      modify fun st => st.callToWithFrame frame cont
  | _ => next

end TvmLean
