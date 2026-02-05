import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallxVarArgs (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callxVarArgs =>
      -- Mirrors C++ `exec_callx_varargs`: pop `retvals`, `params` (both in [-1..254]) and call the continuation.
      let retVals ← VM.popIntFinite
      if decide (retVals < -1 ∨ retVals > 254) then
        throw .rangeChk
      let params ← VM.popIntFinite
      if decide (params < -1 ∨ params > 254) then
        throw .rangeChk
      let cont ← VM.popCont
      let st ← get
      if decide (params < 0) then
        let frame : CallFrame := { savedStack := #[], retArgs := retVals }
        modify fun st => st.consumeStackGas st.stack.size
        modify fun st => st.callToWithFrame frame cont
      else
        let p : Nat := params.toNat
        if p > st.stack.size then
          throw .stkUnd
        let depth : Nat := st.stack.size
        let split : Nat := depth - p
        let saved : Stack := st.stack.take split
        let args : Stack := st.stack.extract split depth
        let frame : CallFrame := { savedStack := saved, retArgs := retVals }
        set { st with stack := args }
        -- Charge stack gas for the new stack depth.
        modify fun st => st.consumeStackGas args.size
        modify fun st => st.callToWithFrame frame cont
  | _ => next

end TvmLean

