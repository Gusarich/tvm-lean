import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowIf (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwIf exc =>
      if (← VM.popBool) then
        modify fun st => (st.throwException exc).consumeGas exceptionGasPrice
      else
        pure ()
  | _ => next

end TvmLean
