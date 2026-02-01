import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowArgIf (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwArgIf exc =>
      let cond ← VM.popBool
      if cond then
        let arg ← VM.pop
        modify fun st => (st.throwExceptionArg exc arg).consumeGas exceptionGasPrice
      else
        let _ ← VM.pop
        pure ()
  | _ => next

end TvmLean
