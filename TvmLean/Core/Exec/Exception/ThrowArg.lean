import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowArg (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwArg exc =>
      let arg ← VM.pop
      modify fun st => (st.throwExceptionArg exc arg).consumeGas exceptionGasPrice
  | _ => next

end TvmLean
