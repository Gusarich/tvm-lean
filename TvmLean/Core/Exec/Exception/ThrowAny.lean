import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrExceptionThrowAny (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .throwAny hasParam hasCond throwCond =>
      let flag ←
        if hasCond then
          VM.popBool
        else
          pure throwCond
      let excnoNat ← VM.popNatUpTo 0xffff
      let excno : Int := Int.ofNat excnoNat
      if flag != throwCond then
        if hasParam then
          let _ ← VM.pop
          pure ()
        else
          pure ()
      else
        if hasParam then
          let arg ← VM.pop
          modify fun st => (st.throwExceptionArg excno arg).consumeGas exceptionGasPrice
        else
          modify fun st => (st.throwException excno).consumeGas exceptionGasPrice
  | _ => next

end TvmLean
