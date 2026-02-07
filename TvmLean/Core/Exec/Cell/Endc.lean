import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellEndc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .endc =>
      let b ← VM.popBuilder
      modify fun st => st.consumeGas cellCreateGasPrice
      VM.push (.cell b.finalize)
  | _ => next

end TvmLean
