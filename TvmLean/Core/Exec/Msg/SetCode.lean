import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsgSetCode (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .setCode =>
      let codeCell ← VM.popCell
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let bits := natToBits 0xad4de08e 32
      let newHead : Cell := Cell.mkOrdinary bits #[prev, codeCell]
      set { st with regs := { st.regs with c5 := newHead } }
  | _ => next

end TvmLean
