import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsgSendRawMsg (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .sendRawMsg =>
      let mode ← VM.popNatUpTo 255
      let msgCell ← VM.popCell
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let bits := natToBits 0x0ec3c86d 32 ++ natToBits mode 8
      let newHead : Cell := Cell.mkOrdinary bits #[prev, msgCell]
      set { st with regs := { st.regs with c5 := newHead } }
  | _ => next

end TvmLean
