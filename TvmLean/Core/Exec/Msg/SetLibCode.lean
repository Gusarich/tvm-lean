import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsgSetLibCode (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .setLibCode =>
      -- Mirrors C++ `exec_set_lib_code` (tonops.cpp) for global_version >= 4:
      -- mode ∈ {0,1,2} ∪ {16,17,18}; other values are rangeChk.
      VM.checkUnderflow 2
      let mode ← VM.popNatUpTo 31
      if (mode &&& 0x0f) > 2 then
        throw .rangeChk
      let codeCell ← VM.popCell
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let modeByte : Nat := mode * 2 + 1
      let bits := natToBits 0x26fa1dd4 32 ++ natToBits modeByte 8
      let newHead : Cell := Cell.mkOrdinary bits #[prev, codeCell]
      set { st with regs := { st.regs with c5 := newHead } }
  | _ => next

end TvmLean
