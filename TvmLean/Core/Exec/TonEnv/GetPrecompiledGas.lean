import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetPrecompiledGas (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .getPrecompiledGas =>
      -- Same semantics as `GETPARAM 16` in the TON opcode table.
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 16 < params.size then
              VM.push (params[16]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean
