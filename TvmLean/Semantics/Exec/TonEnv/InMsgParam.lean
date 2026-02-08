import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvInMsgParam (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.inMsgParam idx) =>
      -- Matches C++ `exec_get_in_msg_param` / `exec_get_var_in_msg_param` (tonops.cpp).
      -- Stack: ... -- ... value
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if 17 < params.size then
              match params[17]! with
              | .tuple inMsgParams =>
                  if idx < inMsgParams.size then
                    VM.push (inMsgParams[idx]!)
                  else
                    throw .rangeChk
              | _ =>
                  throw .typeChk
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean
