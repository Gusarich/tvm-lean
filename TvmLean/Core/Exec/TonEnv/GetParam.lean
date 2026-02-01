import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetParam (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .getParam idx =>
      let st ← get
      if 0 < st.regs.c7.size then
        match st.regs.c7[0]! with
        | .tuple params =>
            if idx < params.size then
              VM.push (params[idx]!)
            else
              throw .rangeChk
        | _ =>
            throw .typeChk
      else
        throw .rangeChk
  | _ => next

end TvmLean
