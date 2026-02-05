import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallcc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callcc =>
      let cont ← VM.popCont
      let cc ← VM.extractCc 3
      VM.push (.cont cc)
      VM.jump cont
  | .callccArgs params retVals =>
      let st ← get
      if params + 1 > st.stack.size then
        throw .stkUnd
      let cont ← VM.popCont
      let cc ← VM.extractCc 3 (Int.ofNat params) retVals
      VM.push (.cont cc)
      VM.jump cont
  | .callccVarArgs =>
      let retVals ← VM.popIntFinite
      if decide (retVals < -1 ∨ retVals > 254) then
        throw .rangeChk
      let params ← VM.popIntFinite
      if decide (params < -1 ∨ params > 254) then
        throw .rangeChk
      let st ← get
      if 1 > st.stack.size then
        throw .stkUnd
      if decide (params ≥ 0) then
        if (params.toNat + 1) > st.stack.size then
          throw .stkUnd
      let cont ← VM.popCont
      let cc ← VM.extractCc 3 params retVals
      VM.push (.cont cc)
      VM.jump cont
  | _ => next

end TvmLean

