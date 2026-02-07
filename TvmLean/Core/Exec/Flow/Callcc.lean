import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallcc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callcc =>
      VM.checkUnderflow 1
      let cont ← VM.popCont
      let cc ← VM.extractCc 3
      VM.push (.cont cc)
      VM.jump cont
  | .callccArgs params retVals =>
      VM.checkUnderflow (params + 1)
      let cont ← VM.popCont
      let cc ← VM.extractCc 3 (Int.ofNat params) retVals
      VM.push (.cont cc)
      VM.jump cont
  | .callccVarArgs =>
      VM.checkUnderflow 3
      let retVals ← VM.popIntFinite
      if decide (retVals < -1 ∨ retVals > 254) then
        throw .rangeChk
      let params ← VM.popIntFinite
      if decide (params < -1 ∨ params > 254) then
        throw .rangeChk
      let need : Nat := if decide (params ≥ 0) then params.toNat + 1 else 0
      VM.checkUnderflow need
      let cont ← VM.popCont
      let cc ← VM.extractCc 3 params retVals
      VM.push (.cont cc)
      VM.jump cont
  | _ => next

end TvmLean
