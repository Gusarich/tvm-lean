import TvmLean.Semantics.Exec.Common

namespace TvmLean

private def sameValueType : Value → Value → Bool
  | .int _, .int _ => true
  | .cell _, .cell _ => true
  | .slice _, .slice _ => true
  | .builder _, .builder _ => true
  | .tuple _, .tuple _ => true
  | .cont _, .cont _ => true
  | .null, .null => true
  | _, _ => false

set_option maxHeartbeats 1000000 in
def execInstrContCondSel (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .contExt .condSel =>
      VM.checkUnderflow 3
      let y ← VM.pop
      let x ← VM.pop
      if (← VM.popBool) then
        VM.push x
      else
        VM.push y
  | .contExt .condSelChk =>
      VM.checkUnderflow 3
      let y ← VM.pop
      let x ← VM.pop
      if !sameValueType x y then
        throw .typeChk
      if (← VM.popBool) then
        VM.push x
      else
        VM.push y
  | _ => next

end TvmLean
