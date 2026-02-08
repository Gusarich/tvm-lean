import TvmLean.Semantics.Exec.Common

namespace TvmLean

def VM.blessArgsCommon (copy : Nat) (more : Int) : VM Unit := do
  if decide (more < -1 ∨ more > 255) then
    throw .rangeChk
  let st ← get
  if copy + 1 > st.stack.size then
    throw .stkUnd
  let cs ← VM.popSlice
  let st ← get
  if copy > st.stack.size then
    throw .stkUnd
  let depth : Nat := st.stack.size
  let split : Nat := depth - copy
  let saved : Stack := st.stack.take split
  let captured : Stack := st.stack.extract split depth
  let cdata : OrdCdata := { stack := captured, nargs := more }
  let cont : Continuation := .ordinary cs (.quit 0) OrdCregs.empty cdata
  set { st with stack := saved }
  modify fun st => st.consumeStackGas captured.size
  VM.push (.cont cont)

set_option maxHeartbeats 1000000 in
def execInstrContBless (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .bless =>
      let cs ← VM.popSlice
      -- Codepage is always 0 in this model; represent as an ordinary continuation.
      VM.push (.cont (.ordinary cs (.quit 0) OrdCregs.empty OrdCdata.empty))
  | .blessArgs copy more =>
      if copy > 15 then
        throw .rangeChk
      if decide (more < -1 ∨ more > 14) then
        throw .rangeChk
      VM.blessArgsCommon copy more
  | .blessVarArgs =>
      VM.checkUnderflow 2
      let more ← VM.popIntFinite
      if decide (more < -1 ∨ more > 255) then
        throw .rangeChk
      let copy ← VM.popNatUpTo 255
      VM.blessArgsCommon copy more
  | _ => next

end TvmLean
