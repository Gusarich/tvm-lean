import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStbRef (i : Instr) (next : VM Unit) : VM Unit := do
  let handle (rev quiet : Bool) : VM Unit := do
    -- Matches C++ `exec_store_builder_as_ref(_rev)` (cellops.cpp).
    VM.checkUnderflow 2
    if rev then
      -- Stack: ... builder cb2 -- ...  (cb2 on top)
      let cb2 ← VM.popBuilder
      let b ← VM.popBuilder
      if b.canExtendBy 0 1 then
        modify fun st => st.consumeGas cellCreateGasPrice
        let c : Cell := cb2.finalize
        VM.push (.builder { b with refs := b.refs.push c })
        if quiet then
          VM.pushSmallInt 0
      else
        if quiet then
          VM.push (.builder b)
          VM.push (.builder cb2)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
    else
      -- Stack: ... cb2 builder -- ...  (builder on top)
      let b ← VM.popBuilder
      let cb2 ← VM.popBuilder
      if b.canExtendBy 0 1 then
        modify fun st => st.consumeGas cellCreateGasPrice
        let c : Cell := cb2.finalize
        VM.push (.builder { b with refs := b.refs.push c })
        if quiet then
          VM.pushSmallInt 0
      else
        if quiet then
          VM.push (.builder cb2)
          VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
  match i with
  | .stbRef rev quiet =>
      handle rev quiet
  | .endcst =>
      handle true false
  | _ =>
      next

end TvmLean
