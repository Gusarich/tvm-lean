import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsgChangeLib (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .changeLib =>
      -- Mirrors C++ `exec_change_lib` (tonops.cpp) for global_version >= 4.
      let mode ← VM.popNatUpTo 31
      if (mode &&& 0x0f) > 2 then
        throw .rangeChk
      let hash ← VM.popIntFinite
      if decide (hash < 0 ∨ hash ≥ intPow2 256) then
        throw .rangeChk
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let modeByte : Nat := mode * 2
      let bits :=
        natToBits 0x26fa1dd4 32 ++
        natToBits modeByte 8 ++
        natToBits hash.toNat 256
      let newHead : Cell := Cell.mkOrdinary bits #[prev]
      set { st with regs := { st.regs with c5 := newHead } }
  | _ => next

end TvmLean

