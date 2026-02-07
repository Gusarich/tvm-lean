import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrMsgRawReserveX (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .rawReserveX =>
      -- Matches C++ `exec_reserve_raw` (mode=1; tonops.cpp).
      VM.checkUnderflow 3
      let f ← VM.popNatUpTo 31
      let y? ← VM.popMaybeCell
      let x ← VM.popIntFinite
      if x < 0 then
        throw .rangeChk
      let bitsLen : Nat := natLenBits x.toNat
      let lenBytes : Nat := (bitsLen + 7) / 8
      if lenBytes ≥ 16 then
        throw .cellOv
      let gramsBits : BitString := natToBits lenBytes 4 ++ natToBits x.toNat (lenBytes * 8)
      let hasY : Bool := y?.isSome
      let bits : BitString := natToBits 0x36e6b809 32 ++ natToBits f 8 ++ gramsBits ++ #[hasY]
      if bits.size > 1023 then
        throw .cellOv
      modify fun st => st.consumeGas cellCreateGasPrice
      let st ← get
      let prev := st.regs.c5
      let refs : Array Cell :=
        match y? with
        | none => #[prev]
        | some y => #[prev, y]
      let newHead : Cell := Cell.mkOrdinary bits refs
      set { st with regs := { st.regs with c5 := newHead } }
  | _ => next

end TvmLean
