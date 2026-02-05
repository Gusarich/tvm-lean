import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvSetRand (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.setRand mix) =>
      let x ← VM.popIntFinite
      if decide (x < 0 ∨ x ≥ intPow2 256) then
        throw .rangeChk
      let st ← get
      match st.regs.c7[0]? with
      | none => throw .rangeChk
      | some (Value.tuple params) =>
          if decide (255 < params.size) then
            throw .typeChk
          let newSeed : Int ←
            if mix then
              match params[6]? with
              | none => throw .rangeChk
              | some (Value.int (.num seed)) =>
                  if decide (seed < 0 ∨ seed ≥ intPow2 256) then
                    throw .rangeChk
                  let seedBytes := natToBytesBEFixed seed.toNat 32
                  let xBytes := natToBytesBEFixed x.toNat 32
                  let digest := sha256Digest (seedBytes ++ xBytes)
                  pure (Int.ofNat (bytesToNatBE digest))
              | some (Value.int .nan) => throw .rangeChk
              | some _ => throw .typeChk
            else
              pure x

          let (params', tpay) := tupleExtendSetIndex params 6 (.int (.num newSeed))
          let outerSize := st.regs.c7.size
          let c7' := st.regs.c7.set! 0 (.tuple params')
          let mut st' := { st with regs := { st.regs with c7 := c7' } }
          if tpay > 0 then
            st' := st'.consumeTupleGas tpay
          st' := st'.consumeTupleGas outerSize
          set st'
      | some _ => throw .typeChk
  | _ => next

end TvmLean
