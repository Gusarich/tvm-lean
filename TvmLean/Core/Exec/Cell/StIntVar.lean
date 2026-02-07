import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellStIntVar (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .stIntVar unsigned rev quiet =>
      VM.checkUnderflow 3
      let maxBits : Nat := if unsigned then 256 else 257
      let bits ← VM.popNatUpTo maxBits
      let (x, b) ←
        if rev then
          let x ← VM.popInt
          let b ← VM.popBuilder
          pure (x, b)
        else
          let b ← VM.popBuilder
          let x ← VM.popInt
          pure (x, b)

      if !b.canExtendBy bits then
        if quiet then
          if rev then
            VM.push (.builder b)
            VM.push (.int x)
          else
            VM.push (.int x)
            VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
      else
        let fits : Bool :=
          match x with
          | .nan => false
          | .num n =>
              if bits = 0 then
                n = 0
              else if unsigned then
                decide (0 ≤ n ∧ n < intPow2 bits)
              else
                intSignedFitsBits n bits
        if !fits then
          if quiet then
            if rev then
              VM.push (.builder b)
              VM.push (.int x)
            else
              VM.push (.int x)
              VM.push (.builder b)
            VM.pushSmallInt 1
          else
            throw .rangeChk
        else
          match x with
          | .nan =>
              -- unreachable due to `fits` check
              throw .rangeChk
          | .num n =>
              let bs : BitString ←
                if unsigned then
                  pure (natToBits n.toNat bits)
                else
                  match intToBitsTwos n bits with
                  | .ok bs => pure bs
                  | .error e => throw e
              VM.push (.builder (b.storeBits bs))
              if quiet then
                VM.pushSmallInt 0
  | _ => next

end TvmLean
