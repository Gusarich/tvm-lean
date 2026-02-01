import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithNot (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .not_ =>
      let x ← VM.popInt
      match x with
      | .nan => VM.pushIntQuiet .nan false
      | .num n =>
          let bs ←
            match intToBitsTwos n 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let inv : BitString := bs.map (fun b => !b)
          VM.pushIntQuiet (.num (bitsToIntSignedTwos inv)) false
  | _ => next

end TvmLean
