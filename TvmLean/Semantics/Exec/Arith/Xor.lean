import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithXor (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .xor =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          let ba ←
            match intToBitsTwos a 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bb ←
            match intToBitsTwos b 257 with
            | .ok bs => pure bs
            | .error e => throw e
          let bc := bitsXor ba bb
          let c := bitsToIntSignedTwos bc
          VM.pushIntQuiet (.num c) false
  | _ => next

end TvmLean
