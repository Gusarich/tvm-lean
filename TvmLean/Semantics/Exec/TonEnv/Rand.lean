import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvRand (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .rand =>
      let x ← VM.popIntFinite
      let y ← VM.generateRandu256
      let z := floorDivPow2 (x * y) 256
      VM.pushIntQuiet (.num z) false
  | _ => next

end TvmLean
