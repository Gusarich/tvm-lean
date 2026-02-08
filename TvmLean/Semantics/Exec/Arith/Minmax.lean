import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithMinmax (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .minmax | .qminmax =>
      VM.checkUnderflow 2
      let x ← VM.popInt
      let y ← VM.popInt
      let quiet := i == .qminmax
      match x, y with
      | .num a, .num b =>
          if a ≤ b then
            VM.pushIntQuiet (.num a) quiet
            VM.pushIntQuiet (.num b) quiet
          else
            VM.pushIntQuiet (.num b) quiet
            VM.pushIntQuiet (.num a) quiet
      | _, _ =>
          VM.pushIntQuiet .nan quiet
          VM.pushIntQuiet .nan quiet
  | _ => next

end TvmLean
