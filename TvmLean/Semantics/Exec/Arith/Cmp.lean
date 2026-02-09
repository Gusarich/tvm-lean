import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArithCmp (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cmp =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan false
      | _, .nan => VM.pushIntQuiet .nan false
      | .num a, .num b =>
          if a < b then
            VM.pushSmallInt (-1)
          else if a = b then
            VM.pushSmallInt 0
          else
            VM.pushSmallInt 1
  | .qcmp =>
      VM.checkUnderflow 2
      let y ← VM.popInt
      let x ← VM.popInt
      match x, y with
      | .nan, _ => VM.pushIntQuiet .nan true
      | _, .nan => VM.pushIntQuiet .nan true
      | .num a, .num b =>
          if a < b then
            VM.pushSmallInt (-1)
          else if a = b then
            VM.pushSmallInt 0
          else
            VM.pushSmallInt 1
  | _ => next

end TvmLean
