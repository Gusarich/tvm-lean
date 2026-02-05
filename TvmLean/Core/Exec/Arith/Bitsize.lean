import TvmLean.Core.Exec.Common

namespace TvmLean

def signedBitsize (n : Int) : Nat :=
  if n = 0 then
    0
  else if n > 0 then
    natLenBits n.toNat + 1
  else
    let m : Int := -n - 1
    natLenBits m.toNat + 1

set_option maxHeartbeats 1000000 in
def execInstrArithBitsize (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .bitsize =>
      let n ← VM.popIntFinite
      let width : Nat := signedBitsize n
      VM.pushSmallInt (Int.ofNat width)
  | _ => next

end TvmLean
