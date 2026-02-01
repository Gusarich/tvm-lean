import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execCellOpLoadLeInt (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .loadLeInt unsigned bytes prefetch quiet =>
      let s ← VM.popSlice
      let needBits : Nat := bytes * 8
      if !s.haveBits needBits then
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
      else
        let b0 ←
          match s.prefetchBytesCellUnd bytes with
          | .ok v => pure v
          | .error e => throw e
        let u : Nat := bytesToNatLE b0
        let x : Int :=
          if unsigned then
            Int.ofNat u
          else
            natToIntSignedTwos u (bytes * 8)
        VM.pushIntQuiet (.num x) false
        if !prefetch then
          let s' : Slice := { s with bitPos := s.bitPos + needBits }
          VM.push (.slice s')
        if quiet then
          VM.pushSmallInt (-1)
  | _ => next

end TvmLean
