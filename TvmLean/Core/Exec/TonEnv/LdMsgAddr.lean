import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvLdMsgAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ldMsgAddr quiet =>
      let csr0 ← VM.popSlice
      match csr0.skipMessageAddr with
      | .ok csr1 =>
          let addrCell := Slice.prefixCell csr0 csr1
          VM.push (.slice (Slice.ofCell addrCell))
          VM.push (.slice csr1)
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.push (.slice csr0)
            VM.pushSmallInt 0
          else
            throw e
  | _ => next

end TvmLean
