import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvParseMsgAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.parseMsgAddr quiet) =>
      let csr0 ← VM.popSlice
      let parsed : Except Excno (Array Value) := do
        let (t, rest) ← csr0.parseMessageAddr
        if rest.bitsRemaining != 0 || rest.refsRemaining != 0 then
          throw .cellUnd
        return t
      match parsed with
      | .ok t =>
          VM.push (.tuple t)
          if quiet then
            VM.pushSmallInt (-1)
      | .error e =>
          if quiet then
            VM.pushSmallInt 0
          else
            throw e
  | _ => next

end TvmLean

