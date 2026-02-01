import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGlobalId (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .globalId =>
      -- Matches C++ `exec_get_global_id` (tonops.cpp) for global_version >= 6.
      let unpacked ← VM.getUnpackedConfigTuple
      match unpacked.get? 1 with
      | some (.slice cs) =>
          if !cs.haveBits 32 then
            throw .cellUnd
          let gid : Int := bitsToIntSignedTwos (cs.readBits 32)
          VM.pushSmallInt gid
      | some .null => throw .invOpcode
      | some _ => throw .typeChk
      | none => throw .typeChk
  | _ => next

end TvmLean
