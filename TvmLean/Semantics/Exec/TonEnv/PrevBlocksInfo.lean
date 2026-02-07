import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases

namespace TvmLean

def VM.pushPrevBlocksInfo (idx : Nat) : VM Unit := do
  -- Mirrors C++ `exec_get_prev_blocks_info` (tonops.cpp).
  VM.pushC7Param 13
  let v ← VM.pop
  match v with
  | .tuple t =>
      if idx < t.size then
        VM.push (t[idx]!)
      else
        throw .rangeChk
  | _ => throw .typeChk

set_option maxHeartbeats 1000000 in
def execInstrTonEnvPrevBlocksInfo (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .prevMcBlocks =>
      VM.pushPrevBlocksInfo 0
  | .tonEnvOp .prevKeyBlock =>
      VM.pushPrevBlocksInfo 1
  | .tonEnvOp .prevMcBlocks100 =>
      VM.pushPrevBlocksInfo 2
  | _ => next

end TvmLean

