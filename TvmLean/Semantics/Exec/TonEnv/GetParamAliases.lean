import TvmLean.Semantics.Exec.Common

namespace TvmLean

def VM.pushC7Param (idx : Nat) : VM Unit := do
  let st ← get
  if 0 < st.regs.c7.size then
    match st.regs.c7[0]! with
    | .tuple params =>
        if idx < params.size then
          VM.push (params[idx]!)
        else
          throw .rangeChk
    | _ =>
        throw .typeChk
  else
    throw .rangeChk

set_option maxHeartbeats 1000000 in
def execInstrTonEnvGetParamAliases (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp .blockLt => VM.pushC7Param 4
  | .tonEnvOp .lTime => VM.pushC7Param 5
  | .tonEnvOp .randSeed => VM.pushC7Param 6
  | .tonEnvOp .myAddr => VM.pushC7Param 8
  | .tonEnvOp .configRoot => VM.pushC7Param 9
  | .tonEnvOp .myCode => VM.pushC7Param 10
  | .tonEnvOp .incomingValue => VM.pushC7Param 11
  | .tonEnvOp .storageFees => VM.pushC7Param 12
  | .tonEnvOp .prevBlocksInfoTuple => VM.pushC7Param 13
  | .tonEnvOp .unpackedConfigTuple => VM.pushC7Param 14
  | .tonEnvOp .duePayment => VM.pushC7Param 15
  | _ => next

end TvmLean
