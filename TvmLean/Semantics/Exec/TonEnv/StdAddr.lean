import TvmLean.Semantics.Exec.Common

namespace TvmLean

def Slice.skipStdMessageAddr (s : Slice) : Except Excno Slice := do
  -- Mirrors TON `skip_std_message_addr` for modern TVM (global_version >= 12):
  -- only `addr_std$10` with `anycast = nothing$0` is accepted.
  let (tag, s1) ← s.takeBitsAsNatCellUnd 2
  if tag != 2 then
    throw .cellUnd
  let (anycast, s2) ← s1.takeBitsAsNatCellUnd 1
  if anycast != 0 then
    throw .cellUnd
  let need : Nat := 8 + 256
  if s2.haveBits need then
    return s2.advanceBits need
  else
    throw .cellUnd

def isValidStdMsgAddr (cs : Slice) : Bool :=
  -- Mirrors TON `is_valid_std_msg_addr` for global_version >= 12.
  cs.refsRemaining == 0 &&
    cs.bitsRemaining == 3 + 8 + 256 &&
      bitsToNat (cs.readBits 3) == 0b100

set_option maxHeartbeats 1000000 in
def execInstrTonEnvStdAddr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tonEnvOp (.ldStdAddr _quiet) =>
      let quiet := _quiet
      let csr0 ← VM.popSlice
      match csr0.skipStdMessageAddr with
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
  | .tonEnvOp (.ldOptStdAddr _quiet) =>
      let quiet := _quiet
      let csr0 ← VM.popSlice
      if !csr0.haveBits 2 then
        if quiet then
          VM.push (.slice csr0)
          VM.pushSmallInt 0
        else
          throw .cellUnd
      else
        let tag : Nat := bitsToNat (csr0.readBits 2)
        if tag = 0b00 then
          let csr1 := csr0.advanceBits 2
          VM.push .null
          VM.push (.slice csr1)
          if quiet then
            VM.pushSmallInt (-1)
        else
          match csr0.skipStdMessageAddr with
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
  | .tonEnvOp (.stStdAddr _quiet) =>
      let quiet := _quiet
      -- Stack: ... slice builder -- ...
      VM.checkUnderflow 2
      let b ← VM.popBuilder
      let cs ← VM.popSlice
      let c := cs.toCellRemaining
      let ok : Bool := isValidStdMsgAddr cs && b.canExtendBy c.bits.size c.refs.size
      if ok then
        let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
        VM.push (.builder b')
        if quiet then
          VM.pushSmallInt 0
      else
        if quiet then
          VM.push (.slice cs)
          VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
  | .tonEnvOp (.stOptStdAddr _quiet) =>
      let quiet := _quiet
      -- Stack: ... (slice|null) builder -- ...
      VM.checkUnderflow 2
      let b ← VM.popBuilder
      let v ← VM.pop
      match v with
      | .null =>
          if !b.canExtendBy 2 then
            if quiet then
              VM.push .null
              VM.push (.builder b)
              VM.pushSmallInt (-1)
            else
              throw .cellOv
          else
            let b' := b.storeBits (Array.replicate 2 false)
            VM.push (.builder b')
            if quiet then
              VM.pushSmallInt 0
      | .slice cs =>
          let c := cs.toCellRemaining
          let ok : Bool := isValidStdMsgAddr cs && b.canExtendBy c.bits.size c.refs.size
          if ok then
            let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
            VM.push (.builder b')
            if quiet then
              VM.pushSmallInt 0
          else
            if quiet then
              VM.push (.slice cs)
              VM.push (.builder b)
              VM.pushSmallInt (-1)
            else
              throw .cellOv
      | _ =>
          if quiet then
            -- C++ pushes `as_slice()` result (null) on quiet type mismatch.
            VM.push .null
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .typeChk
  | _ => next

end TvmLean
