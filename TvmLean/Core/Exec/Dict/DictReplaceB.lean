import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDictDictReplaceB (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictReplaceB intKey unsigned =>
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits : BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure bs
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (keySlice.readBits n)
          else
            throw .cellUnd
      let newVal ← VM.popBuilder
      match dictCell? with
      | some c => modify fun st => st.registerCellLoad c
      | none => pure ()
      match dictReplaceBuilderWithCells dictCell? keyBits newVal with
      | .error e =>
          throw e
      | .ok (newRoot?, ok, created, loaded) =>
          let loaded :=
            match dictCell? with
            | none => loaded
            | some root => loaded.filter (fun c => c != root)
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
          match newRoot? with
          | none => VM.push .null
          | some c => VM.push (.cell c)
          VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
