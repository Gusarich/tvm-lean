import TvmLean.Core.Exec.Common

namespace TvmLean

private def dropFirstRootLoad (dictCell? : Option Cell) (loaded : Array Cell) : Array Cell :=
  match dictCell? with
  | none => loaded
  | some root =>
      Id.run do
        let mut skipped : Bool := false
        let mut out : Array Cell := #[]
        for c in loaded do
          if (!skipped) && c == root then
            skipped := true
          else
            out := out.push c
        out

set_option maxHeartbeats 1000000 in
def execInstrDictDictSetB (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .dictSetB intKey unsigned mode =>
      VM.checkUnderflow 4
      let n ← VM.popNatUpTo 1023
      let dictCell? ← VM.popMaybeCell
      let keyBits? : Option BitString ←
        if intKey then
          let idxVal ← VM.popInt
          match idxVal with
          | .nan => throw .rangeChk
          | .num idx =>
              match dictKeyBits? idx n unsigned with
              | some bs => pure (some bs)
              | none => throw .rangeChk
        else
          let keySlice ← VM.popSlice
          if keySlice.haveBits n then
            pure (some (keySlice.readBits n))
          else
            pure none
      let newVal ← VM.popBuilder
      let keyBits ←
        match keyBits? with
        | some bs => pure bs
        | none => throw .cellUnd
      match dictCell? with
      | some c => modify fun st => st.registerCellLoad c
      | none => pure ()
      match dictSetBuilderWithCells dictCell? keyBits newVal mode with
      | .error e =>
          let loaded := dropFirstRootLoad dictCell? (dictLookupVisitedCells dictCell? keyBits)
          for c in loaded do
            modify fun st => st.registerCellLoad c
          throw e
      | .ok (newRoot?, ok, created, loaded) =>
          let loaded := dropFirstRootLoad dictCell? loaded
          for c in loaded do
            modify fun st => st.registerCellLoad c
          if created > 0 then
            modify fun st => st.consumeGas (cellCreateGasPrice * Int.ofNat created)
          match newRoot? with
          | none => VM.push .null
          | some c => VM.push (.cell c)
          if mode == .set then
            if !ok then
              throw .fatal
          else
            VM.pushSmallInt (if ok then -1 else 0)
  | _ => next

end TvmLean
