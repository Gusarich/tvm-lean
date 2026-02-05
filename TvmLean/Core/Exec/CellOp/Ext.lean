import TvmLean.Core.Exec.Common

namespace TvmLean

def sliceBitsSuffixEq (suf whole : Slice) : Bool :=
  let a : BitString := suf.readBits suf.bitsRemaining
  let b : BitString := whole.readBits whole.bitsRemaining
  a.size ≤ b.size && b.extract (b.size - a.size) b.size == a

set_option maxHeartbeats 1000000 in
def execCellOpExt (op : CellInstr) (next : VM Unit) : VM Unit := do
  match op with
  | .sdFirst =>
      let s ← VM.popSlice
      let ok : Bool := s.haveBits 1 && s.cell.bits[s.bitPos]!
      VM.pushSmallInt (if ok then -1 else 0)
  | .sdSfx =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      VM.pushSmallInt (if sliceBitsSuffixEq s1 s2 then -1 else 0)
  | .sdSfxRev =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      VM.pushSmallInt (if sliceBitsSuffixEq s2 s1 then -1 else 0)
  | .sdPsfx =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      let ok : Bool := s1.bitsRemaining < s2.bitsRemaining && sliceBitsSuffixEq s1 s2
      VM.pushSmallInt (if ok then -1 else 0)
  | .sdPsfxRev =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      let ok : Bool := s2.bitsRemaining < s1.bitsRemaining && sliceBitsSuffixEq s2 s1
      VM.pushSmallInt (if ok then -1 else 0)
  | .sdCntLead1 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let mut cnt : Nat := 0
      while cnt < rem && s.cell.bits[s.bitPos + cnt]! == true do
        cnt := cnt + 1
      VM.pushSmallInt (Int.ofNat cnt)
  | .sdCntTrail1 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let mut cnt : Nat := 0
      if rem = 0 then
        VM.pushSmallInt 0
      else
        while cnt < rem && s.cell.bits[s.bitPos + rem - 1 - cnt]! == true do
          cnt := cnt + 1
        VM.pushSmallInt (Int.ofNat cnt)
  | .strefR quiet =>
      let c ← VM.popCell
      let b ← VM.popBuilder
      if b.canExtendBy 0 1 then
        VM.push (.builder { b with refs := b.refs.push c })
        if quiet then
          VM.pushSmallInt 0
      else
        if quiet then
          VM.push (.builder b)
          VM.push (.cell c)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
  | .endxc =>
      let special ← VM.popBool
      let b ← VM.popBuilder
      let c ←
        match b.finalizeCopy special with
        | .ok c => pure c
        | .error e => throw e
      VM.push (.cell c)
  | .sdSubstr =>
      let bits ← VM.popNatUpTo 1023
      let offs ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits (offs + bits) then
        let fromPos := s.bitPos + offs
        let toPos := fromPos + bits
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract fromPos toPos)
            (s.cell.refs.extract s.refPos s.cell.refs.size)
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .scutfirst =>
      let refs ← VM.popNatUpTo 4
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits && s.haveRefs refs then
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract s.bitPos (s.bitPos + bits))
            (s.cell.refs.extract s.refPos (s.refPos + refs))
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .sskipfirst =>
      let refs ← VM.popNatUpTo 4
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits && s.haveRefs refs then
        VM.push (.slice { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs })
      else
        throw .cellUnd
  | .scutlast =>
      let refs ← VM.popNatUpTo 4
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining && refs ≤ s.refsRemaining then
        let dropBits : Nat := s.bitsRemaining - bits
        let dropRefs : Nat := s.refsRemaining - refs
        let fromBits := s.bitPos + dropBits
        let fromRefs := s.refPos + dropRefs
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract fromBits s.cell.bits.size)
            (s.cell.refs.extract fromRefs s.cell.refs.size)
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .sskiplast =>
      let refs ← VM.popNatUpTo 4
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining && refs ≤ s.refsRemaining then
        let keepBits : Nat := s.bitsRemaining - bits
        let keepRefs : Nat := s.refsRemaining - refs
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract s.bitPos (s.bitPos + keepBits))
            (s.cell.refs.extract s.refPos (s.refPos + keepRefs))
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | _ =>
      next

end TvmLean
