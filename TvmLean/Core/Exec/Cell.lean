import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCell (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .ctos =>
      let c ← VM.popCell
      -- C++ `CTOS` uses `load_cell_slice_ref` which rejects exotic/special cells.
      if c.special then
        throw .cellUnd
      -- C++ `CTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
      modify fun st => st.registerCellLoad c
      VM.push (.slice (Slice.ofCell c))
  | .xctos =>
      let c ← VM.popCell
      -- C++ `XCTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
      modify fun st => st.registerCellLoad c
      VM.push (.slice (Slice.ofCell c))
      -- C++ `XCTOS` also returns a boolean `is_special` (true for exotic/special cells).
      VM.pushSmallInt (if c.special then -1 else 0)
  | .newc =>
      VM.push (.builder Builder.empty)
  | .endc =>
      let b ← VM.popBuilder
      VM.push (.cell b.finalize)
  | .ends =>
      let s ← VM.popSlice
      if s.bitsRemaining == 0 && s.refsRemaining == 0 then
        pure ()
      else
        throw .cellUnd
  | .sbits =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.bitsRemaining)
  | .srefs =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.refsRemaining)
  | .sbitrefs =>
      let s ← VM.popSlice
      VM.pushSmallInt (Int.ofNat s.bitsRemaining)
      VM.pushSmallInt (Int.ofNat s.refsRemaining)
  | .cdepth =>
      let c ← VM.popMaybeCell
      match c with
      | none => VM.pushSmallInt 0
      | some cell => VM.pushSmallInt (Int.ofNat cell.depth)
  | .sempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.bitsRemaining == 0 && s.refsRemaining == 0 then -1 else 0)
  | .sdempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.bitsRemaining == 0 then -1 else 0)
  | .srempty =>
      let s ← VM.popSlice
      VM.pushSmallInt (if s.refsRemaining == 0 then -1 else 0)
  | .sdCntLead0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let mut cnt : Nat := 0
      while cnt < rem && s.cell.bits[s.bitPos + cnt]! == false do
        cnt := cnt + 1
      VM.pushSmallInt (Int.ofNat cnt)
  | .sdCntTrail0 =>
      let s ← VM.popSlice
      let rem : Nat := s.bitsRemaining
      let endPos : Nat := s.cell.bits.size
      let mut cnt : Nat := 0
      while cnt < rem && s.cell.bits[endPos - 1 - cnt]! == false do
        cnt := cnt + 1
      VM.pushSmallInt (Int.ofNat cnt)
  | .sdEq =>
      let s2 ← VM.popSlice
      let s1 ← VM.popSlice
      -- Matches C++ `CellSlice::lex_cmp`: compare only remaining bits (ignore refs).
      let b1 := s1.readBits s1.bitsRemaining
      let b2 := s2.readBits s2.bitsRemaining
      VM.pushSmallInt (if b1 == b2 then -1 else 0)
  | .sdcutfirst =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract s.bitPos (s.bitPos + bits))
            (s.cell.refs.extract s.refPos s.cell.refs.size)
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .sdskipfirst =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | .sdcutlast =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let drop : Nat := s.bitsRemaining - bits
        VM.push (.slice (s.advanceBits drop))
      else
        throw .cellUnd
  | .sdskiplast =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if bits ≤ s.bitsRemaining then
        let keep : Nat := s.bitsRemaining - bits
        let newCell : Cell :=
          Cell.mkOrdinary
            (s.cell.bits.extract s.bitPos (s.bitPos + keep))
            (s.cell.refs.extract s.refPos s.cell.refs.size)
        VM.push (.slice (Slice.ofCell newCell))
      else
        throw .cellUnd
  | .sdBeginsX quiet =>
      let pref ← VM.popSlice
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      if ok then
        VM.push (.slice (s.advanceBits prefBits.size))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .sdBeginsConst quiet pref =>
      let s ← VM.popSlice
      let prefBits := pref.readBits pref.bitsRemaining
      let ok : Bool := s.haveBits prefBits.size && s.readBits prefBits.size == prefBits
      if ok then
        VM.push (.slice (s.advanceBits prefBits.size))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .ldu bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n := bitsToNat bs
        VM.push (.int (.num (Int.ofNat n)))
        VM.push (.slice (s.advanceBits bits))
      else
        throw .cellUnd
  | .loadInt unsigned prefetch quiet bits =>
      if bits == 0 then
        throw .rangeChk
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n : Int :=
          if unsigned then
            Int.ofNat (bitsToNat bs)
          else
            bitsToIntSignedTwos bs
        VM.pushIntQuiet (.num n) false
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
          else
            throw .cellUnd
  | .loadIntVar unsigned prefetch quiet =>
      -- Stack effect: ... slice bits -- ...
      -- Bits may be 0..257 for signed, 0..256 for unsigned (per C++ pop_smallint_range).
      let maxBits : Nat := if unsigned then 256 else 257
      let bits ← VM.popNatUpTo maxBits
      let s ← VM.popSlice
      if s.haveBits bits then
        let bs := s.readBits bits
        let n : Int :=
          if unsigned then
            Int.ofNat (bitsToNat bs)
          else
            bitsToIntSignedTwos bs
        VM.pushIntQuiet (.num n) false
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .ldref =>
      let s ← VM.popSlice
      if s.haveRefs 1 then
        let c := s.cell.refs[s.refPos]!
        VM.push (.cell c)
        VM.push (.slice { s with refPos := s.refPos + 1 })
      else
        throw .cellUnd
  | .ldrefRtos =>
      let s ← VM.popSlice
      if s.haveRefs 1 then
        let c := s.cell.refs[s.refPos]!
        let s' := { s with refPos := s.refPos + 1 }
        -- C++ `LDREFRTOS` uses `load_cell_slice_ref`, which charges a cell load/reload.
        modify fun st => st.registerCellLoad c
        VM.push (.slice s')
        VM.push (.slice (Slice.ofCell c))
      else
        throw .cellUnd
  | .pldRefIdx idx =>
      let s ← VM.popSlice
      if s.haveRefs (idx + 1) then
        let pos := s.refPos + idx
        if pos < s.cell.refs.size then
          let c := s.cell.refs[pos]!
          VM.push (.cell c)
        else
          throw .cellUnd
      else
        throw .cellUnd
  | .loadSliceX prefetch quiet =>
      let bits ← VM.popNatUpTo 1023
      let s ← VM.popSlice
      if s.haveBits bits then
        let subBits := s.readBits bits
        let subCell : Cell := Cell.mkOrdinary subBits #[]
        VM.push (.slice (Slice.ofCell subCell))
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .loadSliceFixed prefetch quiet bits =>
      let s ← VM.popSlice
      if s.haveBits bits then
        let subBits := s.readBits bits
        let subCell : Cell := Cell.mkOrdinary subBits #[]
        VM.push (.slice (Slice.ofCell subCell))
        if !prefetch then
          VM.push (.slice (s.advanceBits bits))
        if quiet then
          VM.pushSmallInt (-1)
      else
        if quiet then
          if !prefetch then
            VM.push (.slice s)
          VM.pushSmallInt 0
        else
          throw .cellUnd
  | .sti bits =>
      if bits == 0 then
        throw .rangeChk
      -- Match C++ operand order for `STI`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          match intToBitsTwos n bits with
          | .ok bs => VM.push (.builder (b.storeBits bs))
          | .error e => throw e
  | .stu bits =>
      if bits == 0 then
        throw .rangeChk
      -- Match C++ operand order for `STU`: builder is on top, integer is below.
      let b ← VM.popBuilder
      let x ← VM.popInt
      if !b.canExtendBy bits then
        throw .cellOv
      match x with
      | .nan => throw .rangeChk
      | .num n =>
          if decide (n < 0 ∨ n ≥ intPow2 bits) then
            throw .rangeChk
          let bs := natToBits n.toNat bits
          VM.push (.builder (b.storeBits bs))
  | .stIntVar unsigned rev quiet =>
      let maxBits : Nat := if unsigned then 256 else 257
      let bits ← VM.popNatUpTo maxBits
      let (x, b) ←
        if rev then
          let x ← VM.popInt
          let b ← VM.popBuilder
          pure (x, b)
        else
          let b ← VM.popBuilder
          let x ← VM.popInt
          pure (x, b)

      if !b.canExtendBy bits then
        if quiet then
          if rev then
            VM.push (.builder b)
            VM.push (.int x)
          else
            VM.push (.int x)
            VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
      else
        let fits : Bool :=
          match x with
          | .nan => false
          | .num n =>
              if bits = 0 then
                n = 0
              else if unsigned then
                decide (0 ≤ n ∧ n < intPow2 bits)
              else
                intSignedFitsBits n bits
        if !fits then
          if quiet then
            if rev then
              VM.push (.builder b)
              VM.push (.int x)
            else
              VM.push (.int x)
              VM.push (.builder b)
            VM.pushSmallInt 1
          else
            throw .rangeChk
        else
          match x with
          | .nan =>
              -- unreachable due to `fits` check
              throw .rangeChk
          | .num n =>
              let bs : BitString ←
                if unsigned then
                  pure (natToBits n.toNat bits)
                else
                  match intToBitsTwos n bits with
                  | .ok bs => pure bs
                  | .error e => throw e
              VM.push (.builder (b.storeBits bs))
              if quiet then
                VM.pushSmallInt 0
  | .stIntFixed unsigned rev quiet bits =>
      let (x, b) ←
        if rev then
          let x ← VM.popInt
          let b ← VM.popBuilder
          pure (x, b)
        else
          let b ← VM.popBuilder
          let x ← VM.popInt
          pure (x, b)

      if !b.canExtendBy bits then
        if quiet then
          if rev then
            VM.push (.builder b)
            VM.push (.int x)
          else
            VM.push (.int x)
            VM.push (.builder b)
          VM.pushSmallInt (-1)
        else
          throw .cellOv
      else
        let fits : Bool :=
          match x with
          | .nan => false
          | .num n =>
              if bits = 0 then
                n = 0
              else if unsigned then
                decide (0 ≤ n ∧ n < intPow2 bits)
              else
                intSignedFitsBits n bits
        if !fits then
          if quiet then
            if rev then
              VM.push (.builder b)
              VM.push (.int x)
            else
              VM.push (.int x)
              VM.push (.builder b)
            VM.pushSmallInt 1
          else
            throw .rangeChk
        else
          match x with
          | .nan =>
              -- unreachable due to `fits` check
              throw .rangeChk
          | .num n =>
              let bs : BitString ←
                if unsigned then
                  pure (natToBits n.toNat bits)
                else
                  match intToBitsTwos n bits with
                  | .ok bs => pure bs
                  | .error e => throw e
              VM.push (.builder (b.storeBits bs))
              if quiet then
                VM.pushSmallInt 0
  | .stSlice rev quiet =>
      if rev then
        -- Stack: ... builder slice -- ...
        let s ← VM.popSlice
        let b ← VM.popBuilder
        let c := s.toCellRemaining
        if b.canExtendBy c.bits.size c.refs.size then
          let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder b)
            VM.push (.slice s)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
      else
        -- Stack: ... slice builder -- ...
        let b ← VM.popBuilder
        let s ← VM.popSlice
        let c := s.toCellRemaining
        if b.canExtendBy c.bits.size c.refs.size then
          let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.slice s)
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
  | .stb rev quiet =>
      -- Matches C++ `exec_store_builder(_rev)` (cellops.cpp).
      if rev then
        -- Stack: ... builder cb2 -- ...  (cb2 on top)
        let cb2 ← VM.popBuilder
        let b ← VM.popBuilder
        if b.canExtendBy cb2.bits.size cb2.refs.size then
          let b' : Builder := { bits := b.bits ++ cb2.bits, refs := b.refs ++ cb2.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder b)
            VM.push (.builder cb2)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
      else
        -- Stack: ... cb2 builder -- ...  (builder on top)
        let b ← VM.popBuilder
        let cb2 ← VM.popBuilder
        if b.canExtendBy cb2.bits.size cb2.refs.size then
          let b' : Builder := { bits := b.bits ++ cb2.bits, refs := b.refs ++ cb2.refs }
          VM.push (.builder b')
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder cb2)
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
  | .stbRef rev quiet =>
      -- Matches C++ `exec_store_builder_as_ref(_rev)` (cellops.cpp).
      if rev then
        -- Stack: ... builder cb2 -- ...  (cb2 on top)
        let cb2 ← VM.popBuilder
        let b ← VM.popBuilder
        if b.canExtendBy 0 1 then
          modify fun st => st.consumeGas cellCreateGasPrice
          let c : Cell := cb2.finalize
          VM.push (.builder { b with refs := b.refs.push c })
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder b)
            VM.push (.builder cb2)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
      else
        -- Stack: ... cb2 builder -- ...  (builder on top)
        let b ← VM.popBuilder
        let cb2 ← VM.popBuilder
        if b.canExtendBy 0 1 then
          modify fun st => st.consumeGas cellCreateGasPrice
          let c : Cell := cb2.finalize
          VM.push (.builder { b with refs := b.refs.push c })
          if quiet then
            VM.pushSmallInt 0
        else
          if quiet then
            VM.push (.builder cb2)
            VM.push (.builder b)
            VM.pushSmallInt (-1)
          else
            throw .cellOv
  | .stref =>
      -- Stack: ... cell builder -- ...  (builder on top)
      let b ← VM.popBuilder
      let c ← VM.popCell
      if b.canExtendBy 0 1 then
        VM.push (.builder { b with refs := b.refs.push c })
      else
        throw .cellOv
  | .bbits =>
      let b ← VM.popBuilder
      VM.pushSmallInt (Int.ofNat b.bits.size)
  | .stSliceConst sConst =>
      let b ← VM.popBuilder
      let c := sConst.toCellRemaining
      if b.canExtendBy c.bits.size c.refs.size then
        let b' : Builder := { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
        VM.push (.builder b')
      else
        throw .cellOv
  | .stZeroes =>
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits false)))
      else
        throw .cellOv
  | .stOnes =>
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits true)))
      else
        throw .cellOv
  | .stSame =>
      let vNat ← VM.popNatUpTo 1
      let bits ← VM.popNatUpTo 1023
      let b ← VM.popBuilder
      if b.canExtendBy bits then
        VM.push (.builder (b.storeBits (Array.replicate bits (vNat == 1))))
      else
        throw .cellOv
  | _ => next

end TvmLean
