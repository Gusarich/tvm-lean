import TvmLean.Core.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellOp (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op =>
      match op with
      | .subslice =>
          let r2 ← VM.popNatUpTo 4
          let l2 ← VM.popNatUpTo 1023
          let r1 ← VM.popNatUpTo 4
          let l1 ← VM.popNatUpTo 1023
          let s ← VM.popSlice
          if !s.haveBits l1 || !s.haveRefs r1 then
            throw .cellUnd
          let s1 : Slice := { s with bitPos := s.bitPos + l1, refPos := s.refPos + r1 }
          if !s1.haveBits l2 || !s1.haveRefs r2 then
            throw .cellUnd
          let stop : Slice := { s1 with bitPos := s1.bitPos + l2, refPos := s1.refPos + r2 }
          let newCell : Cell := Slice.prefixCell s1 stop
          VM.push (.slice (Slice.ofCell newCell))
      | .split quiet =>
          let refs ← VM.popNatUpTo 4
          let bits ← VM.popNatUpTo 1023
          let s ← VM.popSlice
          if !s.haveBits bits || !s.haveRefs refs then
            if quiet then
              VM.push (.slice s)
              VM.pushSmallInt 0
            else
              throw .cellUnd
          else
            let stop : Slice := { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }
            let prefixCell : Cell := Slice.prefixCell s stop
            let sPrefix : Slice := Slice.ofCell prefixCell
            let sRest : Slice := { s with bitPos := s.bitPos + bits, refPos := s.refPos + refs }
            VM.push (.slice sPrefix)
            VM.push (.slice sRest)
            if quiet then
              VM.pushSmallInt (-1)
      | .pldRefVar =>
          let idx ← VM.popNatUpTo 3
          let s ← VM.popSlice
          if s.haveRefs (idx + 1) then
            VM.push (.cell (s.cell.refs[s.refPos + idx]!))
          else
            throw .cellUnd
      | .loadLeInt unsigned bytes prefetch quiet =>
          let s ← VM.popSlice
          let needBits : Nat := bytes * 8
          if !s.haveBits needBits then
            if quiet then
              if !prefetch then
                VM.push (.slice s)
              VM.pushSmallInt 0
            else
              throw .cellUnd
          else
            let b0 ←
              match s.prefetchBytesCellUnd bytes with
              | .ok v => pure v
              | .error e => throw e
            let u : Nat := bytesToNatLE b0
            let x : Int :=
              if unsigned then
                Int.ofNat u
              else
                natToIntSignedTwos u (bytes * 8)
            VM.pushIntQuiet (.num x) false
            if !prefetch then
              let s' : Slice := { s with bitPos := s.bitPos + needBits }
              VM.push (.slice s')
            if quiet then
              VM.pushSmallInt (-1)
      | .ldZeroes =>
          let s ← VM.popSlice
          let n := s.countLeading false
          let s' := if n > 0 then s.advanceBits n else s
          VM.pushSmallInt (Int.ofNat n)
          VM.push (.slice s')
      | .ldOnes =>
          let s ← VM.popSlice
          let n := s.countLeading true
          let s' := if n > 0 then s.advanceBits n else s
          VM.pushSmallInt (Int.ofNat n)
          VM.push (.slice s')
      | .ldSame =>
          let bNat ← VM.popNatUpTo 1
          let s ← VM.popSlice
          let b : Bool := bNat = 1
          let n := s.countLeading b
          let s' := if n > 0 then s.advanceBits n else s
          VM.pushSmallInt (Int.ofNat n)
          VM.push (.slice s')
      | .sdepth =>
          let s ← VM.popSlice
          VM.pushSmallInt (Int.ofNat s.cell.depth)
      | .clevel =>
          let c ← VM.popCell
          VM.pushSmallInt (Int.ofNat (LevelMask.getLevel c.levelMask))
      | .clevelMask =>
          let c ← VM.popCell
          VM.pushSmallInt (Int.ofNat c.levelMask)
      | .chashI i =>
          let c ← VM.popCell
          let info ←
            match c.computeLevelInfo? with
            | .ok v => pure v
            | .error _ => throw .cellUnd
          let h := info.getHash i
          let n := bytesToNatBE h
          VM.pushIntQuiet (.num (Int.ofNat n)) false
      | .cdepthI i =>
          let c ← VM.popCell
          let info ←
            match c.computeLevelInfo? with
            | .ok v => pure v
            | .error _ => throw .cellUnd
          VM.pushSmallInt (Int.ofNat (info.getDepth i))
      | .chashIX =>
          let i ← VM.popNatUpTo 3
          let c ← VM.popCell
          let info ←
            match c.computeLevelInfo? with
            | .ok v => pure v
            | .error _ => throw .cellUnd
          let h := info.getHash i
          let n := bytesToNatBE h
          VM.pushIntQuiet (.num (Int.ofNat n)) false
      | .cdepthIX =>
          let i ← VM.popNatUpTo 3
          let c ← VM.popCell
          let info ←
            match c.computeLevelInfo? with
            | .ok v => pure v
            | .error _ => throw .cellUnd
          VM.pushSmallInt (Int.ofNat (info.getDepth i))
      | .schkBits quiet =>
          let bits ← VM.popNatUpTo 1023
          let s ← VM.popSlice
          let ok : Bool := s.haveBits bits
          if quiet then
            VM.pushSmallInt (if ok then -1 else 0)
          else if !ok then
            throw .cellUnd
          else
            pure ()
      | .schkRefs quiet =>
          let refs ← VM.popNatUpTo 1023
          let s ← VM.popSlice
          let ok : Bool := s.haveRefs refs
          if quiet then
            VM.pushSmallInt (if ok then -1 else 0)
          else if !ok then
            throw .cellUnd
          else
            pure ()
      | .schkBitRefs quiet =>
          let refs ← VM.popNatUpTo 4
          let bits ← VM.popNatUpTo 1023
          let s ← VM.popSlice
          let ok : Bool := s.haveBits bits && s.haveRefs refs
          if quiet then
            VM.pushSmallInt (if ok then -1 else 0)
          else if !ok then
            throw .cellUnd
          else
            pure ()
      | .bdepth =>
          let b ← VM.popBuilder
          let mut d : Nat := 0
          for r in b.refs do
            d := Nat.max d (r.depth + 1)
          VM.pushSmallInt (Int.ofNat d)
      | .brefs =>
          let b ← VM.popBuilder
          VM.pushSmallInt (Int.ofNat b.refs.size)
      | .bbitrefs =>
          let b ← VM.popBuilder
          VM.pushSmallInt (Int.ofNat b.bits.size)
          VM.pushSmallInt (Int.ofNat b.refs.size)
      | .brembits =>
          let b ← VM.popBuilder
          VM.pushSmallInt (Int.ofNat (1023 - b.bits.size))
      | .bremrefs =>
          let b ← VM.popBuilder
          VM.pushSmallInt (Int.ofNat (4 - b.refs.size))
      | .brembitrefs =>
          let b ← VM.popBuilder
          VM.pushSmallInt (Int.ofNat (1023 - b.bits.size))
          VM.pushSmallInt (Int.ofNat (4 - b.refs.size))
      | .bchkBitsImm bits quiet =>
          let b ← VM.popBuilder
          let ok : Bool := b.canExtendBy bits
          if quiet then
            VM.pushSmallInt (if ok then -1 else 0)
          else if !ok then
            throw .cellOv
          else
            pure ()
      | .bchk needBits needRefs quiet =>
          let refs : Nat ← if needRefs then VM.popNatUpTo 7 else pure 0
          let bits : Nat ← if needBits then VM.popNatUpTo 1023 else pure 0
          let b ← VM.popBuilder
          let ok : Bool := b.canExtendBy bits refs
          if quiet then
            VM.pushSmallInt (if ok then -1 else 0)
          else if !ok then
            throw .cellOv
          else
            pure ()
  | _ => next

end TvmLean
