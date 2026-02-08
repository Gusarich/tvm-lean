import TvmLean.Model.Basics.Bytes

namespace TvmLean

structure Cell where
  bits : BitString
  refs : Array Cell
  -- `special=true` means "exotic cell" in TON terminology.
  -- See TON Docs "Cells" + C++ `vm::DataCell` validation rules.
  special : Bool
  -- 3-bit level mask (0..7), as in TON `vm::Cell::LevelMask`.
  levelMask : Nat
  deriving Repr

inductive CellSpecialType where
  | ordinary
  | prunedBranch
  | library
  | merkleProof
  | merkleUpdate
  deriving Repr, DecidableEq

def CellSpecialType.ofByte? (b : Nat) : Option CellSpecialType :=
  match b with
  | 0 => some .ordinary
  | 1 => some .prunedBranch
  | 2 => some .library
  | 3 => some .merkleProof
  | 4 => some .merkleUpdate
  | _ => none

def Cell.maxLevel : Nat := 3

def LevelMask.getLevel (m : Nat) : Nat :=
  if m = 0 then 0 else Nat.log2 m + 1

def LevelMask.shiftRight (m : Nat) : Nat :=
  m >>> 1

def LevelMask.apply (m : Nat) (level : Nat) : Nat :=
  -- `mask & ((1<<level)-1)`; for level=0 this is always 0.
  if level = 0 then
    0
  else
    m &&& ((1 <<< level) - 1)

def LevelMask.isSignificant (m : Nat) (level : Nat) : Bool :=
  level = 0 || (((m >>> (level - 1)) &&& 1) = 1)

def LevelMask.popcount3 (m : Nat) : Nat :=
  (if (m &&& 1) = 1 then 1 else 0) +
  (if (m &&& 2) = 2 then 1 else 0) +
  (if (m &&& 4) = 4 then 1 else 0)

def LevelMask.getHashI (m : Nat) : Nat :=
  LevelMask.popcount3 m

def LevelMask.getHashesCount (m : Nat) : Nat :=
  LevelMask.getHashI m + 1

def Cell.computeOrdinaryLevelMask (refs : Array Cell) : Nat :=
  refs.foldl (fun acc r => acc ||| r.levelMask) 0

def Cell.mkOrdinary (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  { bits := bits, refs := refs, special := false, levelMask := Cell.computeOrdinaryLevelMask refs }

def Cell.empty : Cell :=
  Cell.mkOrdinary #[] #[]

instance : Inhabited Cell := ⟨Cell.empty⟩

partial def Cell.beq (a b : Cell) : Bool :=
  a.special == b.special &&
    a.levelMask == b.levelMask &&
      a.bits == b.bits &&
        a.refs.size == b.refs.size &&
          Id.run do
            let mut ok := true
            for i in [0:a.refs.size] do
              if !(Cell.beq a.refs[i]! b.refs[i]!) then
                ok := false
            return ok

instance : BEq Cell := ⟨Cell.beq⟩

def Cell.ofUInt (bits : Nat) (n : Nat) : Cell :=
  Cell.mkOrdinary (natToBits n bits) #[]

def Cell.depthLe (c : Cell) : Nat → Bool
  | 0 => false
  | limit + 1 =>
      c.refs.all (fun r => r.depthLe limit)

def bitsToByte (bs : BitString) (start len : Nat) : UInt8 :=
  Id.run do
    let mut acc : Nat := 0
    for j in [0:len] do
      if bs[start + j]! then
        acc := acc ||| (1 <<< (7 - j))
    UInt8.ofNat acc

def bitsToPaddedLastByte (bs : BitString) (start usedBits : Nat) : UInt8 :=
  -- `usedBits` ∈ {1..7}: data bits in the high bits, then a single `1` tag bit, then zeros.
  Id.run do
    let mut acc : Nat := 0
    for j in [0:usedBits] do
      if bs[start + j]! then
        acc := acc ||| (1 <<< (7 - j))
    acc := acc ||| (1 <<< (7 - usedBits))
    UInt8.ofNat acc

def bytesToNatBE (bs : Array UInt8) : Nat :=
  bs.foldl (fun acc b => (acc <<< 8) + b.toNat) 0

def bytesToNatLE (bs : Array UInt8) : Nat :=
  Id.run do
    let mut acc : Nat := 0
    let mut shift : Nat := 0
    for b in bs do
      acc := acc + (b.toNat <<< shift)
      shift := shift + 8
    return acc

def byteArrayToNatBE (bs : ByteArray) : Nat :=
  Id.run do
    let mut acc : Nat := 0
    for i in [0:bs.size] do
      acc := (acc <<< 8) + (bs.get! i).toNat
    return acc

structure BitByteAcc where
  bytes : Array UInt8 := #[]
  cur : Nat := 0
  curLen : Nat := 0
  deriving Repr

def BitByteAcc.empty : BitByteAcc := {}

def BitByteAcc.appendBit (acc : BitByteAcc) (b : Bool) : BitByteAcc :=
  let cur :=
    if b then
      acc.cur ||| (1 <<< (7 - acc.curLen))
    else
      acc.cur
  let curLen := acc.curLen + 1
  if curLen = 8 then
    { bytes := acc.bytes.push (UInt8.ofNat (cur &&& 0xff)), cur := 0, curLen := 0 }
  else
    { acc with cur, curLen }

def BitByteAcc.appendBits (acc : BitByteAcc) (bs : BitString) : BitByteAcc :=
  Id.run do
    let mut a := acc
    for b in bs do
      a := a.appendBit b
    return a

def BitByteAcc.finish (acc : BitByteAcc) : Except Excno (Array UInt8) := do
  if acc.curLen = 0 then
    return acc.bytes
  else
    throw .cellUnd

def natToBytesBEFixed (n : Nat) (len : Nat) : Array UInt8 :=
  Array.ofFn (n := len) fun i =>
    let shift := (len - 1 - i.1) * 8
    UInt8.ofNat ((n >>> shift) &&& 0xff)

def bitStringToBytesBE (bs : BitString) : Array UInt8 :=
  -- Mirrors `td::BitSliceWrite{buffer, bytes*8} = prefetch_bits(bytes*8)` used by `CellSlice::prefetch_bytes`.
  -- Bit order: first bit is the MSB of the first byte.
  Id.run do
    let bytes : Nat := bs.size / 8
    let mut out : Array UInt8 := #[]
    for i in [0:bytes] do
      out := out.push (bitsToByte bs (i * 8) 8)
    out

def uint256Limit : Nat := 1 <<< 256

def exportUInt256BE (x : IntVal) : Except Excno (Array UInt8) := do
  match x with
  | .nan => throw .rangeChk
  | .num n =>
      if n < 0 then
        throw .rangeChk
      let u : Nat := n.toNat
      if u ≥ uint256Limit then
        throw .rangeChk
      return natToBytesBEFixed u 32

structure CellLevelInfo where
  ty : CellSpecialType
  levelMask : Nat
  effectiveLevel : Nat
  depths : Array Nat
  hashes : Array (Array UInt8)
  deriving Repr

def CellLevelInfo.clampLevel (info : CellLevelInfo) (level : Nat) : Nat :=
  Nat.min info.effectiveLevel (Nat.min Cell.maxLevel level)

def CellLevelInfo.getDepth (info : CellLevelInfo) (level : Nat) : Nat :=
  info.depths[info.clampLevel level]!

def CellLevelInfo.getHash (info : CellLevelInfo) (level : Nat) : Array UInt8 :=
  info.hashes[info.clampLevel level]!

def readDepthBE (data : Array UInt8) (off : Nat) : Except String Nat := do
  if off + 2 > data.size then
    throw "depth read out of bounds"
  return ((data[off]!.toNat <<< 8) + data[off + 1]!.toNat)

partial def Cell.computeLevelInfo? (c : Cell) : Except String CellLevelInfo := do
  if c.refs.size > 4 then
    throw "Too many references"
  if c.bits.size > 1023 then
    throw "Too many data bits"

  let mut childInfos : Array CellLevelInfo := #[]
  for r in c.refs do
    childInfos := childInfos.push (← Cell.computeLevelInfo? r)

  let ty : CellSpecialType ←
    if !c.special then
      pure .ordinary
    else
      if c.bits.size < 8 then
        throw "Not enough data for a special cell"
      let tyByte := bitsToNat (c.bits.take 8)
      match CellSpecialType.ofByte? tyByte with
      | some .ordinary => throw "Invalid special cell type"
      | some t => pure t
      | none => throw "Invalid special cell type"

  let maxLevel : Nat := Cell.maxLevel
  let mut levelMask : Nat := 0
  let mut depths : Array Nat := Array.replicate (maxLevel + 1) 0

  let mut prunedBytes : Option (Array UInt8) := none
  let mut prunedHashesCount : Nat := 0

  match ty with
  | .ordinary =>
      for ci in childInfos do
        levelMask := levelMask ||| ci.levelMask
        for lvl in [0:maxLevel + 1] do
          let d := ci.getDepth lvl
          if d > depths[lvl]! then
            depths := depths.set! lvl d
      if c.refs.size != 0 then
        depths := depths.map (fun d => d + 1)
  | .prunedBranch =>
      if c.refs.size != 0 then
        throw "Pruned branch cannot have references"
      if c.bits.size < 16 then
        throw "Length mismatch in a pruned branch"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a pruned branch"
      let bytes := bitStringToBytesBE c.bits
      prunedBytes := some bytes
      if bytes.size < 2 then
        throw "Not enough data for a special cell"
      levelMask := bytes[1]!.toNat
      let lvl := LevelMask.getLevel levelMask
      if lvl = 0 || lvl > maxLevel then
        throw "Invalid level mask in a pruned branch"
      prunedHashesCount := LevelMask.getHashI levelMask
      let expectedBytes : Nat := 2 + prunedHashesCount * (32 + 2)
      if bytes.size != expectedBytes then
        throw "Length mismatch in a pruned branch"
      -- depth[maxLevel] = 0
      for off in [0:maxLevel] do
        let i := maxLevel - 1 - off
        if LevelMask.isSignificant levelMask (i + 1) then
          let hashesBefore := LevelMask.getHashI (LevelMask.apply levelMask i)
          let depthOff := 2 + prunedHashesCount * 32 + hashesBefore * 2
          let d ← readDepthBE bytes depthOff
          depths := depths.set! i d
        else
          depths := depths.set! i (depths[i + 1]!)
  | .library =>
      if c.refs.size != 0 then
        throw "Library cell cannot have references"
      if c.bits.size != 8 * (1 + 32) then
        throw "Length mismatch in a library cell"
      levelMask := 0
      depths := Array.replicate (maxLevel + 1) 0
  | .merkleProof =>
      if c.refs.size != 1 then
        throw "Merkle proof must have exactly one reference"
      if c.bits.size != 8 * (1 + 32 + 2) then
        throw "Length mismatch in a Merkle proof"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a Merkle proof"
      let bytes := bitStringToBytesBE c.bits
      let child ←
        match childInfos[0]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child)"
      let storedHash := bytes.extract 1 (1 + 32)
      if storedHash != child.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedDepth ← readDepthBE bytes (1 + 32)
      if storedDepth != child.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      for lvl in [0:maxLevel + 1] do
        let childLevel := Nat.min maxLevel (lvl + 1)
        depths := depths.set! lvl (Nat.max depths[lvl]! (child.getDepth childLevel + 1))
      levelMask := LevelMask.shiftRight child.levelMask
  | .merkleUpdate =>
      if c.refs.size != 2 then
        throw "Merkle update must have exactly two references"
      if c.bits.size != 8 * (1 + (32 + 2) * 2) then
        throw "Length mismatch in a Merkle update"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a Merkle update"
      let bytes := bitStringToBytesBE c.bits
      let c0 ←
        match childInfos[0]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child 0)"
      let c1 ←
        match childInfos[1]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child 1)"
      let storedHash0 := bytes.extract 1 (1 + 32)
      if storedHash0 != c0.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedHash1 := bytes.extract (1 + 32) (1 + 2 * 32)
      if storedHash1 != c1.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedDepth0 ← readDepthBE bytes (1 + 2 * 32)
      if storedDepth0 != c0.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      let storedDepth1 ← readDepthBE bytes (1 + 2 * 32 + 2)
      if storedDepth1 != c1.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      for lvl in [0:maxLevel + 1] do
        let childLevel := Nat.min maxLevel (lvl + 1)
        depths := depths.set! lvl (Nat.max depths[lvl]! (c0.getDepth childLevel + 1))
        depths := depths.set! lvl (Nat.max depths[lvl]! (c1.getDepth childLevel + 1))
      levelMask := LevelMask.shiftRight (c0.levelMask ||| c1.levelMask)

  if c.levelMask != levelMask then
    throw "level mask mismatch"

  let effectiveLevel := LevelMask.getLevel levelMask
  if effectiveLevel > maxLevel then
    throw "Invalid level mask"

  let zeroHash : Array UInt8 := Array.replicate 32 0
  let mut hashes : Array (Array UInt8) := Array.replicate (maxLevel + 1) zeroHash
  let mut lastComputed : Option Nat := none

  let isMerkleNode : Bool := ty == .merkleProof || ty == .merkleUpdate

  for lvl in [0:maxLevel + 1] do
    let shouldCompute : Bool :=
      lvl == maxLevel || LevelMask.isSignificant levelMask (lvl + 1)
    if !shouldCompute then
      continue

    let h : Array UInt8 ←
      match ty, prunedBytes with
      | .prunedBranch, some bytes =>
          if lvl != maxLevel then
            let hashesBefore := LevelMask.getHashI (LevelMask.apply levelMask lvl)
            let off := 2 + hashesBefore * 32
            if off + 32 > bytes.size then
              throw "Length mismatch in a pruned branch"
            pure (bytes.extract off (off + 32))
          else
            -- computed below as an ordinary hash (no chaining for pruned branches)
            pure #[] -- placeholder, overwritten below
      | _, _ =>
          pure #[] -- placeholder, overwritten below

    let h :=
      if h.isEmpty then
        let refsCnt : Nat := c.refs.size
        let bitLen : Nat := c.bits.size
        let fullBytes : Nat := bitLen / 8
        let remBits : Nat := bitLen % 8
        let d1 : Nat :=
          refsCnt +
            (if c.special then 8 else 0) +
              (LevelMask.apply levelMask lvl <<< 5)
        let d2 : Nat := (fullBytes <<< 1) + (if remBits = 0 then 0 else 1)
        Id.run do
          let mut msg : Array UInt8 := #[UInt8.ofNat d1, UInt8.ofNat d2]
          match lastComputed with
          | some last =>
              if ty != .prunedBranch then
                msg := msg ++ hashes[last]!
              else
                -- pruned branch: no chaining; always hash original data
                for i in [0:fullBytes] do
                  msg := msg.push (bitsToByte c.bits (i * 8) 8)
                if remBits ≠ 0 then
                  msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)
          | none =>
              for i in [0:fullBytes] do
                msg := msg.push (bitsToByte c.bits (i * 8) 8)
              if remBits ≠ 0 then
                msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)

          let childLevel : Nat := if isMerkleNode then Nat.min maxLevel (lvl + 1) else lvl
          for ci in childInfos do
            let d := ci.getDepth childLevel
            msg := msg.push (UInt8.ofNat ((d >>> 8) &&& 0xff))
            msg := msg.push (UInt8.ofNat (d &&& 0xff))
          for ci in childInfos do
            msg := msg ++ ci.getHash childLevel
          sha256Digest msg
      else
        h

    -- Store + fill gaps.
    let start : Nat :=
      match lastComputed with
      | none => 0
      | some last => last + 1
    for j in [start:lvl] do
      hashes := hashes.set! j h
    hashes := hashes.set! lvl h
    lastComputed := some lvl

  return { ty, levelMask, effectiveLevel, depths, hashes }

partial def Cell.depth (c : Cell) : Nat :=
  match c.computeLevelInfo? with
  | .ok info => info.getDepth Cell.maxLevel
  | .error _ => 0

partial def Cell.hashBytes (c : Cell) : Array UInt8 :=
  match c.computeLevelInfo? with
  | .ok info => info.getHash Cell.maxLevel
  | .error _ => Array.replicate 32 0

end TvmLean
