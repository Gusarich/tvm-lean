import Std
import TvmLean.Core

namespace TvmLean

/-! Minimal Bag-of-Cells (BOC) deserialization (Milestone 2 “fast path”).

This is an **untrusted input layer**: it is executable engineering code, not formally verified yet.
Supported: `serialized_boc` (0xb5ee9c72) and the legacy idx formats (0x68ff65f3 / 0xacc3a728), with optional CRC32C.
We intentionally reject exotic/special cells, absent cells, and non-zero level masks for now.
-/

inductive BocError : Type
  | invalid (msg : String)
  deriving Repr

instance : ToString BocError := ⟨fun
  | .invalid msg => msg⟩

abbrev BocM := Except BocError

def bocFail (msg : String) : BocM α :=
  .error (.invalid msg)

def readNatBE (ba : ByteArray) (off len : Nat) : BocM Nat := do
  if off + len > ba.size then
    bocFail s!"BOC: unexpected EOF while reading {len} bytes at offset {off}"
  let mut acc : Nat := 0
  for i in [0:len] do
    acc := (acc <<< 8) + (ba.get! (off + i)).toNat
  return acc

def readNatLE (ba : ByteArray) (off len : Nat) : BocM Nat := do
  if off + len > ba.size then
    bocFail s!"BOC: unexpected EOF while reading {len} bytes at offset {off}"
  let mut acc : Nat := 0
  for i in [0:len] do
    acc := acc + ((ba.get! (off + i)).toNat <<< (8 * i))
  return acc

def popcount3 (n : Nat) : Nat :=
  (if (n &&& 1) = 1 then 1 else 0) +
  (if (n &&& 2) = 2 then 1 else 0) +
  (if (n &&& 4) = 4 then 1 else 0)

structure BocHeader where
  magic : Nat
  hasIndex : Bool
  hasCrc32c : Bool
  hasCacheBits : Bool
  refByteSize : Nat
  offsetByteSize : Nat
  cellCount : Nat
  rootCount : Nat
  absentCount : Nat
  rootsOffset : Nat
  indexOffset : Nat
  dataOffset : Nat
  dataSize : Nat
  totalSize : Nat
  deriving Repr

def BocHeader.magicGeneric : Nat := 0xb5ee9c72
def BocHeader.magicIdx : Nat := 0x68ff65f3
def BocHeader.magicIdxCrc32c : Nat := 0xacc3a728

def parseBocHeader (data : ByteArray) : BocM BocHeader := do
  if data.size < 6 then
    bocFail "BOC: too short"
  let magic ← readNatBE data 0 4
  let flags := (data.get! 4).toNat
  let isGeneric := magic = BocHeader.magicGeneric
  let hasIndex : Bool := if isGeneric then ((flags >>> 7) &&& 1) = 1 else true
  let hasCrc32c : Bool := if isGeneric then ((flags >>> 6) &&& 1) = 1 else magic = BocHeader.magicIdxCrc32c
  let hasCacheBits : Bool := if isGeneric then ((flags >>> 5) &&& 1) = 1 else false
  let refByteSize : Nat := flags &&& 7
  if !(magic = BocHeader.magicGeneric ∨ magic = BocHeader.magicIdx ∨ magic = BocHeader.magicIdxCrc32c) then
    bocFail s!"BOC: invalid magic 0x{magic.toDigits 16}"
  if hasCacheBits && !hasIndex then
    bocFail "BOC: cache bits require index table"
  if refByteSize = 0 ∨ refByteSize > 4 then
    bocFail s!"BOC: invalid ref byte size {refByteSize}"
  let offsetByteSize : Nat := (data.get! 5).toNat
  if offsetByteSize = 0 ∨ offsetByteSize > 8 then
    bocFail s!"BOC: invalid offset byte size {offsetByteSize}"

  let rootsOffset : Nat := 6 + 3 * refByteSize + offsetByteSize
  let cellCount ← readNatBE data 6 refByteSize
  let rootCount ← readNatBE data (6 + refByteSize) refByteSize
  let absentCount ← readNatBE data (6 + 2 * refByteSize) refByteSize
  let dataSize ← readNatBE data (6 + 3 * refByteSize) offsetByteSize

  if cellCount = 0 then
    bocFail "BOC: cell_count must be > 0"
  if rootCount = 0 then
    bocFail "BOC: root_count must be > 0"

  if (!isGeneric) && rootCount ≠ 1 then
    bocFail "BOC: idx-form BOC must have exactly one root"

  let indexOffset : Nat :=
    if isGeneric then
      rootsOffset + rootCount * refByteSize
    else
      rootsOffset
  let dataOffset : Nat :=
    if hasIndex then
      indexOffset + cellCount * offsetByteSize
    else
      indexOffset

  let totalSize : Nat := dataOffset + dataSize + (if hasCrc32c then 4 else 0)
  if totalSize > data.size then
    bocFail s!"BOC: declared size {totalSize} exceeds buffer size {data.size}"
  if dataSize > (cellCount <<< 10) then
    bocFail "BOC: declared cell data too large"
  if dataSize < cellCount * (2 + refByteSize) - refByteSize then
    bocFail "BOC: too many cells for declared cell data size"

  return {
    magic, hasIndex, hasCrc32c, hasCacheBits
    refByteSize, offsetByteSize
    cellCount, rootCount, absentCount
    rootsOffset, indexOffset, dataOffset, dataSize, totalSize
  }

def crc32c (data : ByteArray) : UInt32 :=
  -- Simple (table-less) CRC32C / Castagnoli.
  -- Polynomial (reversed): 0x82F63B78.
  Id.run do
    let mut crc : UInt32 := 0xffffffff
    for i in [0:data.size] do
      crc := crc ^^^ (UInt32.ofNat (data.get! i).toNat)
      for _ in [0:8] do
        if (crc &&& 1) = 1 then
          crc := (crc >>> 1) ^^^ 0x82f63b78
        else
          crc := crc >>> 1
    return ~~~crc

def verifyCrc32c (data : ByteArray) (h : BocHeader) : BocM Unit := do
  if h.hasCrc32c then
    if h.totalSize < 4 then
      bocFail "BOC: invalid size for CRC32C"
    let stored ← readNatLE data (h.totalSize - 4) 4
    let computed := (crc32c (data.extract 0 (h.totalSize - 4))).toNat
    if stored ≠ computed then
      bocFail s!"BOC: CRC32C mismatch"
  else
    pure ()

structure CellSerInfo where
  refsCnt : Nat
  special : Bool
  withHashes : Bool
  levelMask : Nat
  dataOffset : Nat
  dataLen : Nat
  dataWithBits : Bool
  refsOffset : Nat
  endOffset : Nat
  deriving Repr

def parseCellSerInfo (cellBytes : ByteArray) (refByteSize : Nat) : BocM CellSerInfo := do
  if cellBytes.size < 2 then
    bocFail "BOC: cell too short"
  let d1 := (cellBytes.get! 0).toNat
  let d2 := (cellBytes.get! 1).toNat
  let refsCnt := d1 &&& 7
  let levelMask := d1 >>> 5
  let special := ((d1 >>> 3) &&& 1) = 1
  let withHashes := ((d1 >>> 4) &&& 1) = 1
  if refsCnt > 4 then
    bocFail "BOC: absent cells not supported"
  let hashesCount := popcount3 levelMask + 1
  let hashesBytes : Nat := if withHashes then hashesCount * 32 else 0
  let depthBytes : Nat := if withHashes then hashesCount * 2 else 0
  let dataOffset := 2 + hashesBytes + depthBytes
  let dataLen := (d2 >>> 1) + (d2 &&& 1)
  let dataWithBits := (d2 &&& 1) = 1
  let refsOffset := dataOffset + dataLen
  let endOffset := refsOffset + refsCnt * refByteSize
  return {
    refsCnt, special, withHashes, levelMask
    dataOffset, dataLen, dataWithBits
    refsOffset, endOffset
  }

def cellSerializedSize (cellBytes : ByteArray) (refByteSize : Nat) : BocM Nat := do
  let info ← parseCellSerInfo cellBytes refByteSize
  if info.endOffset > cellBytes.size then
    bocFail "BOC: cell truncated"
  return info.endOffset

def parseCellBytes
    (cellBytes : ByteArray)
    (refByteSize : Nat)
    (cellsRev : Array Cell)
    (revIdx : Nat)
    (cellCount : Nat) : BocM Cell := do
  let info ← parseCellSerInfo cellBytes refByteSize
  if info.special then
    bocFail "BOC: special/exotic cells not supported (Milestone 2 fast-path)"
  if info.levelMask ≠ 0 then
    bocFail "BOC: non-zero level mask not supported (Milestone 2 fast-path)"
  if info.endOffset ≠ cellBytes.size then
    bocFail "BOC: unused space in cell serialization"

  let bits : Nat ←
    if info.dataWithBits then
      if info.dataLen = 0 then
        bocFail "BOC: invalid cell encoding (data_with_bits but data_len=0)"
      else
        let last := (cellBytes.get! (info.dataOffset + info.dataLen - 1)).toNat
        if (last &&& 0x7f) = 0 then
          bocFail "BOC: overlong cell encoding"
        else
          let mut tz : Nat := 0
          while tz < 8 && (((last >>> tz) &&& 1) = 0) do
            tz := tz + 1
          pure ((info.dataLen - 1) * 8 + 7 - tz)
    else
      pure (info.dataLen * 8)
  if bits > 1023 then
    bocFail "BOC: cell bitstring too large"

  let dataBytes := cellBytes.extract info.dataOffset (info.dataOffset + info.dataLen)
  let bs : BitString :=
    Array.ofFn (n := bits) fun i =>
      let p := i.1
      let b := (dataBytes.get! (p / 8)).toNat
      let k := 7 - (p % 8)
      ((b >>> k) &&& 1) = 1

  let idx : Nat := cellCount - 1 - revIdx
  let mut refs : Array Cell := #[]
  for k in [0:info.refsCnt] do
    let refIdx ← readNatBE cellBytes (info.refsOffset + k * refByteSize) refByteSize
    if refIdx ≥ cellCount then
      bocFail "BOC: reference index out of range"
    if refIdx ≤ idx then
      bocFail "BOC: reference points to an earlier cell"
    let refRevIdx := cellCount - 1 - refIdx
    if refRevIdx ≥ revIdx then
      bocFail "BOC: forward reference"
    refs := refs.push (cellsRev[refRevIdx]!)

  return { bits := bs, refs := refs }

def stdBocDeserializeMulti (data : ByteArray) (maxRoots : Nat := 4) : BocM (Array Cell) := do
  if data.size = 0 then
    return #[]
  let h ← parseBocHeader data
  if h.rootCount > maxRoots then
    bocFail "BOC: too many roots"
  if h.absentCount ≠ 0 then
    bocFail "BOC: absent cells not supported (Milestone 2 fast-path)"
  verifyCrc32c data h

  let isGeneric := h.magic = BocHeader.magicGeneric
  let mut roots : Array Nat := #[]
  if isGeneric then
    for i in [0:h.rootCount] do
      let idx ← readNatBE data (h.rootsOffset + i * h.refByteSize) h.refByteSize
      if idx ≥ h.cellCount then
        bocFail "BOC: invalid root index"
      roots := roots.push idx
  else
    roots := #[0]

  let cellData := data.extract h.dataOffset (h.dataOffset + h.dataSize)
  let mut indexEntries : Array Nat := #[]
  if h.hasIndex then
    for i in [0:h.cellCount] do
      let raw ← readNatBE data (h.indexOffset + i * h.offsetByteSize) h.offsetByteSize
      let offs := if h.hasCacheBits then raw / 2 else raw
      indexEntries := indexEntries.push offs
  else
    let mut offs : Nat := 0
    for _ in [0:h.cellCount] do
      let remaining := cellData.extract offs cellData.size
      let sz ← cellSerializedSize remaining h.refByteSize
      offs := offs + sz
      indexEntries := indexEntries.push offs
    if offs ≠ cellData.size then
      bocFail "BOC: cell data size mismatch"

  if indexEntries.size ≠ h.cellCount then
    bocFail "BOC: index size mismatch"
  if h.cellCount > 0 then
    let last := indexEntries[h.cellCount - 1]!
    if last ≠ cellData.size then
      bocFail "BOC: invalid index table"

  let mut cellsRev : Array Cell := Array.replicate h.cellCount Cell.empty
  for revIdx in [0:h.cellCount] do
    let idx := h.cellCount - 1 - revIdx
    let start := if idx = 0 then 0 else indexEntries[idx - 1]!
    let stop := indexEntries[idx]!
    if stop < start ∨ stop > cellData.size then
      bocFail "BOC: invalid index table"
    let cellBytes := cellData.extract start stop
    let cell ← parseCellBytes cellBytes h.refByteSize cellsRev revIdx h.cellCount
    cellsRev := cellsRev.set! revIdx cell

  let mut out : Array Cell := #[]
  for r in roots do
    if r ≥ h.cellCount then
      bocFail "BOC: root index out of range"
    let rev := h.cellCount - 1 - r
    out := out.push (cellsRev[rev]!)
  return out

def stdBocDeserialize (data : ByteArray) : BocM Cell := do
  let roots ← stdBocDeserializeMulti data 1
  if roots.size ≠ 1 then
    bocFail "BOC: expected exactly one root"
  return roots[0]!

end TvmLean
