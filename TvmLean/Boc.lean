import Std
import TvmLean.Model
import TvmLean.Semantics

namespace TvmLean

/-! Minimal Bag-of-Cells (BOC) (de)serialization.

This is an **untrusted input layer**: it is executable engineering code, not formally verified yet.
Supported: `serialized_boc` (0xb5ee9c72) and the legacy idx formats (0x68ff65f3 / 0xacc3a728), with optional CRC32C.
We support exotic/special cells and non-zero level masks, and validate hashes/depths when `with_hashes` is present.
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
    bocFail "BOC: invalid cell reference count"
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

  let cell : Cell := { bits := bs, refs := refs, special := info.special, levelMask := info.levelMask }
  let infoComputed ←
    match cell.computeLevelInfo? with
    | .ok i => pure i
    | .error e => bocFail s!"BOC: invalid cell: {e}"

  if info.withHashes then
    let hashN : Nat := LevelMask.getHashesCount info.levelMask
    let hashesOffset : Nat := 2
    let depthOffset : Nat := hashesOffset + hashN * 32

    -- Top hash/depth (at effective level).
    let topHashOff : Nat := hashesOffset + 32 * (hashN - 1)
    let topDepthOff : Nat := depthOffset + 2 * (hashN - 1)
    let storedTopHash := cellBytes.extract topHashOff (topHashOff + 32)
    let computedTopHash : ByteArray := ByteArray.mk (infoComputed.getHash Cell.maxLevel)
    if storedTopHash != computedTopHash then
      bocFail "BOC: representation hash mismatch"
    let storedTopDepth ← readNatBE cellBytes topDepthOff 2
    let computedTopDepth : Nat := infoComputed.getDepth Cell.maxLevel
    if storedTopDepth != computedTopDepth then
      bocFail "BOC: depth mismatch"

    -- Lower hashes/depths.
    let effLevel : Nat := infoComputed.effectiveLevel
    let mut hash_i : Nat := 0
    for level_i in [0:effLevel] do
      if !LevelMask.isSignificant info.levelMask level_i then
        continue
      let off := hashesOffset + 32 * hash_i
      let stored := cellBytes.extract off (off + 32)
      let computed : ByteArray := ByteArray.mk (infoComputed.getHash level_i)
      if stored != computed then
        bocFail "BOC: lower hash mismatch"
      let offD := depthOffset + 2 * hash_i
      let storedD ← readNatBE cellBytes offD 2
      let computedD : Nat := infoComputed.getDepth level_i
      if storedD != computedD then
        bocFail "BOC: lower depth mismatch"
      hash_i := hash_i + 1

  return cell

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

/-! ### Serialization (subset compatible with C++ `vm::BagOfCells`) -/

structure BocSerializeOpts where
  hasIndex : Bool := false
  hasCrc32c : Bool := false
  hasCacheBits : Bool := false
  deriving Repr

def BocSerializeOpts.mode (o : BocSerializeOpts) : Nat :=
  (if o.hasIndex then 1 else 0) +
  (if o.hasCrc32c then 2 else 0) +
  (if o.hasCacheBits then 16 else 0)

def BocSerializeOpts.ofHeader (h : BocHeader) : BocSerializeOpts :=
  { hasIndex := h.hasIndex, hasCrc32c := h.hasCrc32c, hasCacheBits := h.hasCacheBits }

def natToBytesLEFixed (n : Nat) (len : Nat) : Array UInt8 :=
  Array.ofFn (n := len) fun i =>
    let shift := i.1 * 8
    UInt8.ofNat ((n >>> shift) &&& 0xff)

def computeRefByteSize (cellCount : Nat) : BocM Nat := do
  let mut rs : Nat := 0
  while cellCount ≥ (1 <<< (rs * 8)) do
    rs := rs + 1
  if rs = 0 ∨ rs > 4 then
    bocFail s!"BOC: invalid computed ref byte size {rs}"
  return rs

def computeOffsetByteSize (maxOffset : Nat) : BocM Nat := do
  let mut os : Nat := 0
  while maxOffset ≥ (1 <<< (os * 8)) do
    os := os + 1
  if os = 0 ∨ os > 8 then
    bocFail s!"BOC: invalid computed offset byte size {os}"
  return os

structure CellInfo where
  cell : Cell
  refs : Array Nat
  wt : Nat
  shouldCache : Bool
  newIdx : Int
  deriving Repr, Inhabited

structure ImportState where
  cells : Array CellInfo
  map : Std.HashMap ByteArray Nat
  intRefs : Nat

def ImportState.empty : ImportState :=
  { cells := #[], map := {}, intRefs := 0 }

partial def importCell (c : Cell) (st : ImportState) : BocM (Nat × ImportState) := do
  if c.refs.size > 4 then
    bocFail "BOC: cells with >4 refs not supported"
  if c.bits.size > 1023 then
    bocFail "BOC: cell bitstring too large"
  let key : ByteArray := ByteArray.mk (Cell.hashBytes c)
  match st.map[key]? with
  | some idx =>
      let ci := st.cells[idx]!
      let cells := st.cells.set! idx { ci with shouldCache := true }
      return (idx, { st with cells := cells })
  | none =>
      let mut st := st
      let mut refs : Array Nat := #[]
      let mut sumChildWt : Nat := 1
      for r in c.refs do
        let (ri, st') ← importCell r st
        st := { st' with intRefs := st'.intRefs + 1 }
        refs := refs.push ri
        sumChildWt := sumChildWt + (st.cells[ri]!).wt
      let wt : Nat := Nat.min 255 sumChildWt
      let idx := st.cells.size
      let ci : CellInfo := { cell := c, refs := refs, wt := wt, shouldCache := false, newIdx := -1 }
      let cells := st.cells.push ci
      let map := st.map.insert key idx
      return (idx, { st with cells := cells, map := map })

def reorderWeights (cells : Array CellInfo) : Array CellInfo :=
  -- Mirrors `vm::BagOfCells::reorder_cells` weight adjustment used for `is_special()` decisions.
  Id.run do
    let maxCellWhs : Nat := 64
    let mut cells := cells

    for i in [0:cells.size] do
      let idx := cells.size - 1 - i
      let dci := cells[idx]!
      let s := dci.refs.size
      if s = 0 then
        continue
      let mut c : Nat := s
      let mut sum : Nat := maxCellWhs - 1
      let mut mask : Nat := 0
      for j in [0:s] do
        let childIdx := dci.refs[j]!
        let dcj := cells[childIdx]!
        let limit : Nat := (maxCellWhs - 1 + j) / s
        if dcj.wt ≤ limit then
          sum := sum - dcj.wt
          c := c - 1
          mask := mask ||| (1 <<< j)
      if c ≠ 0 then
        for j in [0:s] do
          if (mask &&& (1 <<< j)) = 0 then
            let childIdx := dci.refs[j]!
            let dcj := cells[childIdx]!
            let limit : Nat := sum / c
            sum := sum + 1
            if dcj.wt > limit then
              cells := cells.set! childIdx { dcj with wt := limit }

    for i in [0:cells.size] do
      let dci := cells[i]!
      let mut sum : Nat := 1
      for j in [0:dci.refs.size] do
        sum := sum + (cells[dci.refs[j]!]!).wt
      if sum ≤ dci.wt then
        cells := cells.set! i { dci with wt := sum }
      else
        cells := cells.set! i { dci with wt := 0 }

    cells

structure ReorderState where
  cells : Array CellInfo
  tmp : Array CellInfo
  rvIdx : Nat
  deriving Repr

partial def revisit (cellIdx : Nat) (force : Nat) (st : ReorderState) : BocM (Int × ReorderState) := do
  let dci := st.cells[cellIdx]!
  if dci.newIdx ≥ 0 then
    return (dci.newIdx, st)

  if force = 0 then
    if dci.newIdx ≠ -1 then
      return (dci.newIdx, st)
    let mut st := st
    for j in [0:dci.refs.size] do
      let k := dci.refs.size - 1 - j
      let childOld := dci.refs[k]!
      let child := st.cells[childOld]!
      let childForce : Nat := if child.wt = 0 then 1 else 0
      let (_, st') ← revisit childOld childForce st
      st := st'
    let dci' := { dci with newIdx := -2 }
    let cells := st.cells.set! cellIdx dci'
    return (-2, { st with cells := cells })

  if force > 1 then
    let new : Nat := st.rvIdx
    let dci' := { dci with newIdx := Int.ofNat new }
    let cells := st.cells.set! cellIdx dci'
    let tmp := st.tmp.push dci'
    return (Int.ofNat new, { st with cells := cells, tmp := tmp, rvIdx := new + 1 })

  -- force = 1 (visit)
  if dci.newIdx = -3 then
    return (-3, st)
  let mut st := st
  if dci.wt = 0 then
    let (_, st') ← revisit cellIdx 0 st
    st := st'
  -- visit children
  for j in [0:dci.refs.size] do
    let k := dci.refs.size - 1 - j
    let childOld := dci.refs[k]!
    let (_, st') ← revisit childOld 1 st
    st := st'
  -- allocate children + rewrite refs to new indices
  let mut newRefs := dci.refs
  for j in [0:dci.refs.size] do
    let k := dci.refs.size - 1 - j
    let childOld := dci.refs[k]!
    let (childNew, st') ← revisit childOld 2 st
    st := st'
    if childNew < 0 then
      bocFail "BOC: internal error (child allocation did not return an index)"
    newRefs := newRefs.set! k childNew.toNat
  let dci' := { (st.cells[cellIdx]!) with refs := newRefs, newIdx := -3 }
  let cells := st.cells.set! cellIdx dci'
  return (-3, { st with cells := cells })

def reorderCells (cells : Array CellInfo) (rootIdxs : Array Nat) : BocM (Array CellInfo × Array Nat) := do
  let cells := reorderWeights cells
  let mut st : ReorderState := { cells := cells, tmp := #[], rvIdx := 0 }
  for r in rootIdxs do
    let (_, st') ← revisit r 0 st
    st := st'
    let (_, st'') ← revisit r 1 st
    st := st''
  let mut rootsNew : Array Nat := #[]
  for r in rootIdxs do
    let (ri, st') ← revisit r 2 st
    st := st'
    if ri < 0 then
      bocFail "BOC: internal error (root allocation did not return an index)"
    rootsNew := rootsNew.push ri.toNat
  if st.rvIdx ≠ cells.size then
    bocFail "BOC: internal error (reorder did not allocate all cells)"
  return (st.tmp, rootsNew)

def cellBaseSerializedSize (c : Cell) : BocM Nat := do
  if c.refs.size > 4 then
    bocFail "BOC: cells with >4 refs not supported"
  if c.bits.size > 1023 then
    bocFail "BOC: cell bitstring too large"
  let fullBytes : Nat := c.bits.size / 8
  let remBits : Nat := c.bits.size % 8
  let dataLen : Nat := if remBits = 0 then fullBytes else fullBytes + 1
  return 2 + dataLen

def serializeCellNoRefs (c : Cell) : BocM (Array UInt8) := do
  let refsCnt := c.refs.size
  if refsCnt > 4 then
    bocFail "BOC: cells with >4 refs not supported"
  if c.bits.size > 1023 then
    bocFail "BOC: cell bitstring too large"
  let fullBytes : Nat := c.bits.size / 8
  let remBits : Nat := c.bits.size % 8
  let d1 : Nat :=
    refsCnt +
      (if c.special then 8 else 0) +
        ((LevelMask.apply c.levelMask Cell.maxLevel) <<< 5)
  let d2 : Nat := (fullBytes <<< 1) + (if remBits = 0 then 0 else 1)
  let mut out : Array UInt8 := #[UInt8.ofNat d1, UInt8.ofNat d2]
  for i in [0:fullBytes] do
    out := out.push (bitsToByte c.bits (i * 8) 8)
  if remBits ≠ 0 then
    out := out.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)
  return out

def stdBocSerializeMulti (roots : Array Cell) (opts : BocSerializeOpts := {}) : BocM ByteArray := do
  if roots.size = 0 then
    bocFail "BOC: need at least one root"
  if opts.hasCacheBits && !opts.hasIndex then
    bocFail "BOC: cache bits require index table"

  -- Import cells (deduplicate by cell hash, like C++).
  let mut st : ImportState := ImportState.empty
  let mut rootIdxs : Array Nat := #[]
  for r in roots do
    let (ri, st') ← importCell r st
    st := st'
    rootIdxs := rootIdxs.push ri

  let (cellsInternal, rootsInternal) ← reorderCells st.cells rootIdxs
  let cellCount := cellsInternal.size
  let rootCount := rootsInternal.size
  let refByteSize ← computeRefByteSize cellCount

  let mut dataBytes : Nat := 0
  for ci in cellsInternal do
    dataBytes := dataBytes + (← cellBaseSerializedSize ci.cell)
  let dataSize : Nat := dataBytes + st.intRefs * refByteSize
  let maxOffset : Nat := if opts.hasCacheBits then dataSize * 2 else dataSize
  let offsetByteSize ← computeOffsetByteSize maxOffset

  -- Header.
  let mut out : Array UInt8 := #[]
  out := out ++ natToBytesBEFixed BocHeader.magicGeneric 4
  let mut flags : Nat := refByteSize
  if opts.hasIndex then flags := flags ||| (1 <<< 7)
  if opts.hasCrc32c then flags := flags ||| (1 <<< 6)
  if opts.hasCacheBits then flags := flags ||| (1 <<< 5)
  out := out.push (UInt8.ofNat flags)
  out := out.push (UInt8.ofNat offsetByteSize)
  out := out ++ natToBytesBEFixed cellCount refByteSize
  out := out ++ natToBytesBEFixed rootCount refByteSize
  out := out ++ natToBytesBEFixed 0 refByteSize -- absent_count
  out := out ++ natToBytesBEFixed dataSize offsetByteSize

  -- Root indices (BOC numbering is reverse of internal indices).
  for rInternal in rootsInternal do
    let rBoc := cellCount - 1 - rInternal
    out := out ++ natToBytesBEFixed rBoc refByteSize

  -- Index table.
  let cellsBoc : Array CellInfo := cellsInternal.reverse
  if opts.hasIndex then
    let mut offs : Nat := 0
    for ci in cellsBoc do
      offs := offs + (← cellBaseSerializedSize ci.cell) + ci.refs.size * refByteSize
      let fixed := if opts.hasCacheBits then offs * 2 + (if ci.shouldCache then 1 else 0) else offs
      out := out ++ natToBytesBEFixed fixed offsetByteSize
    if offs ≠ dataSize then
      bocFail "BOC: internal error (index table size mismatch)"

  -- Cell data.
  let mut written : Nat := 0
  for ci in cellsBoc do
    let cellBytes ← serializeCellNoRefs ci.cell
    out := out ++ cellBytes
    written := written + cellBytes.size
    for childInternal in ci.refs do
      let childBoc := cellCount - 1 - childInternal
      out := out ++ natToBytesBEFixed childBoc refByteSize
      written := written + refByteSize
  if written ≠ dataSize then
    bocFail "BOC: internal error (data size mismatch)"

  -- CRC32C (little-endian, like C++).
  if opts.hasCrc32c then
    let crc := (crc32c (ByteArray.mk out)).toNat
    out := out ++ natToBytesLEFixed crc 4

  return ByteArray.mk out

def stdBocSerialize (root : Cell) (opts : BocSerializeOpts := {}) : BocM ByteArray := do
  let roots : Array Cell := #[root]
  stdBocSerializeMulti roots opts

end TvmLean
