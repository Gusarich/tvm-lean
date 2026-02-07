import TvmLean.Model.Instr.Codepage.Cp0

namespace TvmLean

def intToBitsTwos (n : Int) (bits : Nat) : Except Excno BitString := do
  if bits = 0 then
    return #[]
  -- For signed `bits`-wide two's complement, require `-(2^(bits-1)) ≤ n < 2^(bits-1)`.
  let half : Int := intPow2 (bits - 1)
  if decide (n < -half ∨ n ≥ half) then
    throw .rangeChk
  let modulus : Nat := 1 <<< bits
  if n ≥ 0 then
    let u := n.toNat
    return natToBits u bits
  else
    -- two's complement: 2^bits - |n|
    let abs : Nat := (-n).toNat
    return natToBits (modulus - abs) bits

def Slice.takeBitsAsNatCellUnd (s : Slice) (n : Nat) : Except Excno (Nat × Slice) := do
  if s.haveBits n then
    let bs := s.readBits n
    return (bitsToNat bs, s.advanceBits n)
  else
    throw .cellUnd

def Slice.skipMaybeAnycast (s : Slice) : Except Excno Slice := do
  -- Mirrors C++ `skip_maybe_anycast` (tonops.cpp).
  let (b, s1) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then
    return s1
  else
    let lenBits : Nat := 5 -- natLenBits 30
    let (depth, s2) ← s1.takeBitsAsNatCellUnd lenBits
    if depth = 0 ∨ depth > 30 then
      throw .cellUnd
    if s2.haveBits depth then
      return s2.advanceBits depth
    else
      throw .cellUnd

def Slice.skipMessageAddr (s : Slice) : Except Excno Slice := do
  -- Minimal `MsgAddress` support (enough for common std addresses used in real txs).
  let (tag, s2) ← s.takeBitsAsNatCellUnd 2
  match tag with
  | 0 =>
      -- addr_none$00
      return s2
  | 1 =>
      -- addr_extern$01 len:(## 9) external_address:(bits len)
      let (len, s11) ← s2.takeBitsAsNatCellUnd 9
      if s11.haveBits len then
        return s11.advanceBits len
      else
        throw .cellUnd
  | 2 =>
      -- addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256
      let s3 ← s2.skipMaybeAnycast
      let need : Nat := 8 + 256
      if s3.haveBits need then
        return s3.advanceBits need
      else
        throw .cellUnd
  | 3 =>
      -- addr_var$11 anycast:(Maybe Anycast) addr_len:(## 9) workchain_id:int32 address:(bits addr_len)
      let s3 ← s2.skipMaybeAnycast
      let (len, s12) ← s3.takeBitsAsNatCellUnd 9
      let need : Nat := 32 + len
      if s12.haveBits need then
        return s12.advanceBits need
      else
        throw .cellUnd
  | _ =>
      throw .cellUnd

def Slice.parseMaybeAnycast (s : Slice) : Except Excno (Value × Slice) := do
  -- Mirrors C++ `parse_maybe_anycast` (tonops.cpp): returns (null) for nothing$0 or a slice for just$1.
  let (b, s1) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then
    return (.null, s1)
  else
    let lenBits : Nat := 5 -- natLenBits 30
    let (depth, s2) ← s1.takeBitsAsNatCellUnd lenBits
    if depth = 0 ∨ depth > 30 then
      throw .cellUnd
    if !s2.haveBits depth then
      throw .cellUnd
    let pfxBits := s2.readBits depth
    let s3 := s2.advanceBits depth
    return (.slice (Slice.ofCell (Cell.mkOrdinary pfxBits #[])), s3)

def Slice.parseMessageAddr (s : Slice) : Except Excno (Array Value × Slice) := do
  -- Mirrors C++ `parse_message_addr` (tonops.cpp).
  let (tag, s2) ← s.takeBitsAsNatCellUnd 2
  match tag with
  | 0 =>
      -- addr_none$00 = MsgAddressExt; -> (0)
      return (#[.int (.num 0)], s2)
  | 1 =>
      -- addr_extern$01 len:(## 9) external_address:(bits len) = MsgAddressExt; -> (1, addr)
      let (len, s3) ← s2.takeBitsAsNatCellUnd 9
      if !s3.haveBits len then
        throw .cellUnd
      let addrBits := s3.readBits len
      let s4 := s3.advanceBits len
      return (#[.int (.num 1), .slice (Slice.ofCell (Cell.mkOrdinary addrBits #[]))], s4)
  | 2 =>
      -- addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256 = MsgAddressInt;
      -- -> (2, anycast_or_null, workchain, addr256)
      let (anycast, s3) ← s2.parseMaybeAnycast
      let (wcNat, s4) ← s3.takeBitsAsNatCellUnd 8
      if !s4.haveBits 256 then
        throw .cellUnd
      let addrBits := s4.readBits 256
      let s5 := s4.advanceBits 256
      let wc : Int := natToIntSignedTwos wcNat 8
      return (#[.int (.num 2), anycast, .int (.num wc), .slice (Slice.ofCell (Cell.mkOrdinary addrBits #[]))], s5)
  | 3 =>
      -- addr_var$11 anycast:(Maybe Anycast) addr_len:(## 9) workchain_id:int32 address:(bits addr_len) = MsgAddressInt;
      -- -> (3, anycast_or_null, workchain, addr)
      let (anycast, s3) ← s2.parseMaybeAnycast
      let (len, s4) ← s3.takeBitsAsNatCellUnd 9
      let (wcNat, s5) ← s4.takeBitsAsNatCellUnd 32
      if !s5.haveBits len then
        throw .cellUnd
      let addrBits := s5.readBits len
      let s6 := s5.advanceBits len
      let wc : Int := natToIntSignedTwos wcNat 32
      return (#[.int (.num 3), anycast, .int (.num wc), .slice (Slice.ofCell (Cell.mkOrdinary addrBits #[]))], s6)
  | _ =>
      throw .cellUnd

def Slice.takeVarUIntegerCellUnd (s : Slice) (lenBits : Nat) : Except Excno (Nat × Slice) := do
  let (len, s1) ← s.takeBitsAsNatCellUnd lenBits
  let dataBits : Nat := len * 8
  if s1.haveBits dataBits then
    let bs := s1.readBits dataBits
    return (bitsToNat bs, s1.advanceBits dataBits)
  else
    throw .cellUnd

def Slice.takeGramsCellUnd (s : Slice) : Except Excno (Int × Slice) := do
  -- Grams = VarUInteger 16, which uses 4-bit length (bytes) prefix in practice.
  let (n, s1) ← s.takeVarUIntegerCellUnd 4
  return (Int.ofNat n, s1)

def Slice.skipHashmapECellUnd (s : Slice) : Except Excno Slice := do
  -- HashmapE is encoded as: `hme_empty$0` or `hme_root$1 root:^Hashmap`.
  let (tag, s1) ← s.takeBitsAsNatCellUnd 1
  if tag = 0 then
    return s1
  else
    if s1.haveRefs 1 then
      return { s1 with refPos := s1.refPos + 1 }
    else
      throw .cellUnd

def Slice.takeCurrencyCollectionGramsCellUnd (s : Slice) : Except Excno (Int × Slice) := do
  -- CurrencyCollection = currencies$_ grams:Grams other:ExtraCurrencyCollection.
  let (grams, s1) ← s.takeGramsCellUnd
  -- ExtraCurrencyCollection = extra_currencies$_ dict:(HashmapE 32 (VarUInteger 32))
  let s2 ← s1.skipHashmapECellUnd
  return (grams, s2)

def Slice.skipStateInitCellUnd (s : Slice) : Except Excno Slice := do
  -- StateInit = _ fixed_prefix_length:(Maybe (## 5)) special:(Maybe TickTock)
  --              code:(Maybe ^Cell) data:(Maybe ^Cell) library:(Maybe ^Cell)
  let (hasFixed, s1) ← s.takeBitsAsNatCellUnd 1
  let s2 ←
    if hasFixed = 0 then
      pure s1
    else if s1.haveBits 5 then
      pure (s1.advanceBits 5)
    else
      throw .cellUnd
  let (hasSpecial, s3) ← s2.takeBitsAsNatCellUnd 1
  let s4 ←
    if hasSpecial = 0 then
      pure s3
    else if s3.haveBits 2 then
      pure (s3.advanceBits 2)
    else
      throw .cellUnd
  let (hasCode, s5) ← s4.takeBitsAsNatCellUnd 1
  let s6 ←
    if hasCode = 0 then
      pure s5
    else if s5.haveRefs 1 then
      pure { s5 with refPos := s5.refPos + 1 }
    else
      throw .cellUnd
  let (hasData, s7) ← s6.takeBitsAsNatCellUnd 1
  let s8 ←
    if hasData = 0 then
      pure s7
    else if s7.haveRefs 1 then
      pure { s7 with refPos := s7.refPos + 1 }
    else
      throw .cellUnd
  let (hasLib, s9) ← s8.takeBitsAsNatCellUnd 1
  if hasLib = 0 then
    return s9
  else if s9.haveRefs 1 then
    return { s9 with refPos := s9.refPos + 1 }
  else
    throw .cellUnd

def Slice.prefixCell (start stop : Slice) : Cell :=
  Cell.mkOrdinary
    (start.cell.bits.extract start.bitPos stop.bitPos)
    (start.cell.refs.extract start.refPos stop.refPos)

structure SendMsgParsed where
  extMsg : Bool
  dest : Slice
  value : Int
  userFwdFee : Int
  extraFlagsLen : Nat
  haveExtraCurrencies : Bool
  haveInit : Bool
  initRef : Bool
  initInlineBits : Nat
  initRefs : Nat
  bodyRef : Bool
  bodyInlineBits : Nat
  bodyRefs : Nat
  deriving Repr

def natLenBits (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

def Slice.countLeading (s : Slice) (b : Bool) : Nat :=
  Id.run do
    let mut k : Nat := 0
    while s.bitPos + k < s.cell.bits.size && s.cell.bits[s.bitPos + k]! == b do
      k := k + 1
    return k

structure DictLabel where
  remainder : Slice
  len : Nat
  sameBit : Option Bool
  storedBits : Nat
  deriving Repr

def parseDictLabel (cell : Cell) (maxLen : Nat) : Except Excno DictLabel := do
  let mut cs := Slice.ofCell cell
  if !cs.haveBits 2 then
    throw .cellUnd
  let p2 := bitsToNat (cs.readBits 2)
  match p2 with
  | 0 =>
      cs := cs.advanceBits 2
      return { remainder := cs, len := 0, sameBit := none, storedBits := 0 }
  | 1 =>
      -- hml_short: `0 1^len 0 <len bits>`
      cs := cs.advanceBits 1
      let lBits := cs.countLeading true
      if lBits > maxLen then
        throw .cellUnd
      if !cs.haveBits (2 * lBits + 1) then
        throw .cellUnd
      cs := cs.advanceBits (lBits + 1)
      return { remainder := cs, len := lBits, sameBit := none, storedBits := lBits }
  | 2 =>
      -- hml_long: `10 <lenBits bits len> <len bits>`
      let lenBits := natLenBits maxLen
      cs := cs.advanceBits 2
      let (lBits, cs') ← cs.takeBitsAsNatCellUnd lenBits
      if lBits > maxLen then
        throw .cellUnd
      if !cs'.haveBits lBits then
        throw .cellUnd
      return { remainder := cs', len := lBits, sameBit := none, storedBits := lBits }
  | 3 =>
      -- hml_same: `11b <lenBits bits len>`
      let lenBits := natLenBits maxLen
      if !cs.haveBits (3 + lenBits) then
        throw .cellUnd
      let (same3, cs3) ← cs.takeBitsAsNatCellUnd 3
      let sameBit := (same3 &&& 1) = 1
      let (lBits, cs') ← cs3.takeBitsAsNatCellUnd lenBits
      if lBits > maxLen then
        throw .cellUnd
      return { remainder := cs', len := lBits, sameBit := some sameBit, storedBits := 0 }
  | _ =>
      throw .cellUnd

def dictKeyBits? (idx : Int) (n : Nat) (unsigned : Bool) : Option BitString :=
  if n = 0 then
    if idx = 0 then some #[] else none
  else if unsigned then
    if idx < 0 then
      none
    else
      let u := idx.toNat
      if u ≥ (1 <<< n) then
        none
      else
        some (natToBits u n)
  else
    let half : Int := intPow2 (n - 1)
    if idx < -half ∨ idx ≥ half then
      none
    else
      match intToBitsTwos idx n with
      | .ok bs => some bs
      | .error _ => none

def dictLabelMatches (lbl : DictLabel) (key : BitString) (pos : Nat) : Bool :=
  if pos + lbl.len > key.size then
    false
  else
    match lbl.sameBit with
    | some b =>
        Id.run do
          let mut ok := true
          for i in [0:lbl.len] do
            if key[pos + i]! != b then
              ok := false
          return ok
    | none =>
        let bs := lbl.remainder.readBits lbl.len
        Id.run do
          let mut ok := true
          for i in [0:lbl.len] do
            if bs[i]! != key[pos + i]! then
              ok := false
          return ok

def dictLabelBits (lbl : DictLabel) : BitString :=
  match lbl.sameBit with
  | some b => Array.replicate lbl.len b
  | none => lbl.remainder.readBits lbl.len

def dictValidateNodeExt (lbl : DictLabel) (remaining : Nat) : Except Excno Nat := do
  let rem0 : Nat := remaining - lbl.len
  -- Match C++ `LabelParser::validate_ext` (used by `Dictionary`):
  -- non-leaf nodes must keep exactly label payload bits and exactly two refs.
  if rem0 > 0 then
    if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
      throw .dictErr
  return rem0

def bitsCommonPrefixLen (a b : BitString) : Nat :=
  let m : Nat := Nat.min a.size b.size
  Id.run do
    let mut k : Nat := 0
    while k < m && a[k]! == b[k]! do
      k := k + 1
    return k

partial def dictLookupAux (cell : Cell) (key : BitString) (pos remaining : Nat) : Except Excno (Option Slice) := do
  let lbl ← parseDictLabel cell remaining
  let rem0 ← dictValidateNodeExt lbl remaining
  if !dictLabelMatches lbl key pos then
    return none
  if rem0 = 0 then
    return some (lbl.remainder.advanceBits lbl.storedBits)
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return none
    let sw : Bool := key[nextPos]!
    let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
    dictLookupAux child key (nextPos + 1) (rem0 - 1)

def dictLookup (root : Option Cell) (key : BitString) : Except Excno (Option Slice) := do
  match root with
  | none => return none
  | some cell =>
      dictLookupAux cell key 0 key.size

partial def dictLookupAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) :
    Except Excno (Option Slice × Array Cell) := do
  let lbl ← parseDictLabel cell remaining
  let rem0 ← dictValidateNodeExt lbl remaining
  if !dictLabelMatches lbl key pos then
    return (none, #[cell])
  if rem0 = 0 then
    return (some (lbl.remainder.advanceBits lbl.storedBits), #[cell])
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return (none, #[cell])
    let sw : Bool := key[nextPos]!
    let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
    match (← dictLookupAuxWithCells child key (nextPos + 1) (rem0 - 1)) with
    | (res, cells) => return (res, #[cell] ++ cells)

def dictLookupWithCells (root : Option Cell) (key : BitString) : Except Excno (Option Slice × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      dictLookupAuxWithCells cell key 0 key.size

partial def dictLookupVisitedCellsAux (cell : Cell) (key : BitString) (pos remaining : Nat) : Array Cell :=
  let here : Array Cell := #[cell]
  match parseDictLabel cell remaining with
  | .error _ => here
  | .ok lbl =>
      let rem0 : Nat := remaining - lbl.len
      if rem0 = 0 then
        here
      else if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
        here
      else if !dictLabelMatches lbl key pos then
        here
      else
        let nextPos : Nat := pos + lbl.len
        if nextPos ≥ key.size then
          here
        else
          let sw : Bool := key[nextPos]!
          let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
          here ++ dictLookupVisitedCellsAux child key (nextPos + 1) (rem0 - 1)

def dictLookupVisitedCells (root : Option Cell) (key : BitString) : Array Cell :=
  match root with
  | none => #[]
  | some cell => dictLookupVisitedCellsAux cell key 0 key.size

partial def dictMinMaxVisitedCellsAux (cell : Cell) (n pos : Nat) (firstBit restBit : Bool) : Array Cell :=
  let here : Array Cell := #[cell]
  match parseDictLabel cell n with
  | .error _ => here
  | .ok lbl =>
      let rem0 : Nat := n - lbl.len
      if rem0 = 0 then
        here
      else if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
        here
      else
        let posAfter : Nat := pos + lbl.len
        let bit : Bool := if posAfter = 0 then firstBit else restBit
        let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
        here ++ dictMinMaxVisitedCellsAux child (rem0 - 1) (posAfter + 1) firstBit restBit

def dictMinMaxVisitedCells (root : Option Cell) (n : Nat) (fetchMax invertFirst : Bool) : Array Cell :=
  match root with
  | none => #[]
  | some cell =>
      let restBit : Bool := fetchMax
      let firstBit : Bool := restBit != invertFirst
      dictMinMaxVisitedCellsAux cell n 0 firstBit restBit

inductive DictDeleteVisitStatus where
  | found
  | none
  | err
  deriving Inhabited

structure DictDeleteVisit where
  status : DictDeleteVisitStatus
  loaded : Array Cell
  deriving Inhabited

private partial def dictDeleteVisitedTraceAux (cell : Cell) (key : BitString) (pos remaining : Nat) :
    DictDeleteVisit :=
  let here : Array Cell := #[cell]
  match parseDictLabel cell remaining with
  | .error _ =>
      { status := .err, loaded := here }
  | .ok lbl =>
      match dictValidateNodeExt lbl remaining with
      | .error _ =>
          { status := .err, loaded := here }
      | .ok rem0 =>
          if !dictLabelMatches lbl key pos then
            { status := .none, loaded := here }
          else if rem0 = 0 then
            { status := .found, loaded := here }
          else
            let nextPos : Nat := pos + lbl.len
            if nextPos ≥ key.size then
              { status := .err, loaded := here }
            else
              let swBit : Bool := key[nextPos]!
              let left0 := lbl.remainder.cell.refs[0]!
              let right0 := lbl.remainder.cell.refs[1]!
              let child0 : Cell := if swBit then right0 else left0
              let sibling0 : Cell := if swBit then left0 else right0
              let childTrace := dictDeleteVisitedTraceAux child0 key (nextPos + 1) (rem0 - 1)
              match childTrace.status with
              | .err =>
                  -- Error while descending: sibling merge path is not reached.
                  { status := .err, loaded := here ++ childTrace.loaded }
              | .none =>
                  { status := .none, loaded := here ++ childTrace.loaded ++ #[sibling0] }
              | .found =>
                  { status := .found, loaded := here ++ childTrace.loaded ++ #[sibling0] }

def dictDeleteVisitedCells (root : Option Cell) (key : BitString) : Array Cell :=
  match root with
  | none => #[]
  | some cell => (dictDeleteVisitedTraceAux cell key 0 key.size).loaded

partial def dictReplaceBuilderAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) (newVal : Builder) :
    Except Excno (Cell × Bool × Nat × Array Cell) := do
  let lbl ← parseDictLabel cell remaining
  let rem0 ← dictValidateNodeExt lbl remaining
  if !dictLabelMatches lbl key pos then
    return (cell, false, 0, #[cell])
  if rem0 = 0 then
    let valueStart := lbl.remainder.advanceBits lbl.storedBits
    let prefixBits := cell.bits.take valueStart.bitPos
    let newBits := prefixBits ++ newVal.bits
    if newBits.size > 1023 || newVal.refs.size > 4 then
      throw .cellOv
    let newCell : Cell := Cell.mkOrdinary newBits newVal.refs
    return (newCell, true, 1, #[cell])
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return (cell, false, 0, #[cell])
    let sw : Bool := key[nextPos]!
    if cell.refs.size < 2 then
      throw .dictErr
    let left := cell.refs[0]!
    let right := cell.refs[1]!
    let (childNew, ok, created, loaded) ←
      if sw then
        dictReplaceBuilderAuxWithCells right key (nextPos + 1) (rem0 - 1) newVal
      else
        dictReplaceBuilderAuxWithCells left key (nextPos + 1) (rem0 - 1) newVal
    if !ok then
      return (cell, false, 0, #[cell] ++ loaded)
    let newRefs : Array Cell :=
      if sw then
        #[left, childNew]
      else
        #[childNew, right]
    let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
    return (newCell, true, created + 1, #[cell] ++ loaded)

def dictReplaceBuilderWithCells (root : Option Cell) (key : BitString) (newVal : Builder) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  match root with
  | none => return (none, false, 0, #[])
  | some cell =>
      let (c', ok, created, loaded) ← dictReplaceBuilderAuxWithCells cell key 0 key.size newVal
      return (some c', ok, created, loaded)

def bitsAllSame? (bs : BitString) : Option Bool :=
  if h : 0 < bs.size then
    let b0 := bs[0]!
    Id.run do
      let mut ok := true
      for i in [0:bs.size] do
        if bs[i]! != b0 then
          ok := false
      if ok then some b0 else none
  else
    none

def dictLabelEncodeSame (same : Bool) (len maxLen : Nat) : BitString :=
  let k : Nat := natLenBits maxLen
  if len > 1 && k < 2 * len - 1 then
    -- mode '11'
    natToBits (6 + (if same then 1 else 0)) 3 ++ natToBits len k
  else if k < len then
    -- mode '10'
    natToBits 2 2 ++ natToBits len k ++ Array.replicate len same
  else
    -- mode '0'
    #[false] ++ Array.replicate len true ++ #[false] ++ Array.replicate len same

def dictLabelEncode (labelBits : BitString) (len maxLen : Nat) : BitString :=
  if len = 0 then
    -- mode '0' with len=0: `0 0`
    #[false, false]
  else
    match bitsAllSame? (labelBits.take len) with
    | some b => dictLabelEncodeSame b len maxLen
    | none =>
        let k : Nat := natLenBits maxLen
        if k < len then
          -- mode '10'
          natToBits 2 2 ++ natToBits len k ++ labelBits.take len
        else
          -- mode '0'
          #[false] ++ Array.replicate len true ++ #[false] ++ labelBits.take len

def builderStoreBitsChecked (b : Builder) (bs : BitString) : Except Excno Builder := do
  if b.canExtendBy bs.size then
    return b.storeBits bs
  else
    throw .cellOv

def builderStoreRefChecked (b : Builder) (c : Cell) : Except Excno Builder := do
  if b.canExtendBy 0 1 then
    return { b with refs := b.refs.push c }
  else
    throw .cellOv

def builderAppendCellChecked (b : Builder) (c : Cell) : Except Excno Builder := do
  if b.canExtendBy c.bits.size c.refs.size then
    return { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
  else
    throw .cellOv

def builderAppendBuilderChecked (b : Builder) (v : Builder) : Except Excno Builder := do
  if b.canExtendBy v.bits.size v.refs.size then
    return { bits := b.bits ++ v.bits, refs := b.refs ++ v.refs }
  else
    throw .cellOv

partial def dictMinMaxAuxWithCells (cell : Cell) (n pos : Nat) (firstBit restBit : Bool) :
    Except Excno (Slice × BitString × Array Cell) := do
  let lbl ← parseDictLabel cell n
  let rem0 ← dictValidateNodeExt lbl n
  let labelBits := dictLabelBits lbl
  let payload := lbl.remainder.advanceBits lbl.storedBits
  if rem0 = 0 then
    return (payload, labelBits, #[cell])

  let posAfter : Nat := pos + lbl.len
  let bit : Bool := if posAfter = 0 then firstBit else restBit
  let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
  let (val, keyTail, loaded) ← dictMinMaxAuxWithCells child (rem0 - 1) (posAfter + 1) firstBit restBit
  return (val, labelBits ++ #[bit] ++ keyTail, #[cell] ++ loaded)

def dictMinMaxWithCells (root : Option Cell) (n : Nat) (fetchMax invertFirst : Bool) :
    Except Excno (Option (Slice × BitString) × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      let restBit : Bool := fetchMax
      let firstBit : Bool := restBit != invertFirst
      let (val, keyBits, loaded) ← dictMinMaxAuxWithCells cell n 0 firstBit restBit
      return (some (val, keyBits), loaded)

partial def dictNearestAuxWithCells (cell : Cell) (hint : BitString) (n pos : Nat) (allowEq : Bool)
    (firstBit restBit : Bool) : Except Excno (Option (Slice × BitString) × Array Cell) := do
  let lbl ← parseDictLabel cell n
  let rem0 ← dictValidateNodeExt lbl n
  let labelBits := dictLabelBits lbl

  -- Compare the hint against the edge label.
  let pfxLen : Nat := bitsCommonPrefixLen labelBits (hint.take lbl.len)
  if pfxLen < lbl.len then
    let hintBit : Bool := hint[pfxLen]!
    let expectedBit : Bool := if pos = 0 ∧ pfxLen = 0 then firstBit else restBit
    if hintBit = expectedBit then
      return (none, #[cell])
    else
      let firstBit' : Bool := !firstBit
      let restBit' : Bool := !restBit
      let (val, keyBits, loadedMin) ← dictMinMaxAuxWithCells cell n pos firstBit' restBit'
      return (some (val, keyBits), #[cell] ++ loadedMin)

  -- Label fully matches: recurse into child.
  let payload := lbl.remainder.advanceBits lbl.storedBits
  let posAfter : Nat := pos + lbl.len
  let hintRest : BitString := hint.extract lbl.len hint.size
  if rem0 = 0 then
    if allowEq then
      return (some (payload, labelBits), #[cell])
    else
      return (none, #[cell])

  if hintRest.isEmpty then
    throw .dictErr
  let bit : Bool := hintRest[0]!
  let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
  let hintChild : BitString := hintRest.extract 1 hintRest.size
  let (resChild, loadedChild) ← dictNearestAuxWithCells child hintChild (rem0 - 1) (posAfter + 1) allowEq firstBit restBit
  match resChild with
  | some (val, keyTail) =>
      return (some (val, labelBits ++ #[bit] ++ keyTail), #[cell] ++ loadedChild)
  | none =>
      let expectedBit : Bool := if posAfter = 0 then firstBit else restBit
      if bit = expectedBit then
        return (none, #[cell] ++ loadedChild)
      else
        let altChild := lbl.remainder.cell.refs[if expectedBit then 1 else 0]!
        let firstBit' : Bool := !firstBit
        let restBit' : Bool := !restBit
        let (valAlt, keyAlt, loadedAlt) ← dictMinMaxAuxWithCells altChild (rem0 - 1) (posAfter + 1) firstBit' restBit'
        return (some (valAlt, labelBits ++ #[expectedBit] ++ keyAlt), #[cell] ++ loadedChild ++ loadedAlt)

def dictNearestWithCells (root : Option Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    Except Excno (Option (Slice × BitString) × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      let restBit : Bool := fetchNext
      let firstBit : Bool := restBit != invertFirst
      dictNearestAuxWithCells cell hint hint.size 0 allowEq firstBit restBit

inductive DictNearestVisitStatus where
  | found
  | none
  | err
  deriving Inhabited

structure DictNearestVisit where
  status : DictNearestVisitStatus
  loaded : Array Cell
  deriving Inhabited

private partial def dictNearestVisitedTraceAux (cell : Cell) (hint : BitString) (n pos : Nat) (allowEq : Bool)
    (firstBit restBit : Bool) : DictNearestVisit :=
  let here : Array Cell := #[cell]
  match parseDictLabel cell n with
  | .error _ =>
      { status := .err, loaded := here }
  | .ok lbl =>
      let rem0 : Nat := n - lbl.len
      if rem0 > 0 && (lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2) then
        { status := .err, loaded := here }
      else
        let labelBits : BitString := dictLabelBits lbl
        let pfxLen : Nat := bitsCommonPrefixLen labelBits (hint.take lbl.len)
        if pfxLen < lbl.len then
          let hintBit : Bool := hint[pfxLen]!
          let expectedBit : Bool := if pos = 0 ∧ pfxLen = 0 then firstBit else restBit
          if hintBit = expectedBit then
            { status := .none, loaded := here }
          else
            let firstBit' : Bool := !firstBit
            let restBit' : Bool := !restBit
            let loadedMin : Array Cell := dictMinMaxVisitedCellsAux cell n pos firstBit' restBit'
            match dictMinMaxAuxWithCells cell n pos firstBit' restBit' with
            | .ok _ =>
                -- Includes a second visit of this node (reload) via `loadedMin`.
                { status := .found, loaded := here ++ loadedMin }
            | .error _ =>
                { status := .err, loaded := here ++ loadedMin }
        else if rem0 = 0 then
          { status := (if allowEq then .found else .none), loaded := here }
        else
          let hintRest : BitString := hint.extract lbl.len hint.size
          if hintRest.isEmpty then
            { status := .err, loaded := here }
          else
            let posAfter : Nat := pos + lbl.len
            let bit : Bool := hintRest[0]!
            let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
            let hintChild : BitString := hintRest.extract 1 hintRest.size
            let childTrace :=
              dictNearestVisitedTraceAux child hintChild (rem0 - 1) (posAfter + 1) allowEq firstBit restBit
            match childTrace.status with
            | .err =>
                { status := .err, loaded := here ++ childTrace.loaded }
            | .found =>
                { status := .found, loaded := here ++ childTrace.loaded }
            | .none =>
                let expectedBit : Bool := if posAfter = 0 then firstBit else restBit
                if bit = expectedBit then
                  { status := .none, loaded := here ++ childTrace.loaded }
                else
                  let altChild := lbl.remainder.cell.refs[if expectedBit then 1 else 0]!
                  let firstBit' : Bool := !firstBit
                  let restBit' : Bool := !restBit
                  let loadedAlt : Array Cell :=
                    dictMinMaxVisitedCellsAux altChild (rem0 - 1) (posAfter + 1) firstBit' restBit'
                  match dictMinMaxAuxWithCells altChild (rem0 - 1) (posAfter + 1) firstBit' restBit' with
                  | .ok _ =>
                      { status := .found, loaded := here ++ childTrace.loaded ++ loadedAlt }
                  | .error _ =>
                      { status := .err, loaded := here ++ childTrace.loaded ++ loadedAlt }

def dictNearestVisitedCells (root : Option Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    Array Cell :=
  match root with
  | none => #[]
  | some cell =>
      let restBit : Bool := fetchNext
      let firstBit : Bool := restBit != invertFirst
      (dictNearestVisitedTraceAux cell hint hint.size 0 allowEq firstBit restBit).loaded

partial def dictDeleteAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  let lbl ← parseDictLabel cell remaining
  let rem0 ← dictValidateNodeExt lbl remaining
  if !dictLabelMatches lbl key pos then
    return (none, some cell, 0, #[cell])
  let payload := lbl.remainder.advanceBits lbl.storedBits
  if rem0 = 0 then
    -- Delete leaf.
    return (some payload, none, 0, #[cell])

  let nextPos : Nat := pos + lbl.len
  let swBit : Bool := key[nextPos]!
  let left0 := lbl.remainder.cell.refs[0]!
  let right0 := lbl.remainder.cell.refs[1]!
  let child0 := if swBit then right0 else left0
  let (oldVal?, childNew?, createdChild, loadedChild) ← dictDeleteAuxWithCells child0 key (nextPos + 1) (rem0 - 1)
  match oldVal? with
  | none =>
      -- Not found in subtree: unchanged.
      return (none, some cell, 0, #[cell] ++ loadedChild)
  | some oldVal =>
      match childNew? with
      | some childNew =>
          -- Both children present: rebuild fork with updated child.
          let newRefs : Array Cell := if swBit then #[left0, childNew] else #[childNew, right0]
          let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
          return (some oldVal, some newCell, createdChild + 1, #[cell] ++ loadedChild)
      | none =>
          -- One child removed: merge current edge with the surviving child.
          let survivorBit : Bool := !swBit
          let survivor : Cell := if swBit then left0 else right0
          let lbl2 ← parseDictLabel survivor (rem0 - 1)
          let childLabelBits := dictLabelBits lbl2
          let combinedLabelBits : BitString := dictLabelBits lbl ++ #[survivorBit] ++ childLabelBits
          let combinedLen : Nat := lbl.len + 1 + lbl2.len
          let enc : BitString := dictLabelEncode combinedLabelBits combinedLen remaining
          let payload2 := lbl2.remainder.advanceBits lbl2.storedBits
          let payloadCell2 : Cell := payload2.toCellRemaining
          let b0 ← builderStoreBitsChecked Builder.empty enc
          let b1 ← builderAppendCellChecked b0 payloadCell2
          return (some oldVal, some b1.finalize, createdChild + 1, #[cell] ++ loadedChild ++ #[survivor])

def dictDeleteWithCells (root : Option Cell) (key : BitString) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  match root with
  | none => return (none, none, 0, #[])
  | some cell =>
      dictDeleteAuxWithCells cell key 0 key.size

def dictCommonPrefixLen (lbl : DictLabel) (key : BitString) : Nat :=
  let l := lbl.len
  match lbl.sameBit with
  | some b =>
      Id.run do
        let mut k : Nat := 0
        while k < l && k < key.size && key[k]! == b do
          k := k + 1
        return k
  | none =>
      let bs := lbl.remainder.readBits l
      Id.run do
        let mut k : Nat := 0
        while k < l && k < key.size && bs[k]! == key[k]! do
          k := k + 1
        return k

partial def dictSetGenAuxWithCells (root : Option Cell) (key : BitString)
    (storeVal : Builder → Except Excno Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let n : Nat := key.size
  match root with
  | none =>
      if mode == .replace then
        return (none, false, 0, #[])
      let enc : BitString := dictLabelEncode key n n
      let b0 := Builder.empty
      let b1 ← builderStoreBitsChecked b0 enc
      let b2 ← storeVal b1
      return (some b2.finalize, true, 1, #[])
  | some cell =>
      let lbl ← parseDictLabel cell n
      let rem0 ← dictValidateNodeExt lbl n
      let pfxLen : Nat := dictCommonPrefixLen lbl key
      if pfxLen < lbl.len then
        if mode == .replace then
          return (some cell, false, 0, #[cell])

        -- Insert a new fork inside the current edge.
        let m : Nat := n - pfxLen - 1
        let keySuffix : BitString := key.extract (pfxLen + 1) n

        -- New leaf for the inserted key.
        let enc1 : BitString := dictLabelEncode keySuffix m m
        let b1 ← builderStoreBitsChecked Builder.empty enc1
        let b1 ← storeVal b1
        let cNew := b1.finalize

        -- Lower part of the old edge.
        let t : Nat := lbl.len - pfxLen - 1
        let oldLabelBits : BitString :=
          match lbl.sameBit with
          | some b => Array.replicate lbl.len b
          | none => lbl.remainder.readBits lbl.len
        let oldSuffix : BitString := oldLabelBits.extract (pfxLen + 1) lbl.len
        let payloadSlice : Slice := lbl.remainder.advanceBits lbl.storedBits
        let payloadCell : Cell := payloadSlice.toCellRemaining
        let enc2 : BitString := dictLabelEncode oldSuffix t m
        let b2 ← builderStoreBitsChecked Builder.empty enc2
        let b2 ← builderAppendCellChecked b2 payloadCell
        let cOld := b2.finalize

        -- Fork node with the shared prefix.
        let prefBits : BitString := key.take pfxLen
        let encF : BitString := dictLabelEncode prefBits pfxLen n
        let bF ← builderStoreBitsChecked Builder.empty encF
        let swBit : Bool := key[pfxLen]!
        let (left, right) := if swBit then (cOld, cNew) else (cNew, cOld)
        let bF ← builderStoreRefChecked bF left
        let bF ← builderStoreRefChecked bF right
        return (some bF.finalize, true, 3, #[cell])

      if rem0 = 0 then
        -- Leaf node: key matches the whole label.
        if mode == .add then
          return (some cell, false, 0, #[cell])
        let enc : BitString := dictLabelEncode key n n
        let b0 ← builderStoreBitsChecked Builder.empty enc
        let b0 ← storeVal b0
        return (some b0.finalize, true, 1, #[cell])

      -- Fork node: recurse into the selected child.
      let swBit : Bool := key[lbl.len]!
      let childKey : BitString := key.extract (lbl.len + 1) n
      let left0 := lbl.remainder.cell.refs[0]!
      let right0 := lbl.remainder.cell.refs[1]!
      if swBit then
        let (rightNew?, ok, created, loaded) ← dictSetGenAuxWithCells (some right0) childKey storeVal mode
        if !ok then
          return (some cell, false, 0, #[cell] ++ loaded)
        match rightNew? with
        | none => throw .dictErr
        | some rightNew =>
            let labelBits : BitString := key.take lbl.len
            let enc : BitString := dictLabelEncode labelBits lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreRefChecked b left0
            let b ← builderStoreRefChecked b rightNew
            return (some b.finalize, true, created + 1, #[cell] ++ loaded)
      else
        let (leftNew?, ok, created, loaded) ← dictSetGenAuxWithCells (some left0) childKey storeVal mode
        if !ok then
          return (some cell, false, 0, #[cell] ++ loaded)
        match leftNew? with
        | none => throw .dictErr
        | some leftNew =>
            let labelBits : BitString := key.take lbl.len
            let enc : BitString := dictLabelEncode labelBits lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreRefChecked b leftNew
            let b ← builderStoreRefChecked b right0
            return (some b.finalize, true, created + 1, #[cell] ++ loaded)

def dictSetRefWithCells (root : Option Cell) (key : BitString) (valRef : Cell) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderStoreRefChecked b valRef
  dictSetGenAuxWithCells root key storeVal mode

def dictSetSliceWithCells (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let c := val.toCellRemaining
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendCellChecked b c
  dictSetGenAuxWithCells root key storeVal mode

def dictSetBuilderWithCells (root : Option Cell) (key : BitString) (val : Builder) (mode : DictSetMode) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendBuilderChecked b val
  dictSetGenAuxWithCells root key storeVal mode

partial def dictLookupSetGenAuxWithCells (root : Option Cell) (key : BitString)
    (storeVal : Builder → Except Excno Builder) (mode : DictSetMode) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let n : Nat := key.size
  match root with
  | none =>
      if mode == .replace then
        return (none, none, false, 0, #[])
      let enc : BitString := dictLabelEncode key n n
      let b0 := Builder.empty
      let b1 ← builderStoreBitsChecked b0 enc
      let b2 ← storeVal b1
      return (none, some b2.finalize, true, 1, #[])
  | some cell =>
      let lbl ← parseDictLabel cell n
      let rem0 ← dictValidateNodeExt lbl n
      let pfxLen : Nat := dictCommonPrefixLen lbl key
      if pfxLen < lbl.len then
        if mode == .replace then
          return (none, some cell, false, 0, #[cell])

        -- Insert a new fork inside the current edge.
        let m : Nat := n - pfxLen - 1
        let keySuffix : BitString := key.extract (pfxLen + 1) n

        -- New leaf for the inserted key.
        let enc1 : BitString := dictLabelEncode keySuffix m m
        let b1 ← builderStoreBitsChecked Builder.empty enc1
        let b1 ← storeVal b1
        let cNew := b1.finalize

        -- Lower part of the old edge.
        let t : Nat := lbl.len - pfxLen - 1
        let oldLabelBits : BitString := dictLabelBits lbl
        let oldSuffix : BitString := oldLabelBits.extract (pfxLen + 1) lbl.len
        let payloadSlice : Slice := lbl.remainder.advanceBits lbl.storedBits
        let payloadCell : Cell := payloadSlice.toCellRemaining
        let enc2 : BitString := dictLabelEncode oldSuffix t m
        let b2 ← builderStoreBitsChecked Builder.empty enc2
        let b2 ← builderAppendCellChecked b2 payloadCell
        let cOld := b2.finalize

        -- Fork node with the shared prefix.
        let prefBits : BitString := key.take pfxLen
        let encF : BitString := dictLabelEncode prefBits pfxLen n
        let bF ← builderStoreBitsChecked Builder.empty encF
        let swBit : Bool := key[pfxLen]!
        let (left, right) := if swBit then (cOld, cNew) else (cNew, cOld)
        let bF ← builderStoreRefChecked bF left
        let bF ← builderStoreRefChecked bF right
        return (none, some bF.finalize, true, 3, #[cell])

      if rem0 = 0 then
        -- Leaf node.
        let oldVal : Slice := lbl.remainder.advanceBits lbl.storedBits
        if mode == .add then
          return (some oldVal, some cell, false, 0, #[cell])
        let enc : BitString := dictLabelEncode key n n
        let b0 ← builderStoreBitsChecked Builder.empty enc
        let b0 ← storeVal b0
        return (some oldVal, some b0.finalize, true, 1, #[cell])

      -- Fork node: recurse into the selected child.
      let swBit : Bool := key[lbl.len]!
      let childKey : BitString := key.extract (lbl.len + 1) n
      let left0 := lbl.remainder.cell.refs[0]!
      let right0 := lbl.remainder.cell.refs[1]!
      if swBit then
        let (oldVal?, rightNew?, ok, created, loaded) ←
          dictLookupSetGenAuxWithCells (some right0) childKey storeVal mode
        if !ok then
          return (oldVal?, some cell, false, 0, #[cell] ++ loaded)
        match rightNew? with
        | none => throw .dictErr
        | some rightNew =>
            let labelBits : BitString := key.take lbl.len
            let enc : BitString := dictLabelEncode labelBits lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreRefChecked b left0
            let b ← builderStoreRefChecked b rightNew
            return (oldVal?, some b.finalize, true, created + 1, #[cell] ++ loaded)
      else
        let (oldVal?, leftNew?, ok, created, loaded) ←
          dictLookupSetGenAuxWithCells (some left0) childKey storeVal mode
        if !ok then
          return (oldVal?, some cell, false, 0, #[cell] ++ loaded)
        match leftNew? with
        | none => throw .dictErr
        | some leftNew =>
            let labelBits : BitString := key.take lbl.len
            let enc : BitString := dictLabelEncode labelBits lbl.len n
            let b ← builderStoreBitsChecked Builder.empty enc
            let b ← builderStoreRefChecked b leftNew
            let b ← builderStoreRefChecked b right0
            return (oldVal?, some b.finalize, true, created + 1, #[cell] ++ loaded)

def dictLookupSetRefWithCells (root : Option Cell) (key : BitString) (valRef : Cell) (mode : DictSetMode) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderStoreRefChecked b valRef
  dictLookupSetGenAuxWithCells root key storeVal mode

def dictLookupSetSliceWithCells (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let c := val.toCellRemaining
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendCellChecked b c
  dictLookupSetGenAuxWithCells root key storeVal mode

def dictLookupSetBuilderWithCells (root : Option Cell) (key : BitString) (val : Builder) (mode : DictSetMode) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendBuilderChecked b val
  dictLookupSetGenAuxWithCells root key storeVal mode

partial def dictExtractPrefixSubdictWithCells (root : Option Cell) (keyBits : Nat)
    (pfx : BitString) (prefixLen : Nat) (removePrefix : Bool) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  match root with
  | none =>
      return (none, false, 0, #[])
  | some rootCell =>
      if prefixLen = 0 then
        return (some rootCell, false, 0, #[])
      if prefixLen > keyBits then
        if removePrefix then
          throw .dictErr
        else
          return (none, true, 0, #[])

      let rec go (cell : Cell) (m : Nat) (loaded : Array Cell) :
          Except Excno (Option Cell × Bool × Nat × Array Cell) := do
        let loaded := loaded.push cell
        let remaining : Nat := keyBits - m
        let lbl ← parseDictLabel cell remaining
        let labelBits : BitString := dictLabelBits lbl
        let l : Nat := Nat.min (prefixLen - m) lbl.len
        let prefixPart : BitString := pfx.extract m (m + l)
        if bitsCommonPrefixLen labelBits prefixPart < l then
          return (none, true, 0, loaded)

        if m + lbl.len < prefixLen then
          let m1 : Nat := m + lbl.len
          if m1 ≥ prefixLen then
            throw .fatal
          if !lbl.remainder.haveRefs 2 then
            throw .dictErr
          let swBit : Bool := pfx[m1]!
          let child := lbl.remainder.cell.refs[if swBit then 1 else 0]!
          go child (m1 + 1) loaded
        else
          let payload := lbl.remainder.advanceBits lbl.storedBits
          if !removePrefix then
            if m = 0 then
              return (some rootCell, false, 0, loaded)
            let combinedLabelBits : BitString := pfx.take m ++ labelBits
            let combinedLen : Nat := m + lbl.len
            let enc : BitString := dictLabelEncode combinedLabelBits combinedLen keyBits
            let b0 ← builderStoreBitsChecked Builder.empty enc
            let b1 ← builderAppendCellChecked b0 payload.toCellRemaining
            return (some b1.finalize, true, 1, loaded)
          else
            let newKeyBits : Nat := keyBits - prefixLen
            let keep : Nat := m + lbl.len - prefixLen
            let suffixBits : BitString := labelBits.drop (lbl.len - keep)
            let enc : BitString := dictLabelEncode suffixBits keep newKeyBits
            let b0 ← builderStoreBitsChecked Builder.empty enc
            let b1 ← builderAppendCellChecked b0 payload.toCellRemaining
            return (some b1.finalize, true, 1, loaded)

      go rootCell 0 #[]

end TvmLean
