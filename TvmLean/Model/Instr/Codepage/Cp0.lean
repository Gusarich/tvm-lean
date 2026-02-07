import TvmLean.Model.Gas.Constants

namespace TvmLean

def Slice.takeBitsAsNat (s : Slice) (n : Nat) : Except Excno (Nat × Slice) := do
  if s.haveBits n then
    let bs := s.readBits n
    return (bitsToNat bs, s.advanceBits n)
  else
    throw .invOpcode

def Slice.peekBitsAsNat (s : Slice) (n : Nat) : Except Excno Nat := do
  if s.haveBits n then
    return bitsToNat (s.readBits n)
  else
    throw .invOpcode

def Slice.takeRefInv (s : Slice) : Except Excno (Cell × Slice) := do
  if s.haveRefs 1 then
    let c := s.cell.refs[s.refPos]!
    let s' := { s with refPos := s.refPos + 1 }
    return (c, s')
  else
    throw .invOpcode

def natToIntSignedTwos (n bits : Nat) : Int :=
  let half : Nat := 1 <<< (bits - 1)
  if n < half then
    Int.ofNat n
  else
    Int.ofNat n - Int.ofNat (1 <<< bits)

def bitsToIntSignedTwos (bs : BitString) : Int :=
  match bs.size with
  | 0 => 0
  | bits + 1 =>
      let u : Nat := bitsToNat bs
      if bs[0]! then
        Int.ofNat u - Int.ofNat (1 <<< (bits + 1))
      else
        Int.ofNat u

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
def decodeCp0WithBits (s : Slice) : Except Excno (Instr × Nat × Slice) := do
  -- PUSHINT (tinyint4): 4-bit prefix 0x7, 4-bit immediate.
  let p4 ← s.peekBitsAsNat 4
  if p4 = 0x7 then
    let (b8, s') ← s.takeBitsAsNat 8
    let imm4 : Nat := b8 &&& 0xf
    let x : Int := Int.ofNat ((imm4 + 5) &&& 0xf) - 5
    return (.pushInt (.num x), 8, s')

  -- PUSHCONT (tiny, 4-bit prefix 0x9): 4-bit prefix + 4-bit len (bytes), then that many bytes of inline code.
  if p4 = 0x9 then
    let (b8, s8) ← s.takeBitsAsNat 8
    let lenBytes : Nat := b8 &&& 0xf
    let dataBits : Nat := lenBytes * 8
    if !s8.haveBits dataBits then
      throw .invOpcode
    let codeBits := s8.readBits dataBits
    let rest := s8.advanceBits dataBits
    let codeCell : Cell := Cell.mkOrdinary codeBits #[]
    return (.pushCont (Slice.ofCell codeCell), 8, rest)

  -- Exception opcodes: THROW / THROWIF / THROWIFNOT short/long.
  -- Short: 10-bit prefix (0xf200 / 0xf240 / 0xf280 >> 6) + 6-bit excno.
  if s.haveBits 10 then
    let p10 := bitsToNat (s.readBits 10)
    if p10 = (0xf200 >>> 6) ∨ p10 = (0xf240 >>> 6) ∨ p10 = (0xf280 >>> 6) then
      let (_, s10) ← s.takeBitsAsNat 10
      let (exc, s16) ← s10.takeBitsAsNat 6
      let e : Int := Int.ofNat exc
      if p10 = (0xf200 >>> 6) then
        return (.throw e, 16, s16)
      else if p10 = (0xf240 >>> 6) then
        return (.throwIf e, 16, s16)
      else
        return (.throwIfNot e, 16, s16)
  -- Long: 13-bit prefix (0xf2c0 / 0xf2d0 / 0xf2e0 >> 3) + 11-bit excno.
  if s.haveBits 13 then
    let p13 := bitsToNat (s.readBits 13)
    if p13 = (0xf2c0 >>> 3) ∨ p13 = (0xf2d0 >>> 3) ∨ p13 = (0xf2e0 >>> 3) then
      let (_, s13) ← s.takeBitsAsNat 13
      let (exc, s24) ← s13.takeBitsAsNat 11
      let e : Int := Int.ofNat exc
      if p13 = (0xf2c0 >>> 3) then
        return (.throw e, 24, s24)
      else if p13 = (0xf2d0 >>> 3) then
        return (.throwIf e, 24, s24)
      else
        return (.throwIfNot e, 24, s24)

    -- THROWARG / THROWARGIF / THROWARGIFNOT: 13-bit prefix (0xf2c8 / 0xf2d8 / 0xf2e8 >> 3) + 11-bit excno.
    if p13 = (0xf2c8 >>> 3) ∨ p13 = (0xf2d8 >>> 3) ∨ p13 = (0xf2e8 >>> 3) then
      let (_, s13) ← s.takeBitsAsNat 13
      let (exc, s24) ← s13.takeBitsAsNat 11
      let e : Int := Int.ofNat exc
      if p13 = (0xf2c8 >>> 3) then
        return (.throwArg e, 24, s24)
      else if p13 = (0xf2d8 >>> 3) then
        return (.throwArgIf e, 24, s24)
      else
        return (.throwArgIfNot e, 24, s24)

    -- SDBEGINS{Q} (const): 13-bit prefix (0xd728 >> 3) + 8-bit args + inline bits (args*8+3).
    if p13 = (0xd728 >>> 3) then
      if !s.haveBits 21 then
        throw .invOpcode
      let (_, s13) ← s.takeBitsAsNat 13
      let (args8, s21) ← s13.takeBitsAsNat 8
      let quiet : Bool := (args8 &&& 0x80) = 0x80
      let dataBits : Nat := (args8 &&& 0x7f) * 8 + 3
      if !s21.haveBits dataBits then
        throw .invOpcode
      let raw := s21.readBits dataBits
      let rest := s21.advanceBits dataBits
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := Cell.mkOrdinary bits #[]
      return (.sdBeginsConst quiet (Slice.ofCell cell), 21, rest)

  -- DICTPUSHCONST (24-bit, +1 ref): 0xf4a4..0xf4a7 + 10-bit key size.
  if s.haveBits 24 then
    let w24 := bitsToNat (s.readBits 24)

    -- PREVMCBLOCKS / PREVKEYBLOCK / PREVMCBLOCKS_100 (24-bit): 0xf83400..0xf83402.
    if w24 = 0xf83400 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.tonEnvOp .prevMcBlocks, 24, s24)
    if w24 = 0xf83401 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.tonEnvOp .prevKeyBlock, 24, s24)
    if w24 = 0xf83402 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.tonEnvOp .prevMcBlocks100, 24, s24)

    -- BLS_* (24-bit): 0xf93000..0xf93031.
    if w24 >>> 8 = 0xf930 then
      let op : Nat := w24 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      match op with
      | 0x00 => return (.cryptoOp (.ext .blsVerify), 24, s24)
      | 0x01 => return (.cryptoOp (.ext .blsAggregate), 24, s24)
      | 0x02 => return (.cryptoOp (.ext .blsFastAggregateVerify), 24, s24)
      | 0x03 => return (.cryptoOp (.ext .blsAggregateVerify), 24, s24)
      | 0x10 => return (.cryptoOp (.ext .blsG1Add), 24, s24)
      | 0x11 => return (.cryptoOp (.ext .blsG1Sub), 24, s24)
      | 0x12 => return (.cryptoOp (.ext .blsG1Neg), 24, s24)
      | 0x13 => return (.cryptoOp (.ext .blsG1Mul), 24, s24)
      | 0x14 => return (.cryptoOp (.ext .blsG1MultiExp), 24, s24)
      | 0x15 => return (.cryptoOp (.ext .blsG1Zero), 24, s24)
      | 0x16 => return (.cryptoOp (.ext .blsMapToG1), 24, s24)
      | 0x17 => return (.cryptoOp (.ext .blsG1InGroup), 24, s24)
      | 0x18 => return (.cryptoOp (.ext .blsG1IsZero), 24, s24)
      | 0x20 => return (.cryptoOp (.ext .blsG2Add), 24, s24)
      | 0x21 => return (.cryptoOp (.ext .blsG2Sub), 24, s24)
      | 0x22 => return (.cryptoOp (.ext .blsG2Neg), 24, s24)
      | 0x23 => return (.cryptoOp (.ext .blsG2Mul), 24, s24)
      | 0x24 => return (.cryptoOp (.ext .blsG2MultiExp), 24, s24)
      | 0x25 => return (.cryptoOp (.ext .blsG2Zero), 24, s24)
      | 0x26 => return (.cryptoOp (.ext .blsMapToG2), 24, s24)
      | 0x27 => return (.cryptoOp (.ext .blsG2InGroup), 24, s24)
      | 0x28 => return (.cryptoOp (.ext .blsG2IsZero), 24, s24)
      | 0x30 => return (.cryptoOp (.ext .blsPairing), 24, s24)
      | 0x31 => return (.cryptoOp (.ext .blsPushR), 24, s24)
      | _ => throw .invOpcode

    -- BCHKBITS / BCHKBITSQ (24-bit): 16-bit opcode 0xcf38/0xcf3c + 8-bit arg (bits-1).
    let p16 := w24 >>> 8
    if p16 = 0xcf38 ∨ p16 = 0xcf3c then
      let bits : Nat := (w24 &&& 0xff) + 1
      let quiet : Bool := p16 = 0xcf3c
      let (_, s24) ← s.takeBitsAsNat 24
      return (.cellOp (.bchkBitsImm bits quiet), 24, s24)

    -- GETPARAMLONG / INMSGPARAMS (24-bit): 0xf88100..0xf881ff.
    if w24 >>> 8 = 0xf881 then
      let idx : Nat := w24 &&& 0xff
      -- C++ uses two fixed ranges with an exclusive upper bound; 0xff is reserved/invalid.
      if idx = 0xff then
        throw .invOpcode
      let (_, s24) ← s.takeBitsAsNat 24
      return (.tonEnvOp (.getParam idx), 24, s24)
    if 0xf4a400 ≤ w24 ∧ w24 < 0xf4a800 then
      if !s.haveRefs 1 then
        throw .invOpcode
      -- Layout (pfx_bits=24):
      --   advance 13; take 1 bit (maybe), take 1 ref; take 10-bit n.
      let (_, s13) ← s.takeBitsAsNat 13
      let (_, s14) ← s13.takeBitsAsNat 1
      let (dictCell, sRef) ← s14.takeRefInv
      let (n, s24) ← sRef.takeBitsAsNat 10
      return (.dictPushConst dictCell n, 24, s24)

    -- PFXDICTSWITCH (24-bit, +1 ref): 14-bit prefix 0x3d2b + 10-bit key_len, then 1 ref (dict).
    if w24 >>> 10 = 0x3d2b then
      if !s.haveRefs 1 then
        throw .invOpcode
      let keyLen : Nat := w24 &&& 0x3ff
      let (_, s24) ← s.takeBitsAsNat 24
      let (dictCell, rest) ← s24.takeRefInv
      return (.dictExt (.pfxSwitch dictCell keyLen), 24, rest)

    -- PREPAREDICT <idx> (24-bit): 10-bit prefix (0xf180 >> 6) + 14-bit args.
    -- Matches C++ `exec_preparedict` (contops.cpp).
    let p10 := w24 >>> 14
    if p10 = (0xf180 >>> 6) then
      let idx : Nat := w24 &&& 0x3fff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.prepareDict idx, 24, s24)

    -- CALLDICT_LONG / JMPDICT (24-bit): 10-bit prefix (0x3c4/0x3c5) + 14-bit args.
    if p10 = 0x3c4 then
      let idx : Nat := w24 &&& 0x3fff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.callDict idx, 24, s24)
    if p10 = 0x3c5 then
      let idx : Nat := w24 &&& 0x3fff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt (.jmpDict idx), 24, s24)

    -- SETCONTCTRMANY (24-bit): 16-bit opcode 0xede3 + 8-bit arg (mask).
    let p16 := w24 >>> 8
    if p16 = 0xede3 then
      let mask : Nat := w24 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt (.setContCtrMany mask), 24, s24)

    -- RUNVM (24-bit): 12-bit prefix (0xdb4) + 12-bit mode.
    if w24 >>> 12 = 0xdb4 then
      let mode : Nat := w24 &&& 0xfff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt (.runvm mode), 24, s24)

    -- HASHEXT (24-bit): 14-bit prefix (0xf904 >> 2) + 10-bit args (hash_id8 + rev + append).
    -- Matches C++ `exec_hash_ext` / `dump_hash_ext` (TON version >= 4).
    let p14 := w24 >>> 10
    if p14 = (0xf904 >>> 2) then
      let args10 : Nat := w24 &&& 0x3ff
      let rev : Bool := ((args10 >>> 8) &&& 1) = 1
      let append : Bool := ((args10 >>> 9) &&& 1) = 1
      let hashId : Nat := args10 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.cryptoOp (.hashExt hashId append rev), 24, s24)

    -- {P}LDSLICE{Q} <bits> (24-bit): 14-bit prefix (0xd71c >> 2) + 10-bit args (flags2 + bits8).
    -- Matches C++ `exec_load_slice_fixed2`.
    if p14 = (0xd71c >>> 2) then
      let args10 : Nat := w24 &&& 0x3ff
      let flags2 : Nat := args10 >>> 8
      let bits : Nat := (args10 &&& 0xff) + 1
      let prefetch : Bool := (flags2 &&& 1) = 1
      let quiet : Bool := (flags2 &&& 2) = 2
      let (_, s24) ← s.takeBitsAsNat 24
      return (.loadSliceFixed prefetch quiet bits, 24, s24)

    -- QLSHIFT / QRSHIFT (24-bit): 16-bit opcode 0xb7aa/0xb7ab + 8-bit arg.
    if p16 = 0xb7aa then
      let bits : Nat := (w24 &&& 0xff) + 1
      let (_, s24) ← s.takeBitsAsNat 24
      return (.lshiftConst true bits, 24, s24)
    if p16 = 0xb7ab then
      let bits : Nat := (w24 &&& 0xff) + 1
      let (_, s24) ← s.takeBitsAsNat 24
      return (.rshiftConst true bits, 24, s24)
    if w24 = 0xb7b600 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt .qfitsx, 24, s24)
    if w24 = 0xb7b601 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt .qufitsx, 24, s24)
    if w24 = 0xb7b602 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt .qbitsize, 24, s24)
    if w24 = 0xb7b603 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.ubitsize true, 24, s24)
    if w24 = 0xb7b608 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.contExt .qmin, 24, s24)
    if w24 = 0xb7b609 then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.qmax, 24, s24)
    if w24 = 0xb7b60b then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.abs true, 24, s24)
    if w24 = 0xb7b60a then
      let (_, s24) ← s.takeBitsAsNat 24
      return (.qminmax, 24, s24)

    -- QADDINT / QMULINT (24-bit): 0xb7a6/0xb7a7 + imm8.
    if p16 = 0xb7a6 then
      let imm8 : Nat := w24 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.arithExt (.qaddInt (natToIntSignedTwos imm8 8)), 24, s24)
    if p16 = 0xb7a7 then
      let imm8 : Nat := w24 &&& 0xff
      let (_, s24) ← s.takeBitsAsNat 24
      return (.arithExt (.qmulInt (natToIntSignedTwos imm8 8)), 24, s24)

    -- QEQINT / QLESSINT / QGTINT / QNEQINT (24-bit): 0xb7c0..0xb7c3 + imm8.
    if 0xb7c0 ≤ p16 ∧ p16 ≤ 0xb7c3 then
      let imm8 : Nat := w24 &&& 0xff
      let n : Int := natToIntSignedTwos imm8 8
      let (_, s24) ← s.takeBitsAsNat 24
      match p16 with
      | 0xb7c0 => return (.eqInt n, 24, s24)
      | 0xb7c1 => return (.lessInt n, 24, s24)
      | 0xb7c2 => return (.gtInt n, 24, s24)
      | _ => return (.neqInt n, 24, s24)

    -- QFITS / QUFITS (24-bit): 0xb7b4/0xb7b5 + width8 (delta=1).
    if p16 = 0xb7b4 ∨ p16 = 0xb7b5 then
      let bits : Nat := (w24 &&& 0xff) + 1
      let unsigned : Bool := p16 = 0xb7b5
      let (_, s24) ← s.takeBitsAsNat 24
      return (.arithExt (.fitsConst unsigned true bits), 24, s24)

    -- QDIV/MOD family (24-bit): 20-bit prefix 0xb7a90 + 4-bit args.
    let p20 := w24 >>> 4
    if p20 = 0xb7a90 then
      let args4 : Nat := w24 &&& 0xf
      let roundEnc : Nat := args4 &&& 0x3
      let dEnc : Nat := (args4 >>> 2) &&& 0x3
      if roundEnc = 3 then
        throw .invOpcode
      let roundMode : Int := Int.ofNat roundEnc - 1
      let (d, add) : (Nat × Bool) :=
        if dEnc = 0 then
          (3, true)
        else
          (dEnc, false)
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s24) ← s.takeBitsAsNat 24
      return (.divMod d roundMode add true, 24, s24)

    -- QMUL{DIV,MOD,DIVMOD} family (24-bit): 20-bit prefix 0xb7a98 + 4-bit args.
    if p20 = 0xb7a98 then
      let args4 : Nat := w24 &&& 0xf
      let roundEnc : Nat := args4 &&& 0x3
      let dEnc : Nat := (args4 >>> 2) &&& 0x3
      if roundEnc = 3 then
        throw .invOpcode
      let roundMode : Int := Int.ofNat roundEnc - 1
      let (d, add) : (Nat × Bool) :=
        if dEnc = 0 then
          (3, true)
        else
          (dEnc, false)
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s24) ← s.takeBitsAsNat 24
      return (.mulDivMod d roundMode add true, 24, s24)

    -- RIST255_Q* (24-bit): 0xb7f921..0xb7f925.
    if w24 >>> 8 = 0xb7f9 then
      let (_, s24) ← s.takeBitsAsNat 24
      match w24 &&& 0xff with
      | 0x21 => return (.cryptoOp (.ext .rist255Qvalidate), 24, s24)
      | 0x22 => return (.cryptoOp (.ext .rist255Qadd), 24, s24)
      | 0x23 => return (.cryptoOp (.ext .rist255Qsub), 24, s24)
      | 0x24 => return (.cryptoOp (.ext .rist255Qmul), 24, s24)
      | 0x25 => return (.cryptoOp (.ext .rist255QmulBase), 24, s24)
      | _ => throw .invOpcode

    -- Q-shrmod/shldivmod families (24-bit): 0xb7 + 16-bit opcode in the 0xa9** range.
    if w24 >>> 16 = 0xb7 then
      let op16 : Nat := w24 &&& 0xffff
      let roundOfs (ofs : Nat) : Int := Int.ofNat ofs - 1

      let decodeShrMod (start d : Nat) (mul add : Bool) : Option Instr :=
        if start ≤ op16 ∧ op16 ≤ start + 2 then
          let ofs : Nat := op16 - start
          some (.arithExt (.shrMod mul add d (roundOfs ofs) true none))
        else
          none

      let decodeShlDivMod (start d : Nat) (addMode : Bool) : Option Instr :=
        if start ≤ op16 ∧ op16 ≤ start + 2 then
          let ofs : Nat := op16 - start
          some (.arithExt (.shlDivMod d (roundOfs ofs) addMode true none))
        else
          none

      let candidates : List (Option Instr) :=
        [ decodeShrMod 0xa920 3 false true
        , decodeShrMod 0xa924 1 false false
        , decodeShrMod 0xa928 2 false false
        , decodeShrMod 0xa92c 3 false false
        , decodeShrMod 0xa9a0 3 true true
        , decodeShrMod 0xa9a4 1 true false
        , decodeShrMod 0xa9a8 2 true false
        , decodeShrMod 0xa9ac 3 true false
        , decodeShlDivMod 0xa9c0 3 true
        , decodeShlDivMod 0xa9c4 1 false
        , decodeShlDivMod 0xa9c8 2 false
        , decodeShlDivMod 0xa9cc 3 false
        ]
      let instr? : Option Instr := candidates.findSome? (fun x => x)

      match instr? with
      | some instr =>
          let (_, s24) ← s.takeBitsAsNat 24
          return (instr, 24, s24)
      | none =>
          pure ()

    -- {RSHIFT,MODPOW2,RSHIFTMOD}# and related pow2 shift/divmod ops (24-bit): 16-bit opcode + arg8 (delta=1).
    if (0xa930 ≤ p16 ∧ p16 ≤ 0xa93e) ∨ (0xa9b0 ≤ p16 ∧ p16 ≤ 0xa9b2) ∨ (0xa9d0 ≤ p16 ∧ p16 ≤ 0xa9de) then
      let z : Nat := (w24 &&& 0xff) + 1
      let roundOfs (ofs : Nat) : Int := Int.ofNat ofs - 1
      let (_, s24) ← s.takeBitsAsNat 24
      if 0xa930 ≤ p16 ∧ p16 ≤ 0xa932 then
        let ofs : Nat := p16 - 0xa930
        return (.arithExt (.shrMod false true 3 (roundOfs ofs) false (some z)), 24, s24)
      if 0xa934 ≤ p16 ∧ p16 ≤ 0xa936 then
        let ofs : Nat := p16 - 0xa934
        return (.arithExt (.shrMod false false 1 (roundOfs ofs) false (some z)), 24, s24)
      if 0xa938 ≤ p16 ∧ p16 ≤ 0xa93a then
        let ofs : Nat := p16 - 0xa938
        return (.arithExt (.shrMod false false 2 (roundOfs ofs) false (some z)), 24, s24)
      if 0xa93c ≤ p16 ∧ p16 ≤ 0xa93e then
        let ofs : Nat := p16 - 0xa93c
        return (.arithExt (.shrMod false false 3 (roundOfs ofs) false (some z)), 24, s24)
      if 0xa9b0 ≤ p16 ∧ p16 ≤ 0xa9b2 then
        let ofs : Nat := p16 - 0xa9b0
        return (.arithExt (.shrMod true true 3 (roundOfs ofs) false (some z)), 24, s24)
      if 0xa9d0 ≤ p16 ∧ p16 ≤ 0xa9d2 then
        let ofs : Nat := p16 - 0xa9d0
        return (.arithExt (.shlDivMod 3 (roundOfs ofs) true false (some z)), 24, s24)
      if 0xa9d4 ≤ p16 ∧ p16 ≤ 0xa9d6 then
        let ofs : Nat := p16 - 0xa9d4
        return (.arithExt (.shlDivMod 1 (roundOfs ofs) false false (some z)), 24, s24)
      if 0xa9d8 ≤ p16 ∧ p16 ≤ 0xa9da then
        let ofs : Nat := p16 - 0xa9d8
        return (.arithExt (.shlDivMod 2 (roundOfs ofs) false false (some z)), 24, s24)
      if 0xa9dc ≤ p16 ∧ p16 ≤ 0xa9de then
        let ofs : Nat := p16 - 0xa9dc
        return (.arithExt (.shlDivMod 3 (roundOfs ofs) false false (some z)), 24, s24)
      throw .invOpcode

    -- Integer load from slice: 13-bit prefix (0xd708 >> 3) + 11-bit args.
    -- Matches C++ `exec_load_int_fixed2`.
    let p13 := w24 >>> 11
    if p13 = (0xd708 >>> 3) then
      let args11 : Nat := w24 &&& 0x7ff
      let flags3 : Nat := args11 >>> 8
      let bits : Nat := (args11 &&& 0xff) + 1
      let unsigned : Bool := (flags3 &&& 1) = 1
      let prefetch : Bool := (flags3 &&& 2) = 2
      let quiet : Bool := (flags3 &&& 4) = 4
      let (_, s24) ← s.takeBitsAsNat 24
      return (.loadInt unsigned prefetch quiet bits, 24, s24)

    -- ST{I,U}{R}{Q} <bits> (24-bit): 13-bit prefix (0xcf08 >> 3) + 11-bit args (flags3 + bits8).
    -- Matches C++ `exec_store_int_fixed`.
    if p13 = (0xcf08 >>> 3) then
      let args11 : Nat := w24 &&& 0x7ff
      let flags3 : Nat := args11 >>> 8
      let bits : Nat := (args11 &&& 0xff) + 1
      let unsigned : Bool := (flags3 &&& 1) = 1
      let rev : Bool := (flags3 &&& 2) = 2
      let quiet : Bool := (flags3 &&& 4) = 4
      let (_, s24) ← s.takeBitsAsNat 24
      return (.stIntFixed unsigned rev quiet bits, 24, s24)

    -- XC2PU: 12-bit prefix 0x541 + 12-bit args (x,y,z nibbles).
    let p12 := w24 >>> 12
    if p12 = 0x540 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xchg3 x y z, 24, s24)
    if p12 = 0x541 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xc2pu x y z, 24, s24)
    if p12 = 0x542 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xcpuxc x y z, 24, s24)
    if p12 = 0x543 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.xcpu2 x y z, 24, s24)
    if p12 = 0x544 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.puxc2 x y z, 24, s24)
    if p12 = 0x545 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.puxcpu x y z, 24, s24)
    if p12 = 0x546 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.pu2xc x y z, 24, s24)
    if p12 = 0x547 then
      let args12 : Nat := w24 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s24) ← s.takeBitsAsNat 24
      return (.push3 x y z, 24, s24)

    -- MUL{RSHIFT,MODPOW2,RSHIFTMOD}# (24-bit): 12-bit prefix 0xa9b + 12-bit args (cfg4 + z8).
    if p12 = 0xa9b then
      let args12 : Nat := w24 &&& 0xfff
      let cfg4 : Nat := args12 >>> 8
      let z : Nat := (args12 &&& 0xff) + 1
      let roundMode : Int := Int.ofNat (cfg4 &&& 0x3) - 1
      let d : Nat := (cfg4 >>> 2) &&& 0x3
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s24) ← s.takeBitsAsNat 24
      return (.mulShrModConst d roundMode z, 24, s24)

  -- PUSHCONT (general, 7-bit prefix 0x47): 7-bit prefix + 9-bit args + inline bits + inline refs.
  if s.haveBits 16 then
    let w16 := bitsToNat (s.readBits 16)
    let p7 := w16 >>> 9
    if p7 = 0x47 then
      let args9 : Nat := w16 &&& 0x1ff
      let refs : Nat := (args9 >>> 7) &&& 0x3
      let lenBytes : Nat := args9 &&& 0x7f
      let dataBits : Nat := lenBytes * 8
      if !s.haveBits (16 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      let codeBits := s16.readBits dataBits
      let mut rest := s16.advanceBits dataBits
      let mut contRefs : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        contRefs := contRefs.push c
        rest := rest'
      let codeCell : Cell := Cell.mkOrdinary codeBits contRefs
      return (.pushCont (Slice.ofCell codeCell), 16, rest)

  -- PUSHSLICE r2 (18-bit prefix): 0x8d + 3-bit refs (0..4) + 7-bit len, then inline bits/refs.
  -- Matches C++ `exec_push_slice_r2`.
  if s.haveBits 18 then
    let w18 := bitsToNat (s.readBits 18)
    if w18 >>> 10 = 0x8d then
      let refs : Nat := (w18 >>> 7) &&& 0x7
      if refs > 4 then
        throw .invOpcode
      let len7 : Nat := w18 &&& 0x7f
      let dataBits : Nat := len7 * 8 + 6
      if !s.haveBits (18 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s18) ← s.takeBitsAsNat 18
      let raw := s18.readBits dataBits
      let mut rest := s18.advanceBits dataBits
      let mut refCells : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        refCells := refCells.push c
        rest := rest'
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := Cell.mkOrdinary bits refCells
      return (.pushSliceConst (Slice.ofCell cell), 18, rest)

  -- PUSHSLICE_REFS (15-bit prefix): 0x8c + r:2 + bits:5, then (r+1) refs and (8*bits+1) inline bits.
  -- Matches C++ `exec_push_slice_r`.
  if s.haveBits 15 then
    let w15 := bitsToNat (s.readBits 15)
    if w15 >>> 7 = 0x8c then
      let r : Nat := (w15 >>> 5) &&& 0x3
      let bits5 : Nat := w15 &&& 0x1f
      let refs : Nat := r + 1
      let dataBits : Nat := bits5 * 8 + 1
      if !s.haveBits (15 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s15) ← s.takeBitsAsNat 15
      let raw := s15.readBits dataBits
      let mut rest := s15.advanceBits dataBits
      let mut refCells : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        refCells := refCells.push c
        rest := rest'
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := Cell.mkOrdinary bits refCells
      return (.pushSliceConst (Slice.ofCell cell), 15, rest)

  -- PUSHINT (8/16/long)
  -- STSLICECONST (inline constant slice): 9-bit prefix 0xcf80>>7 + 5-bit args, then inline slice bits/refs.
  if s.haveBits 14 then
    let w14 := bitsToNat (s.readBits 14)
    if w14 >>> 5 = (0xcf80 >>> 7) then
      let args5 : Nat := w14 &&& 0x1f
      let refs : Nat := (args5 >>> 3) &&& 0x3
      let dataBits : Nat := (args5 &&& 0x7) * 8 + 2
      if !s.haveBits (14 + dataBits) then
        throw .invOpcode
      if !s.haveRefs refs then
        throw .invOpcode
      let (_, s14) ← s.takeBitsAsNat 14
      let raw := s14.readBits dataBits
      let mut rest := s14.advanceBits dataBits
      let mut rs : Array Cell := #[]
      for _ in [0:refs] do
        let (c, rest') ← rest.takeRefInv
        rs := rs.push c
        rest := rest'
      let bits := bitsStripTrailingMarker raw
      let cell : Cell := Cell.mkOrdinary bits rs
      return (.stSliceConst (Slice.ofCell cell), 14, rest)

  let b8 ← s.peekBitsAsNat 8
  -- PUSHREF / PUSHREFSLICE: 0x88/0x89 (8) + 1 ref.
  if b8 = 0x88 then
    if !s.haveRefs 1 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (c, s') ← s8.takeRefInv
    return (.pushRef c, 8, s')
  if b8 = 0x89 then
    if !s.haveRefs 1 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (c, s') ← s8.takeRefInv
    return (.pushRefSlice c, 8, s')
  -- PUSHREFCONT: 0x8a (8) + 1 ref.
  if b8 = 0x8a then
    if !s.haveRefs 1 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (c, s') ← s8.takeRefInv
    return (.pushRefCont c, 8, s')
  -- PUSHSLICE (const): 0x8b (8) + 4-bit args, then inline bits (args*8+4); strip trailing marker.
  if b8 = 0x8b then
    if !s.haveBits 12 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (args4, s12) ← s8.takeBitsAsNat 4
    let dataBits : Nat := (args4 &&& 0xf) * 8 + 4
    if !s12.haveBits dataBits then
      throw .invOpcode
    let raw := s12.readBits dataBits
    let rest := s12.advanceBits dataBits
    let bits := bitsStripTrailingMarker raw
    let cell : Cell := Cell.mkOrdinary bits #[]
    return (.pushSliceConst (Slice.ofCell cell), 12, rest)
  if b8 = 0x80 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.pushInt (.num (natToIntSignedTwos arg 8)), 16, s16)
  if b8 = 0x81 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s24) ← s8.takeBitsAsNat 16
    return (.pushInt (.num (natToIntSignedTwos arg 16)), 24, s24)
  if b8 = 0x82 then
    -- Extended constant: 0x82 (8) + len (5) + value (3 + 8*(len+2)).
    if !s.haveBits 13 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (len5, s13) ← s8.takeBitsAsNat 5
    -- C++ reserves len=31; upper bound of mkextrange is exclusive.
    if len5 = 31 then
      throw .invOpcode
    let l : Nat := len5 + 2
    let width : Nat := 3 + l * 8
    if !s13.haveBits width then
      throw .invOpcode
    let bs := s13.readBits width
    let s' := s13.advanceBits width
    return (.pushInt (.num (bitsToIntSignedTwos bs)), 13, s')

  -- 16-bit control register ops: PUSH c<i>, POP c<i>.
  if s.haveBits 16 then
    let w16 := bitsToNat (s.readBits 16)
    -- PLDUZ: 13-bit prefix (0x1ae2) + 3-bit arg.
    if w16 >>> 3 = 0x1ae2 then
      let c : Nat := w16 &&& 0x7
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.plduz c), 16, s16)
    -- ST{I,U}X{R}{Q}: 0xcf00..0xcf07 (16-bit; 13-bit prefix + 3-bit flags).
    if w16 &&& 0xfff8 = 0xcf00 then
      let args3 : Nat := w16 &&& 0x7
      let unsigned : Bool := (args3 &&& 1) = 1
      let rev : Bool := (args3 &&& 2) = 2
      let quiet : Bool := (args3 &&& 4) = 4
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stIntVar unsigned rev quiet, 16, s16)
    if w16 = 0xcf30 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .bdepth, 16, s16)
    if w16 = 0xcf31 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.bbits, 16, s16)
    if w16 = 0xcf32 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .brefs, 16, s16)
    if w16 = 0xcf33 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .bbitrefs, 16, s16)
    if w16 = 0xcf35 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .brembits, 16, s16)
    if w16 = 0xcf36 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .bremrefs, 16, s16)
    if w16 = 0xcf37 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .brembitrefs, 16, s16)
    if w16 = 0xcf39 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true false false), 16, s16)
    if w16 = 0xcf3a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk false true false), 16, s16)
    if w16 = 0xcf3b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true true false), 16, s16)
    if w16 = 0xcf3d then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true false true), 16, s16)
    if w16 = 0xcf3e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk false true true), 16, s16)
    if w16 = 0xcf3f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.bchk true true true), 16, s16)
    -- THROW{ARG}ANY{IF,IFNOT}: 0xf2f0..0xf2f6 (16-bit, 3-bit args).
    if w16 &&& 0xfff8 = 0xf2f0 then
      let args3 : Nat := w16 &&& 0x7
      if args3 ≤ 6 then
        let hasParam : Bool := (args3 &&& 1) = 1
        let hasCond : Bool := (args3 &&& 6) ≠ 0
        let throwCond : Bool := (args3 &&& 2) = 2
        let (_, s16) ← s.takeBitsAsNat 16
        return (.throwAny hasParam hasCond throwCond, 16, s16)
    if w16 = 0xf2ff then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.try_, 16, s16)
    -- TRYARGS <p>,<r>: 0xf3 (8-bit) + args8 (p:4, r:4).
    if w16 &&& 0xff00 = 0xf300 then
      let args8 : Nat := w16 &&& 0xff
      let params : Nat := (args8 >>> 4) &&& 0xf
      let retVals : Nat := args8 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tryArgs params retVals, 16, s16)
    -- XCHG3 (16-bit): 4-bit prefix 0x4 + 12-bit args (x,y,z nibbles).
    if w16 >>> 12 = 0x4 then
      let args12 : Nat := w16 &&& 0xfff
      let x : Nat := (args12 >>> 8) &&& 0xf
      let y : Nat := (args12 >>> 4) &&& 0xf
      let z : Nat := args12 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.xchg3 x y z, 16, s16)
    -- BLKDROP (16-bit): 12-bit prefix 0x5f0 + 4-bit `n`.
    if w16 &&& 0xfff0 = 0x5f00 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blkdrop n, 16, s16)
    -- BLKPUSH: 0x5f10..0x5fff (8-bit args packed as nibbles).
    if w16 &&& 0xff00 = 0x5f00 ∧ (w16 &&& 0xff) ≥ 0x10 then
      let args8 : Nat := w16 &&& 0xff
      let x : Nat := (args8 >>> 4) &&& 0xf
      let y : Nat := args8 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blkPush x y, 16, s16)
    -- BLKDROP2: 0x6c10..0x6cff (8-bit args packed as nibbles).
    if w16 &&& 0xff00 = 0x6c00 ∧ (w16 &&& 0xff) ≥ 0x10 then
      let args8 : Nat := w16 &&& 0xff
      let x : Nat := (args8 >>> 4) &&& 0xf
      let y : Nat := args8 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blkdrop2 x y, 16, s16)
    -- TUPLE (12-bit prefix 0x6f0 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f00 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.mktuple n), 16, s16)
    -- INDEX (12-bit prefix 0x6f1 + 4-bit `i`).
    if w16 &&& 0xfff0 = 0x6f10 then
      let i : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.index i), 16, s16)
    -- UNTUPLE (12-bit prefix 0x6f2 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f20 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.untuple n), 16, s16)
    -- UNPACKFIRST (12-bit prefix 0x6f3 + 4-bit `n`).
    if w16 &&& 0xfff0 = 0x6f30 then
      let n : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.unpackFirst n), 16, s16)
    -- EXPLODE (12-bit prefix 0x6f4 + 4-bit `max_len`).
    if w16 &&& 0xfff0 = 0x6f40 then
      let maxLen : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.explode maxLen), 16, s16)
    -- SETINDEX (12-bit prefix 0x6f5 + 4-bit `idx`).
    if w16 &&& 0xfff0 = 0x6f50 then
      let idx : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.setIndex idx), 16, s16)
    -- INDEXQ (12-bit prefix 0x6f6 + 4-bit `idx`).
    if w16 &&& 0xfff0 = 0x6f60 then
      let idx : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.indexQ idx), 16, s16)
    -- SETINDEXQ (12-bit prefix 0x6f7 + 4-bit `idx`).
    if w16 &&& 0xfff0 = 0x6f70 then
      let idx : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.setIndexQ idx), 16, s16)

    -- TUPLEVAR / INDEXVAR / UNTUPLEVAR / UNPACKFIRSTVAR / EXPLODEVAR / SETINDEXVAR / INDEXVARQ / SETINDEXVARQ.
    if 0x6f80 ≤ w16 ∧ w16 ≤ 0x6f87 then
      let (_, s16) ← s.takeBitsAsNat 16
      match w16 with
      | 0x6f80 => return (.tupleOp .mktupleVar, 16, s16)
      | 0x6f81 => return (.tupleOp .indexVar, 16, s16)
      | 0x6f82 => return (.tupleOp .untupleVar, 16, s16)
      | 0x6f83 => return (.tupleOp .unpackFirstVar, 16, s16)
      | 0x6f84 => return (.tupleOp .explodeVar, 16, s16)
      | 0x6f85 => return (.tupleOp .setIndexVar, 16, s16)
      | 0x6f86 => return (.tupleOp .indexVarQ, 16, s16)
      | _ => return (.tupleOp .setIndexVarQ, 16, s16)

    -- TLEN / QTLEN / ISTUPLE / LAST / TPUSH / TPOP.
    if 0x6f88 ≤ w16 ∧ w16 ≤ 0x6f8d then
      let (_, s16) ← s.takeBitsAsNat 16
      match w16 with
      | 0x6f88 => return (.tupleOp .tlen, 16, s16)
      | 0x6f89 => return (.tupleOp .qtlen, 16, s16)
      | 0x6f8a => return (.tupleOp .isTuple, 16, s16)
      | 0x6f8b => return (.tupleOp .last, 16, s16)
      | 0x6f8c => return (.tupleOp .tpush, 16, s16)
      | _ => return (.tupleOp .tpop, 16, s16)

    -- INDEX2 (12-bit prefix 0x6fb + 4-bit args).
    if w16 &&& 0xfff0 = 0x6fb0 then
      let args4 : Nat := w16 &&& 0xf
      let i : Nat := (args4 >>> 2) &&& 3
      let j : Nat := args4 &&& 3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.index2 i j), 16, s16)

    -- INDEX3 (10-bit prefix 0x6fc>>2 + 6-bit args).
    if w16 &&& 0xffc0 = 0x6fc0 then
      let args6 : Nat := w16 &&& 0x3f
      let i : Nat := (args6 >>> 4) &&& 3
      let j : Nat := (args6 >>> 2) &&& 3
      let k : Nat := args6 &&& 3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tupleOp (.index3 i j k), 16, s16)
    if w16 = 0x6fa0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIf, 16, s16)
    if w16 = 0x6fa1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIfNot, 16, s16)
    if w16 = 0x6fa2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIf, 16, s16)
    if w16 = 0x6fa3 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIfNot, 16, s16)
    if w16 = 0x6fa4 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIf2, 16, s16)
    if w16 = 0x6fa5 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullSwapIfNot2, 16, s16)
    if w16 = 0x6fa6 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIf2, 16, s16)
    if w16 = 0x6fa7 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.nullRotrIfNot2, 16, s16)
    if w16 = 0xc700 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sempty, 16, s16)
    if w16 = 0xc701 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdempty, 16, s16)
    if w16 = 0xc702 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.srempty, 16, s16)
    if w16 = 0xc703 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdFirst, 16, s16)
    if w16 = 0xc710 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdCntLead0, 16, s16)
    if w16 = 0xc712 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdCntTrail0, 16, s16)
    if w16 = 0xc711 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdCntLead1, 16, s16)
    if w16 = 0xc713 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdCntTrail1, 16, s16)
    if w16 = 0xc705 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdEq, 16, s16)
    if w16 = 0xc704 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdLexCmp, 16, s16)
    if w16 = 0xc708 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPfx, 16, s16)
    if w16 = 0xc709 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPfxRev, 16, s16)
    if w16 = 0xc70a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPpfx, 16, s16)
    if w16 = 0xc70b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdPpfxRev, 16, s16)
    if w16 = 0xc70c then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdSfx, 16, s16)
    if w16 = 0xc70d then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdSfxRev, 16, s16)
    if w16 = 0xc70e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdPsfx, 16, s16)
    if w16 = 0xc70f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdPsfxRev, 16, s16)
    if w16 = 0xd720 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdcutfirst, 16, s16)
    if w16 = 0xd721 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdskipfirst, 16, s16)
    if w16 = 0xd722 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdcutlast, 16, s16)
    if w16 = 0xd723 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdskiplast, 16, s16)
    if w16 = 0xd724 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdSubstr, 16, s16)
    if w16 = 0xd730 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .scutfirst, 16, s16)
    if w16 = 0xd731 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sskipfirst, 16, s16)
    if w16 = 0xd732 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .scutlast, 16, s16)
    if w16 = 0xd733 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sskiplast, 16, s16)
    if w16 = 0xcf14 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.strefR false), 16, s16)
    if w16 = 0xcf1c then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.strefR true), 16, s16)
    if w16 = 0xcf23 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .endxc, 16, s16)
    if w16 = 0xb600 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .fitsx, 16, s16)
    if w16 = 0xb601 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .ufitsx, 16, s16)
    if w16 = 0xb608 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.min, 16, s16)
    if w16 = 0xb609 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.max, 16, s16)
    if w16 = 0xb60a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.minmax, 16, s16)
    if w16 = 0xb602 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.bitsize, 16, s16)
    if w16 = 0xb60b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.abs false, 16, s16)
    if w16 = 0xb603 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.ubitsize false, 16, s16)
    if w16 = 0xb7a0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qadd, 16, s16)
    if w16 = 0xb7a1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qsub, 16, s16)
    if w16 = 0xb7a2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qsubr, 16, s16)
    if w16 = 0xb7a8 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qmul, 16, s16)
    if w16 = 0xb7a3 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qnegate, 16, s16)
    if w16 = 0xb7a4 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qinc, 16, s16)
    if w16 = 0xb7a5 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qdec, 16, s16)
    -- QLSHIFT_VAR / QRSHIFT_VAR (16-bit): 0xb7ac/0xb7ad.
    if w16 = 0xb7ac then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.arithExt (.lshiftVar true), 16, s16)
    if w16 = 0xb7ad then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.arithExt (.rshiftVar true), 16, s16)
    if w16 = 0xb7ae then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qpow2, 16, s16)
    if w16 = 0xb7b0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qand, 16, s16)
    if w16 = 0xb7b1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qor, 16, s16)
    if w16 = 0xb7b2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qxor, 16, s16)
    if w16 = 0xb7b3 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qnot, 16, s16)
    if w16 = 0xb7b8 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qsgn, 16, s16)
    if w16 = 0xb7b9 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qless, 16, s16)
    if w16 = 0xb7ba then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qequal, 16, s16)
    if w16 = 0xb7bb then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qleq, 16, s16)
    if w16 = 0xb7bc then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qgreater, 16, s16)
    if w16 = 0xb7bd then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qneq, 16, s16)
    if w16 = 0xb7be then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .qgeq, 16, s16)
    if w16 = 0xb7bf then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.qcmp, 16, s16)
    -- PUSHPOW2 / PUSHNAN: 0x8300..0x83ff.
    if w16 &&& 0xff00 = 0x8300 then
      let (_, s16) ← s.takeBitsAsNat 16
      if w16 = 0x83ff then
        return (.pushInt .nan, 16, s16)
      else
        let exp : Nat := (w16 &&& 0xff) + 1
        return (.pushPow2 exp, 16, s16)
    -- LDSLICE <bits> (16-bit): 0xd6 (8) + <bits-1> (8).
    if w16 &&& 0xff00 = 0xd600 then
      let bits : Nat := (w16 &&& 0xff) + 1
      let (_, s16) ← s.takeBitsAsNat 16
      return (.loadSliceFixed false false bits, 16, s16)
    -- {PLD,LD}{I,U}X{Q}: 0xd700..0xd707 (13-bit prefix + 3-bit args).
    if w16 &&& 0xfff8 = 0xd700 then
      let args3 : Nat := w16 &&& 0x7
      let unsigned : Bool := (args3 &&& 1) = 1
      let prefetch : Bool := (args3 &&& 2) = 2
      let quiet : Bool := (args3 &&& 4) = 4
      let (_, s16) ← s.takeBitsAsNat 16
      return (.loadIntVar unsigned prefetch quiet, 16, s16)
    -- {PLD,LD}SLICEX{Q}: 0xd718..0xd71b (14-bit prefix + 2-bit args).
    if w16 &&& 0xfffc = 0xd718 then
      let args2 : Nat := w16 &&& 0x3
      let prefetch : Bool := (args2 &&& 1) = 1
      let quiet : Bool := (args2 &&& 2) = 2
      let (_, s16) ← s.takeBitsAsNat 16
      return (.loadSliceX prefetch quiet, 16, s16)
    -- XLOAD / XLOADQ: 0xd73a/0xd73b.
    if w16 = 0xd73a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.xload false), 16, s16)
    if w16 = 0xd73b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.xload true), 16, s16)
    -- DIV/MOD family (16-bit): 12-bit prefix 0xa90 + 4-bit args.
    if w16 >>> 4 = 0xa90 then
      let args4 : Nat := w16 &&& 0xf
      let roundEnc : Nat := args4 &&& 0x3
      let dEnc : Nat := (args4 >>> 2) &&& 0x3
      if roundEnc = 3 then
        throw .invOpcode
      let roundMode : Int := Int.ofNat roundEnc - 1
      let (d, add) : (Nat × Bool) :=
        if dEnc = 0 then
          (3, true)
        else
          (dEnc, false)
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.divMod d roundMode add false, 16, s16)
    -- MUL{DIV,MOD,DIVMOD} family (16-bit): 12-bit prefix 0xa98 + 4-bit args.
    -- Matches C++ `exec_muldivmod` (arithops.cpp).
    if w16 >>> 4 = 0xa98 then
      let args4 : Nat := w16 &&& 0xf
      let roundEnc : Nat := args4 &&& 0x3
      let dEnc : Nat := (args4 >>> 2) &&& 0x3
      if roundEnc = 3 then
        throw .invOpcode
      let roundMode : Int := Int.ofNat roundEnc - 1
      let (d, add) : (Nat × Bool) :=
        if dEnc = 0 then
          (3, true)
        else
          (dEnc, false)
      if d = 0 ∨ roundMode = 2 then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.mulDivMod d roundMode add false, 16, s16)

    -- SHR/MOD pow2 family (16-bit): 0xa920..0xa92e / 0xa9a0..0xa9ae / 0xa9c0..0xa9ce.
    let roundOfs (ofs : Nat) : Int := Int.ofNat ofs - 1
    if (0xa920 ≤ w16 ∧ w16 ≤ 0xa92e) ∨ (0xa9a0 ≤ w16 ∧ w16 ≤ 0xa9ae) ∨ (0xa9c0 ≤ w16 ∧ w16 ≤ 0xa9ce) then
      let (_, s16) ← s.takeBitsAsNat 16
      if 0xa920 ≤ w16 ∧ w16 ≤ 0xa922 then
        let ofs : Nat := w16 - 0xa920
        return (.arithExt (.shrMod false true 3 (roundOfs ofs) false none), 16, s16)
      if 0xa924 ≤ w16 ∧ w16 ≤ 0xa926 then
        let ofs : Nat := w16 - 0xa924
        return (.arithExt (.shrMod false false 1 (roundOfs ofs) false none), 16, s16)
      if 0xa928 ≤ w16 ∧ w16 ≤ 0xa92a then
        let ofs : Nat := w16 - 0xa928
        return (.arithExt (.shrMod false false 2 (roundOfs ofs) false none), 16, s16)
      if 0xa92c ≤ w16 ∧ w16 ≤ 0xa92e then
        let ofs : Nat := w16 - 0xa92c
        return (.arithExt (.shrMod false false 3 (roundOfs ofs) false none), 16, s16)
      if 0xa9a0 ≤ w16 ∧ w16 ≤ 0xa9a2 then
        let ofs : Nat := w16 - 0xa9a0
        return (.arithExt (.shrMod true true 3 (roundOfs ofs) false none), 16, s16)
      if 0xa9a4 ≤ w16 ∧ w16 ≤ 0xa9a6 then
        let ofs : Nat := w16 - 0xa9a4
        return (.arithExt (.shrMod true false 1 (roundOfs ofs) false none), 16, s16)
      if 0xa9a8 ≤ w16 ∧ w16 ≤ 0xa9aa then
        let ofs : Nat := w16 - 0xa9a8
        return (.arithExt (.shrMod true false 2 (roundOfs ofs) false none), 16, s16)
      if 0xa9ac ≤ w16 ∧ w16 ≤ 0xa9ae then
        let ofs : Nat := w16 - 0xa9ac
        return (.arithExt (.shrMod true false 3 (roundOfs ofs) false none), 16, s16)
      if 0xa9c0 ≤ w16 ∧ w16 ≤ 0xa9c2 then
        let ofs : Nat := w16 - 0xa9c0
        return (.arithExt (.shlDivMod 3 (roundOfs ofs) true false none), 16, s16)
      if 0xa9c4 ≤ w16 ∧ w16 ≤ 0xa9c6 then
        let ofs : Nat := w16 - 0xa9c4
        return (.arithExt (.shlDivMod 1 (roundOfs ofs) false false none), 16, s16)
      if 0xa9c8 ≤ w16 ∧ w16 ≤ 0xa9ca then
        let ofs : Nat := w16 - 0xa9c8
        return (.arithExt (.shlDivMod 2 (roundOfs ofs) false false none), 16, s16)
      if 0xa9cc ≤ w16 ∧ w16 ≤ 0xa9ce then
        let ofs : Nat := w16 - 0xa9cc
        return (.arithExt (.shlDivMod 3 (roundOfs ofs) false false none), 16, s16)
      throw .invOpcode

    -- STREF_ALT: 0xcf10 (same semantics as STREF).
    if w16 = 0xcf10 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stref, 16, s16)

    -- STREFCONST / STREF2CONST: 0xcf20/0xcf21 (+1/+2 refs).
    if w16 = 0xcf20 then
      if !s.haveRefs 1 then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.cellExt (.stRefConst c), 16, rest)
    if w16 = 0xcf21 then
      if !s.haveRefs 2 then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      let (c1, s17) ← s16.takeRefInv
      let (c2, rest) ← s17.takeRefInv
      return (.cellExt (.stRef2Const c1 c2), 16, rest)

    -- ST{I,U}LE{4,8}: 0xcf28..0xcf2b.
    if 0xcf28 ≤ w16 ∧ w16 ≤ 0xcf2b then
      let (_, s16) ← s.takeBitsAsNat 16
      let unsigned : Bool := (w16 &&& 1) = 1
      let bytes : Nat := if (w16 &&& 2) = 2 then 8 else 4
      return (.cellExt (.stLeInt unsigned bytes), 16, s16)

    -- BTOS: 0xcf50.
    if w16 = 0xcf50 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt .btos, 16, s16)

    -- Store slice into builder (16-bit): STSLICE / STSLICER and quiet variants.
    if w16 = 0xcf12 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice false false, 16, s16)
    if w16 = 0xcf11 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef false false, 16, s16)
    if w16 = 0xcf15 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef true false, 16, s16)
    if w16 = 0xcf16 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice true false, 16, s16)
    if w16 = 0xcf1a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice false true, 16, s16)
    if w16 = 0xcf1e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSlice true true, 16, s16)
    if w16 = 0xcf13 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb false false, 16, s16)
    if w16 = 0xcf17 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb true false, 16, s16)
    if w16 = 0xcf19 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef false true, 16, s16)
    if w16 = 0xcf1d then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stbRef true true, 16, s16)
    if w16 = 0xcf1b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb false true, 16, s16)
    if w16 = 0xcf1f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stb true true, 16, s16)
    if w16 = 0xcf18 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.strefq, 16, s16)
    if w16 = 0xcf40 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stZeroes, 16, s16)
    if w16 = 0xcf41 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stOnes, 16, s16)
    if w16 = 0xcf42 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stSame, 16, s16)
    if w16 &&& 0xff00 = 0xf000 then
      let idx : Nat := w16 &&& 0xff
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callDict idx, 16, s16)
    if w16 = 0xf800 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .accept, 16, s16)
    if w16 = 0xf801 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .setGasLimit, 16, s16)
    if w16 = 0xf810 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .randu256, 16, s16)
    if w16 = 0xf811 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .rand, 16, s16)
    if w16 = 0xf807 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .gasConsumed, 16, s16)
    if w16 = 0xf80f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .commit, 16, s16)
    if w16 = 0xf823 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .now, 16, s16)
    if w16 = 0xf827 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .balance, 16, s16)
    if w16 = 0xf824 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .blockLt, 16, s16)
    if w16 = 0xf825 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .lTime, 16, s16)
    if w16 = 0xf826 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .randSeed, 16, s16)
    if w16 = 0xf828 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .myAddr, 16, s16)
    if w16 = 0xf829 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .configRoot, 16, s16)
    if w16 = 0xf82a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .myCode, 16, s16)
    if w16 = 0xf82b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .incomingValue, 16, s16)
    if w16 = 0xf82c then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .storageFees, 16, s16)
    if w16 = 0xf82d then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .prevBlocksInfoTuple, 16, s16)
    if w16 = 0xf82e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .unpackedConfigTuple, 16, s16)
    if w16 = 0xf82f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .duePayment, 16, s16)
    if w16 = 0xf830 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .configDict, 16, s16)
    if w16 = 0xf832 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.configParam false), 16, s16)
    if w16 = 0xf833 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.configParam true), 16, s16)
    if w16 = 0xf814 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.setRand false), 16, s16)
    if w16 = 0xf815 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.setRand true), 16, s16)
    if 0xf820 ≤ w16 ∧ w16 ≤ 0xf82f then
      let idx : Nat := w16 - 0xf820
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.getParam idx), 16, s16)
    if w16 = 0xf881 then
      -- GETPARAMLONG / GETPARAMLONG2: 24-bit opcode 0xf88100..0xf881ff (arg = low 8 bits).
      let (w24, s24) ← s.takeBitsAsNat 24
      let idx : Nat := w24 &&& 0xff
      if idx = 0xff then
        throw .invOpcode
      return (.tonEnvOp (.getParam idx), 24, s24)
    if w16 = 0xf835 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .globalId, 16, s16)
    if w16 = 0xf836 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getGasFee, 16, s16)
    if w16 = 0xf837 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getStorageFee, 16, s16)
    if w16 = 0xf839 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getPrecompiledGas, 16, s16)
    if w16 = 0xf838 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getForwardFee, 16, s16)
    if w16 = 0xf83a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getOriginalFwdFee, 16, s16)
    if w16 = 0xf83b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getGasFeeSimple, 16, s16)
    if w16 = 0xf83c then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getForwardFeeSimple, 16, s16)
    if w16 = 0xf840 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getGlobVar, 16, s16)
    if 0xf841 ≤ w16 ∧ w16 < 0xf860 then
      -- C++ `GETGLOB` immediate uses low 5 bits; the range 0xf841..0xf85f corresponds to 1..31.
      let idx : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.getGlob idx), 16, s16)
    if w16 = 0xf860 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .setGlobVar, 16, s16)
    if 0xf861 ≤ w16 ∧ w16 < 0xf880 then
      -- C++ `SETGLOB` immediate uses low 5 bits; the range 0xf861..0xf87f corresponds to 1..31.
      let idx : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.setGlob idx), 16, s16)
    if w16 = 0xf880 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .getExtraBalance, 16, s16)
    if 0xf890 ≤ w16 ∧ w16 < 0xf8a0 then
      let idx : Nat := w16 - 0xf890
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.inMsgParam idx), 16, s16)
    if w16 = 0xf900 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp .hashCU, 16, s16)
    if w16 = 0xf901 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp .hashSU, 16, s16)
    if w16 = 0xf902 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp .sha256U, 16, s16)
    if w16 = 0xf910 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp .chkSignU, 16, s16)
    if w16 = 0xf911 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp .chkSignS, 16, s16)
    -- Newer crypto ops (16-bit): 0xf912..0xf916 and RIST255_* (0xf920..0xf926).
    if w16 = 0xf912 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp (.ext .ecrecover), 16, s16)
    if w16 = 0xf913 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp (.ext .secp256k1XonlyPubkeyTweakAdd), 16, s16)
    if w16 = 0xf914 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp (.ext .p256ChkSignU), 16, s16)
    if w16 = 0xf915 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cryptoOp (.ext .p256ChkSignS), 16, s16)
    if w16 = 0xf916 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt .hashbu, 16, s16)
    if 0xf920 ≤ w16 ∧ w16 ≤ 0xf926 then
      let (_, s16) ← s.takeBitsAsNat 16
      match w16 with
      | 0xf920 => return (.cryptoOp (.ext .rist255FromHash), 16, s16)
      | 0xf921 => return (.cryptoOp (.ext .rist255Validate), 16, s16)
      | 0xf922 => return (.cryptoOp (.ext .rist255Add), 16, s16)
      | 0xf923 => return (.cryptoOp (.ext .rist255Sub), 16, s16)
      | 0xf924 => return (.cryptoOp (.ext .rist255Mul), 16, s16)
      | 0xf925 => return (.cryptoOp (.ext .rist255MulBase), 16, s16)
      | _ => return (.cryptoOp (.ext .rist255PushL), 16, s16)
    if w16 = 0xf940 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.cdataSize true), 16, s16)
    if w16 = 0xf941 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.cdataSize false), 16, s16)
    if w16 = 0xf942 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.sdataSize true), 16, s16)
    if w16 = 0xf943 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.sdataSize false), 16, s16)
    -- VarInt/VarUInt + standard address ops (16-bit): 0xfa01..0xfa07 / 0xfa48..0xfa55.
    if w16 = 0xfa01 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.ldVarInt true 16), 16, s16)
    if w16 = 0xfa03 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.stVarInt true 16), 16, s16)
    if w16 = 0xfa04 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.ldVarInt false 32), 16, s16)
    if w16 = 0xfa05 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.ldVarInt true 32), 16, s16)
    if w16 = 0xfa06 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.stVarInt false 32), 16, s16)
    if w16 = 0xfa07 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellExt (.stVarInt true 32), 16, s16)
    if w16 = 0xfa48 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.ldStdAddr false), 16, s16)
    if w16 = 0xfa49 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.ldStdAddr true), 16, s16)
    if w16 = 0xfa50 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.ldOptStdAddr false), 16, s16)
    if w16 = 0xfa51 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.ldOptStdAddr true), 16, s16)
    if w16 = 0xfa52 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.stStdAddr false), 16, s16)
    if w16 = 0xfa53 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.stStdAddr true), 16, s16)
    if w16 = 0xfa54 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.stOptStdAddr false), 16, s16)
    if w16 = 0xfa55 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.stOptStdAddr true), 16, s16)
    -- SETCONTARGS <copy>,<more> (16-bit): 0xec (8-bit) + args8 (copy:4, more:4 with 15 => -1).
    if w16 &&& 0xff00 = 0xec00 then
      let args8 : Nat := w16 &&& 0xff
      let copy : Nat := (args8 >>> 4) &&& 0xf
      let moreNib : Nat := args8 &&& 0xf
      let more : Int := if moreNib = 15 then -1 else Int.ofNat moreNib
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setContArgs copy more, 16, s16)
    -- RETURNARGS <count> (16-bit): 12-bit prefix 0xed0 + 4-bit count.
    if w16 &&& 0xfff0 = 0xed00 then
      let count : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.returnArgs count, 16, s16)
    if w16 = 0xed10 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.returnVarArgs, 16, s16)
    if w16 = 0xed11 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setContVarArgs, 16, s16)
    if w16 = 0xed12 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setNumVarArgs, 16, s16)
    if w16 = 0xed1e then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.bless, 16, s16)
    if w16 = 0xed1f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blessVarArgs, 16, s16)
    -- BLESSARGS <copy>,<more> (16-bit): 0xee (8-bit) + args8 (copy:4, more:4 with 15 => -1).
    if w16 &&& 0xff00 = 0xee00 then
      let args8 : Nat := w16 &&& 0xff
      let copy : Nat := (args8 >>> 4) &&& 0xf
      let moreNib : Nat := args8 &&& 0xf
      let more : Int := if moreNib = 15 then -1 else Int.ofNat moreNib
      let (_, s16) ← s.takeBitsAsNat 16
      return (.blessArgs copy more, 16, s16)
    if w16 &&& 0xfff8 = 0xed40 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.pushCtr idx, 16, s16)
    if w16 &&& 0xfff8 = 0xed50 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.popCtr idx, 16, s16)
    if w16 &&& 0xfff0 = 0xed60 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 ∨ idx ≥ 8 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setContCtr idx, 16, s16)
    if w16 &&& 0xfff8 = 0xed70 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.setRetCtr idx), 16, s16)
    if w16 &&& 0xfff8 = 0xed80 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.setAltCtr idx), 16, s16)
    if w16 &&& 0xfff8 = 0xed90 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.popSave idx), 16, s16)
    if w16 &&& 0xfff8 = 0xeda0 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.saveCtr idx, 16, s16)
    if w16 &&& 0xfff8 = 0xedb0 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.saveAltCtr idx), 16, s16)
    if w16 &&& 0xfff8 = 0xedc0 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.saveBothCtr idx), 16, s16)
    if w16 = 0xede0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .pushCtrX, 16, s16)
    if w16 = 0xede1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .popCtrX, 16, s16)
    if w16 = 0xede2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .setContCtrX, 16, s16)
    if w16 = 0xede4 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .setContCtrManyX, 16, s16)
    if w16 = 0xdb50 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .runvmx, 16, s16)
    if w16 = 0xedf0 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.boolAnd, 16, s16)
    if w16 = 0xedf1 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.boolOr, 16, s16)
    if w16 = 0xedf2 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.composBoth, 16, s16)
    if w16 = 0xedfa then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sameAlt, 16, s16)
    if w16 = 0xedfb then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sameAltSave, 16, s16)
    if w16 = 0xedf3 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .atexit, 16, s16)
    if w16 = 0xedf4 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .atexitAlt, 16, s16)
    if w16 = 0xedf5 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .setExitAlt, 16, s16)
    if w16 = 0xedf6 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .thenret, 16, s16)
    if w16 = 0xedf7 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .thenretAlt, 16, s16)
    if w16 = 0xedf8 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .invert, 16, s16)
    if w16 = 0xedf9 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .booleval, 16, s16)
    if w16 &&& 0xff00 = 0xff00 then
      let b : Nat := w16 &&& 0xff
      if b = 0xf0 then
        -- SETCPX (0xfff0): cp is taken from the stack.
        let (_, s16) ← s.takeBitsAsNat 16
        return (.setcpX, 16, s16)
      -- Match `exec_set_cp`: cp = ((b + 0x10) & 0xff) - 0x10.
      let cp : Int := Int.ofNat ((b + 0x10) &&& 0xff) - 0x10
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setcp cp, 16, s16)

    if w16 = 0xfa00 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .ldGrams, 16, s16)
    if w16 = 0xfa02 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .stGrams, 16, s16)
    if w16 = 0xfa40 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.ldMsgAddr false), 16, s16)
    if w16 = 0xfa41 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.ldMsgAddr true), 16, s16)
    if w16 = 0xfa42 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.parseMsgAddr false), 16, s16)
    if w16 = 0xfa43 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.parseMsgAddr true), 16, s16)
    if w16 = 0xfa44 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.rewriteStdAddr false), 16, s16)
    if w16 = 0xfa45 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.rewriteStdAddr true), 16, s16)
    if w16 = 0xfa46 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.rewriteVarAddr false), 16, s16)
    if w16 = 0xfa47 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp (.rewriteVarAddr true), 16, s16)
    if w16 = 0xfb00 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .sendRawMsg, 16, s16)
    if w16 = 0xfb02 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .rawReserve, 16, s16)
    if w16 = 0xfb03 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .rawReserveX, 16, s16)
    if w16 = 0xfb04 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .setCode, 16, s16)
    if w16 = 0xfb06 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .setLibCode, 16, s16)
    if w16 = 0xfb07 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .changeLib, 16, s16)
    if w16 = 0xfb08 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.tonEnvOp .sendMsg, 16, s16)

    if w16 = 0xe302 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifjmpref (Slice.ofCell c) , 16, rest)
    if w16 = 0xe303 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifnotjmpref (Slice.ofCell c), 16, rest)
    if w16 = 0xe300 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifref (Slice.ofCell c), 16, rest)
    if w16 = 0xe301 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifnotref (Slice.ofCell c), 16, rest)
    if w16 = 0xe30d then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifrefElse (Slice.ofCell c), 16, rest)
    if w16 = 0xe30e then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.ifelseRef (Slice.ofCell c), 16, rest)
    if w16 = 0xe30f then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c1, s1) ← s16.takeRefInv
      let (c2, rest) ← s1.takeRefInv
      return (.ifrefElseRef (Slice.ofCell c1) (Slice.ofCell c2), 16, rest)
    if w16 = 0xe314 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.repeat true), 16, s16)
    if w16 = 0xe315 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.repeatEnd true), 16, s16)
    if w16 = 0xe316 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.until true), 16, s16)
    if w16 = 0xe317 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.untilEnd true), 16, s16)
    if w16 = 0xe318 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.while true), 16, s16)
    if w16 = 0xe319 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.whileEnd true), 16, s16)
    if w16 = 0xe31a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.again true), 16, s16)
    if w16 = 0xe31b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.againEnd true), 16, s16)
    if w16 = 0xe304 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .condSel, 16, s16)
    if w16 = 0xe305 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .condSelChk, 16, s16)
    if w16 = 0xe308 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .ifretAlt, 16, s16)
    if w16 = 0xe309 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt .ifnotretAlt, 16, s16)
    -- IFBITJMP / IFNBITJMP: 11-bit prefix (0x71c/0x71d) + 5-bit arg, padded to 16 bits.
    if w16 &&& 0xffe0 = 0xe380 then
      let i : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.ifbitjmp i), 11 + 5, s16)
    if w16 &&& 0xffe0 = 0xe3a0 then
      let i : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.contExt (.ifnbitjmp i), 11 + 5, s16)
    -- IFBITJMPREF / IFNBITJMPREF: same bit layout plus 1 ref operand.
    if w16 &&& 0xffe0 = 0xe3c0 then
      let i : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.contExt (.ifbitjmpref i (Slice.ofCell c)), 11 + 5, rest)
    if w16 &&& 0xffe0 = 0xe3e0 then
      let i : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.contExt (.ifnbitjmpref i (Slice.ofCell c)), 11 + 5, rest)

    -- Continuation calls/jumps with arg counts (contops.cpp).
    -- CALLXARGS <params>,<retvals>: 0xda (8-bit) + args8 (params:4, retvals:4).
    if w16 &&& 0xff00 = 0xda00 then
      let args8 : Nat := w16 &&& 0xff
      let params : Nat := (args8 >>> 4) &&& 0xf
      let retVals : Int := Int.ofNat (args8 &&& 0xf)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callxArgs params retVals, 16, s16)
    -- CALLXARGS <params>,-1: 12-bit prefix 0xdb0 + 4-bit params.
    if w16 &&& 0xfff0 = 0xdb00 then
      let params : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callxArgs params (-1), 16, s16)
    -- JMPXARGS <params>: 12-bit prefix 0xdb1 + 4-bit params.
    if w16 &&& 0xfff0 = 0xdb10 then
      let params : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.jmpxArgs params, 16, s16)
    -- RETARGS <params>: 12-bit prefix 0xdb2 + 4-bit params.
    if w16 &&& 0xfff0 = 0xdb20 then
      let params : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retArgs params, 16, s16)
    if w16 = 0xdb30 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.ret, 16, s16)
    if w16 = 0xdb31 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retAlt, 16, s16)
    if w16 = 0xdb32 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retBool, 16, s16)
    if w16 = 0xdb34 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callcc, 16, s16)
    if w16 = 0xdb35 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.jmpxData, 16, s16)
    if w16 = 0xdb36 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (args8, s24) ← s16.takeBitsAsNat 8
      let params : Nat := (args8 >>> 4) &&& 0xf
      let retVals : Int := Int.ofNat ((args8 + 1) &&& 0xf) - 1
      return (.callccArgs params retVals, 24, s24)
    if w16 = 0xdb38 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callxVarArgs, 16, s16)
    if w16 = 0xdb39 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retVarArgs, 16, s16)
    if w16 = 0xdb3a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.jmpxVarArgs, 16, s16)
    if w16 = 0xdb3b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.callccVarArgs, 16, s16)
    if w16 = 0xdb3c then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.callRef (Slice.ofCell c), 16, rest)
    if w16 = 0xdb3d then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.jmpRef (Slice.ofCell c), 16, rest)
    if w16 = 0xdb3e then
      let (_, s16) ← s.takeBitsAsNat 16
      let (c, rest) ← s16.takeRefInv
      return (.jmpRefData (Slice.ofCell c), 16, rest)
    if w16 = 0xdb3f then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.retData, 16, s16)

    if w16 = 0xf400 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.stdict, 16, s16)
    if w16 = 0xf401 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.skipdict, 16, s16)
    if w16 = 0xf402 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.lddicts false), 16, s16)
    if w16 = 0xf403 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.lddicts true), 16, s16)
    -- DICT{I,U}GET{REF?}: 0xf40a..0xf40f.
    if 0xf40a ≤ w16 ∧ w16 ≤ 0xf40f then
      let byRef : Bool := (w16 &&& 1) = 1
      let intKey : Bool := (w16 &&& 4) = 4
      let unsigned : Bool := intKey && ((w16 &&& 2) = 2)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGet intKey unsigned byRef, 16, s16)

    -- DICT{I,U}{SET,REPLACE,ADD}{REF?}: 0xf412..0xf417 / 0xf422..0xf427 / 0xf432..0xf437.
    let decodeDictSet (mode : DictSetMode) : Except Excno (Instr × Nat × Slice) := do
      let byRef : Bool := (w16 &&& 1) = 1
      let intKey : Bool := (w16 &&& 4) = 4
      let unsigned : Bool := intKey && ((w16 &&& 2) = 2)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictSet intKey unsigned byRef mode, 16, s16)
    if 0xf412 ≤ w16 ∧ w16 < 0xf418 then
      return (← decodeDictSet .set)
    if 0xf422 ≤ w16 ∧ w16 < 0xf428 then
      return (← decodeDictSet .replace)
    if 0xf432 ≤ w16 ∧ w16 < 0xf438 then
      return (← decodeDictSet .add)

    -- DICT*{SET,REPLACE,ADD,DEL}GET{REF?}: 0xf41a..0xf41f / 0xf42a..0xf42f / 0xf43a..0xf43f / 0xf462..0xf467.
    let decodeDictMutGet (mode : DictMutMode) : Except Excno (Instr × Nat × Slice) := do
      let byRef : Bool := (w16 &&& 1) = 1
      let intKey : Bool := (w16 &&& 4) = 4
      let unsigned : Bool := intKey && ((w16 &&& 2) = 2)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.mutGet intKey unsigned byRef mode), 16, s16)
    if 0xf41a ≤ w16 ∧ w16 ≤ 0xf41f then
      return (← decodeDictMutGet .set)
    if 0xf42a ≤ w16 ∧ w16 ≤ 0xf42f then
      return (← decodeDictMutGet .replace)
    if 0xf43a ≤ w16 ∧ w16 ≤ 0xf43f then
      return (← decodeDictMutGet .add)
    if 0xf462 ≤ w16 ∧ w16 ≤ 0xf467 then
      return (← decodeDictMutGet .del)

    -- DICT*{SET,REPLACE,ADD}GETB (builder): 0xf445..0xf447 / 0xf44d..0xf44f / 0xf455..0xf457.
    let decodeDictMutGetB (mode : DictSetMode) : Except Excno (Instr × Nat × Slice) := do
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.mutGetB intKey unsigned mode), 16, s16)
    if 0xf445 ≤ w16 ∧ w16 ≤ 0xf447 then
      return (← decodeDictMutGetB .set)
    if 0xf44d ≤ w16 ∧ w16 ≤ 0xf44f then
      return (← decodeDictMutGetB .replace)
    if 0xf455 ≤ w16 ∧ w16 ≤ 0xf457 then
      return (← decodeDictMutGetB .add)

    -- DICT{I,U}?SETB (builder value): 0xf441..0xf443.
    if 0xf441 ≤ w16 ∧ w16 < 0xf444 then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictSetB intKey unsigned .set, 16, s16)

    -- DICT{I,U}?REPLACEB (builder value): 0xf449..0xf44b.
    if 0xf449 ≤ w16 ∧ w16 < 0xf44c then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictReplaceB intKey unsigned, 16, s16)

    -- DICT*ADDB (builder): 0xf451..0xf453.
    if 0xf451 ≤ w16 ∧ w16 < 0xf454 then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictSetB intKey unsigned .add, 16, s16)

    -- DICT{I,U}?DEL: 0xf459..0xf45b.
    if 0xf459 ≤ w16 ∧ w16 < 0xf45c then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.del intKey unsigned), 16, s16)

    -- DICT{I,U}?GETOPTREF: 0xf469..0xf46b.
    if 0xf469 ≤ w16 ∧ w16 < 0xf46c then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.getOptRef intKey unsigned), 16, s16)

    -- DICT{I,U}?SETGETOPTREF: 0xf46d..0xf46f.
    if 0xf46d ≤ w16 ∧ w16 < 0xf470 then
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.setGetOptRef intKey unsigned), 16, s16)

    -- PFXDICT{SET,REPLACE,ADD,DEL}: 0xf470..0xf473.
    if 0xf470 ≤ w16 ∧ w16 ≤ 0xf472 then
      let mode : DictSetMode :=
        if w16 = 0xf470 then .set else if w16 = 0xf471 then .replace else .add
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.pfxSet mode), 16, s16)
    if w16 = 0xf473 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt .pfxDel, 16, s16)

    -- DICTGET{NEXT,PREV}{EQ} and DICT{I,U}GET{NEXT,PREV}{EQ}: 0xf474..0xf47f.
    -- Matches C++ `exec_dict_getnear` (dictops.cpp).
    if 0xf474 ≤ w16 ∧ w16 < 0xf480 then
      let args4 : Nat := w16 &&& 0xf
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGetNear args4, 16, s16)

    -- DICT{I,U}{MIN,MAX,REMMIN,REMMAX}{REF?}: 0xf482..0xf487 / 0xf48a..0xf48f / 0xf492..0xf497 / 0xf49a..0xf49f.
    -- Matches C++ `exec_dict_getmin` (dictops.cpp).
    if (0xf482 ≤ w16 ∧ w16 < 0xf488) ∨ (0xf48a ≤ w16 ∧ w16 < 0xf490) ∨ (0xf492 ≤ w16 ∧ w16 < 0xf498) ∨
        (0xf49a ≤ w16 ∧ w16 < 0xf4a0) then
      let args5 : Nat := w16 &&& 0x1f
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGetMinMax args5, 16, s16)

    -- PFXDICTGET{Q, ,JMP,EXEC}: 0xf4a8..0xf4ab.
    if 0xf4a8 ≤ w16 ∧ w16 ≤ 0xf4ab then
      let kind : PfxDictGetKind :=
        if w16 = 0xf4a8 then .getQ
        else if w16 = 0xf4a9 then .get
        else if w16 = 0xf4aa then .getJmp
        else .getExec
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.pfxGet kind), 16, s16)

    -- SUBDICT*GET / SUBDICT*RPGET: 0xf4b1..0xf4b3 / 0xf4b5..0xf4b7.
    if (0xf4b1 ≤ w16 ∧ w16 < 0xf4b4) ∨ (0xf4b5 ≤ w16 ∧ w16 < 0xf4b8) then
      let rp : Bool := (0xf4b5 ≤ w16 ∧ w16 < 0xf4b8)
      let intKey : Bool := (w16 &&& 2) = 2
      let unsigned : Bool := intKey && ((w16 &&& 1) = 1)
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictExt (.subdictGet intKey unsigned rp), 16, s16)

    if w16 = 0xd726 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdBeginsX false, 16, s16)
    if w16 = 0xd727 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sdBeginsX true, 16, s16)

    -- DICT{I,U}GET{JMP,EXEC}{Z}: 0xf4a0..0xf4a3 (no Z) and 0xf4bc..0xf4bf (Z).
    if w16 &&& 0xfffc = 0xf4a0 ∨ w16 &&& 0xfffc = 0xf4bc then
      let unsigned : Bool := (w16 &&& 1) = 1
      let doCall : Bool := (w16 &&& 2) = 2
      let pushZ : Bool := (w16 &&& 4) = 4
      let (_, s16) ← s.takeBitsAsNat 16
      return (.dictGetExec unsigned doCall pushZ, 16, s16)

    -- {P}LDDICT{Q}: 0xf404..0xf407.
    if w16 &&& 0xfffc = 0xf404 then
      let args2 : Nat := w16 &&& 0x3
      let preload : Bool := (args2 &&& 1) = 1
      let quiet : Bool := (args2 &&& 2) = 2
      let (_, s16) ← s.takeBitsAsNat 16
      return (.lddict preload quiet, 16, s16)

    if w16 = 0xd739 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.xctos, 16, s16)
    if w16 = 0xd734 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .subslice, 16, s16)
    if w16 = 0xd736 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.split false), 16, s16)
    if w16 = 0xd737 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.split true), 16, s16)
    if w16 = 0xd741 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBits false), 16, s16)
    if w16 = 0xd742 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkRefs false), 16, s16)
    if w16 = 0xd743 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBitRefs false), 16, s16)
    if w16 = 0xd745 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBits true), 16, s16)
    if w16 = 0xd746 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkRefs true), 16, s16)
    if w16 = 0xd747 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.schkBitRefs true), 16, s16)
    if w16 = 0xd748 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .pldRefVar, 16, s16)
    if w16 &&& 0xfff0 = 0xd750 then
      let args : Nat := w16 &&& 0xf
      let unsigned : Bool := (args &&& 1) = 1
      let bytes : Nat := if (args &&& 2) = 2 then 8 else 4
      let prefetch : Bool := (args &&& 4) = 4
      let quiet : Bool := (args &&& 8) = 8
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.loadLeInt unsigned bytes prefetch quiet), 16, s16)
    if w16 = 0xd749 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sbits, 16, s16)
    if w16 = 0xd74a then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.srefs, 16, s16)
    if w16 = 0xd74b then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.sbitrefs, 16, s16)
    if w16 &&& 0xfffc = 0xd74c then
      let idx : Nat := w16 &&& 0x3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.pldRefIdx idx, 16, s16)
    if w16 = 0xd760 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .ldZeroes, 16, s16)
    if w16 = 0xd761 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .ldOnes, 16, s16)
    if w16 = 0xd762 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .ldSame, 16, s16)
    if w16 = 0xd764 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .sdepth, 16, s16)
    if w16 = 0xd765 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cdepth, 16, s16)
    if w16 = 0xd766 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .clevel, 16, s16)
    if w16 = 0xd767 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .clevelMask, 16, s16)
    if w16 &&& 0xfffc = 0xd768 then
      let i : Nat := w16 &&& 0x3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.chashI i), 16, s16)
    if w16 &&& 0xfffc = 0xd76c then
      let i : Nat := w16 &&& 0x3
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp (.cdepthI i), 16, s16)
    if w16 = 0xd770 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .chashIX, 16, s16)
    if w16 = 0xd771 then
      let (_, s16) ← s.takeBitsAsNat 16
      return (.cellOp .cdepthIX, 16, s16)

  -- 8-bit opcodes / fixed+arg opcodes
  if b8 = 0x00 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.nop, 8, s')
  if b8 = 0x84 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let exp : Nat := (args &&& 0xff) + 1
    return (.pushPow2Dec exp, 16, s16)
  if b8 = 0x85 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let exp : Nat := (args &&& 0xff) + 1
    return (.pushNegPow2 exp, 16, s16)
  if b8 = 0x01 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg0 1, 8, s')
  if 0x02 ≤ b8 ∧ b8 ≤ 0x0f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg0 idx, 8, s')
  if b8 = 0x10 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.xchg x y, 16, s16)
  if b8 = 0x11 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.xchg0 idx, 16, s16)
  if 0x12 ≤ b8 ∧ b8 ≤ 0x1f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg1 idx, 8, s')
  if b8 = 0x20 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.push 0, 8, s')
  if b8 = 0x21 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.push 1, 8, s')
  if 0x22 ≤ b8 ∧ b8 ≤ 0x2f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.push idx, 8, s')
  if b8 = 0x30 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop 0, 8, s')
  if b8 = 0x31 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop 1, 8, s')
  if 0x32 ≤ b8 ∧ b8 ≤ 0x3f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop idx, 8, s')
  if b8 = 0x50 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.xchg2 x y, 16, s16)
  if b8 = 0x51 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.xcpu x y, 16, s16)
  if b8 = 0x52 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.puxc x y, 16, s16)
  if b8 = 0x53 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := args >>> 4
    let y : Nat := args &&& 0xf
    return (.push2 x y, 16, s16)
  if b8 = 0x55 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := ((args >>> 4) &&& 0xf) + 1
    let y : Nat := (args &&& 0xf) + 1
    return (.blkSwap x y, 16, s16)
  if b8 = 0x56 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.push idx, 16, s16)
  if b8 = 0x57 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.pop idx, 16, s16)
  if b8 = 0x58 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rot, 8, s')
  if b8 = 0x59 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rotRev, 8, s')
  if b8 = 0x5a then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoSwap, 8, s')
  if b8 = 0x5b then
    let (_, s') ← s.takeBitsAsNat 8
    return (.drop2, 8, s')
  if b8 = 0x5c then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoDup, 8, s')
  if b8 = 0x5d then
    let (_, s') ← s.takeBitsAsNat 8
    return (.twoOver, 8, s')
  if b8 = 0x5e then
    let (_, s8) ← s.takeBitsAsNat 8
    let (args, s16) ← s8.takeBitsAsNat 8
    let x : Nat := ((args >>> 4) &&& 0xf) + 2
    let y : Nat := args &&& 0xf
    return (.reverse x y, 16, s16)
  if b8 = 0x60 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pick, 8, s')
  if b8 = 0x61 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.roll, 8, s')
  if b8 = 0x62 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rollRev, 8, s')
  if b8 = 0x63 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.blkSwapX, 8, s')
  if b8 = 0x64 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.reverseX, 8, s')
  if b8 = 0x65 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.dropX, 8, s')
  if b8 = 0x66 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.tuck, 8, s')
  if b8 = 0x67 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchgX, 8, s')
  if b8 = 0x68 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.depth, 8, s')
  if b8 = 0x69 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.chkDepth, 8, s')
  if b8 = 0x6a then
    let (_, s') ← s.takeBitsAsNat 8
    return (.onlyTopX, 8, s')
  if b8 = 0x6b then
    let (_, s') ← s.takeBitsAsNat 8
    return (.onlyX, 8, s')
  if b8 = 0x6d then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pushNull, 8, s')
  if b8 = 0x6e then
    let (_, s') ← s.takeBitsAsNat 8
    return (.isNull, 8, s')
  if b8 = 0xa4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.inc, 8, s')
  if b8 = 0xa5 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.dec, 8, s')
  if b8 = 0xa3 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.negate, 8, s')
  if b8 = 0xa0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.add, 8, s')
  if b8 = 0xa1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.sub, 8, s')
  if b8 = 0xa2 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.subr, 8, s')
  if b8 = 0xa6 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.addInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xa7 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.mulInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xa8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.mul, 8, s')
  if b8 = 0xaa then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.lshiftConst false (arg + 1), 16, s16)
  if b8 = 0xab then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.rshiftConst false (arg + 1), 16, s16)
  if b8 = 0xac then
    let (_, s') ← s.takeBitsAsNat 8
    return (.lshift, 8, s')
  if b8 = 0xad then
    let (_, s') ← s.takeBitsAsNat 8
    return (.rshift, 8, s')
  if b8 = 0xae then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt .pow2, 8, s')
  if b8 = 0xba then
    let (_, s') ← s.takeBitsAsNat 8
    return (.equal, 8, s')
  if b8 = 0xbd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.neq, 8, s')
  if b8 = 0xb0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.and_, 8, s')
  if b8 = 0xb1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.or, 8, s')
  if b8 = 0xb2 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xor, 8, s')
  if b8 = 0xb3 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.not_, 8, s')
  -- FITS / UFITS (16-bit): 0xb4/0xb5 + width8 (delta=1).
  if b8 = 0xb4 ∨ b8 = 0xb5 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (imm8, s16) ← s8.takeBitsAsNat 8
    let bits : Nat := imm8 + 1
    let unsigned : Bool := b8 = 0xb5
    return (.arithExt (.fitsConst unsigned false bits), 16, s16)
  if b8 = 0xb8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.sgn, 8, s')
  if b8 = 0xb9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.less, 8, s')
  if b8 = 0xbb then
    let (_, s') ← s.takeBitsAsNat 8
    return (.leq, 8, s')
  if b8 = 0xbc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.greater, 8, s')
  if b8 = 0xbe then
    let (_, s') ← s.takeBitsAsNat 8
    return (.geq, 8, s')
  if b8 = 0xbf then
    let (_, s') ← s.takeBitsAsNat 8
    return (.cmp, 8, s')
  if b8 = 0xc0 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.eqInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc1 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.lessInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc2 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.gtInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc3 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.neqInt (natToIntSignedTwos arg 8), 16, s16)
  if b8 = 0xc4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt .isnan, 8, s')
  if b8 = 0xc5 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt .chknan, 8, s')
  if b8 = 0xc8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.newc, 8, s')
  if b8 = 0xc9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.endc, 8, s')
  if b8 = 0xca then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.sti (arg + 1), 16, s16)
  if b8 = 0xcb then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.stu (arg + 1), 16, s16)
  if b8 = 0xcc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.stref, 8, s')
  -- ENDCST: 0xcd (8). Alias for STBREFR (non-quiet).
  if b8 = 0xcd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.endcst, 8, s')
  if b8 = 0xce then
    let (_, s') ← s.takeBitsAsNat 8
    return (.stSlice false false, 8, s')
  if b8 = 0xd0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ctos, 8, s')
  if b8 = 0xd1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ends, 8, s')
  if b8 = 0xd2 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.loadInt false false false (arg + 1), 16, s16)
  if b8 = 0xd3 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.ldu (arg + 1), 16, s16)
  if b8 = 0xd4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ldref, 8, s')
  if b8 = 0xd5 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ldrefRtos, 8, s')
  if b8 = 0xd8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.execute, 8, s')
  if b8 = 0xd9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.jmpx, 8, s')
  if b8 = 0xdc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifret, 8, s')
  if b8 = 0xdd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnotret, 8, s')
  if b8 = 0xde then
    let (_, s') ← s.takeBitsAsNat 8
    return (.if_, 8, s')
  if b8 = 0xdf then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnot, 8, s')
  if b8 = 0xe0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifjmp, 8, s')
  if b8 = 0xe1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnotjmp, 8, s')
  if b8 = 0xe2 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifelse, 8, s')
  if b8 = 0xe4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt (.repeat false), 8, s')
  if b8 = 0xe5 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt (.repeatEnd false), 8, s')
  if b8 = 0xe6 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.until, 8, s')
  if b8 = 0xe7 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt (.untilEnd false), 8, s')
  if b8 = 0xe8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.while_, 8, s')
  if b8 = 0xe9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt (.whileEnd false), 8, s')
  if b8 = 0xea then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt (.again false), 8, s')
  if b8 = 0xeb then
    let (_, s') ← s.takeBitsAsNat 8
    return (.contExt (.againEnd false), 8, s')

  -- Debug / FFI opcodes.
  -- EXTCALL: 0xfc00 (16) + id (32).
  if s.haveBits 48 then
    let w16 := bitsToNat (s.readBits 16)
    if w16 = 0xfc00 then
      let (_, s16) ← s.takeBitsAsNat 16
      let (id, rest) ← s16.takeBitsAsNat 32
      return (.debugOp (.extCall id), 48, rest)

  -- Debug family: 0xfe**.
  if s.haveBits 16 then
    let w16 := bitsToNat (s.readBits 16)
    -- DUMPSTK: 0xfe00.
    if w16 = 0xfe00 then
      let (_, rest) ← s.takeBitsAsNat 16
      return (.debugOp .dumpStk, 16, rest)
    -- STRDUMP: 0xfe14.
    if w16 = 0xfe14 then
      let (_, rest) ← s.takeBitsAsNat 16
      return (.debugOp .strDump, 16, rest)
    -- DUMP: 12-bit prefix 0xfe2 + 4-bit stack index.
    if w16 >>> 4 = 0xfe2 then
      let idx : Nat := w16 &&& 0xf
      let (_, rest) ← s.takeBitsAsNat 16
      return (.debugOp (.dump idx), 16, rest)
    -- DEBUGSTR: 12-bit prefix 0xfef + 4-bit length tag, then (len+1) bytes of data.
    if w16 >>> 4 = 0xfef then
      let len4 : Nat := w16 &&& 0xf
      let dataBits : Nat := (len4 + 1) * 8
      if !s.haveBits (16 + dataBits) then
        throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      let data := s16.readBits dataBits
      let rest := s16.advanceBits dataBits
      let cell : Cell := Cell.mkOrdinary data #[]
      return (.debugOp (.debugStr (Slice.ofCell cell)), 16, rest)
    -- DEBUG / DEBUG_1 / DEBUG_2: 0xfe + 8-bit immediate, with disjoint ranges.
    if w16 >>> 8 = 0xfe then
      let imm : Nat := w16 &&& 0xff
      if 0x01 ≤ imm ∧ imm ≤ 0x13 then
        let (_, rest) ← s.takeBitsAsNat 16
        return (.debugOp (.debug imm), 16, rest)
      else if 0x15 ≤ imm ∧ imm ≤ 0x1f then
        let (_, rest) ← s.takeBitsAsNat 16
        return (.debugOp (.debug1 imm), 16, rest)
      else if 0x30 ≤ imm ∧ imm ≤ 0xef then
        let (_, rest) ← s.takeBitsAsNat 16
        return (.debugOp (.debug2 imm), 16, rest)

  throw .invOpcode

def decodeCp0 (s : Slice) : Except Excno (Instr × Slice) := do
  let (i, _, rest) ← decodeCp0WithBits s
  return (i, rest)

end TvmLean
