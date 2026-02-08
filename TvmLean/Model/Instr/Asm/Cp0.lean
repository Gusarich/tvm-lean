import TvmLean.Model.Cell.Primitives

namespace TvmLean

def bitsOr (a b : BitString) : BitString :=
  if a.size != b.size then
    #[]
  else
    Array.ofFn (n := a.size) fun i =>
      a[i.1]! || b[i.1]!

def bitsAnd (a b : BitString) : BitString :=
  if a.size != b.size then
    #[]
  else
    Array.ofFn (n := a.size) fun i =>
      a[i.1]! && b[i.1]!

def bitsXor (a b : BitString) : BitString :=
  if a.size != b.size then
    #[]
  else
    Array.ofFn (n := a.size) fun i =>
      a[i.1]! != b[i.1]!

def encodeTupleInstr (op : TupleInstr) : Except Excno BitString := do
  match op with
  | .mktuple n =>
      if n ≤ 15 then
        return natToBits (0x6f00 + n) 16
      else
        throw .rangeChk
  | .index idx =>
      if idx ≤ 15 then
        return natToBits (0x6f10 + idx) 16
      else
        throw .rangeChk
  | .untuple n =>
      if n ≤ 15 then
        return natToBits (0x6f20 + n) 16
      else
        throw .rangeChk
  | .unpackFirst n =>
      if n ≤ 15 then
        return natToBits (0x6f30 + n) 16
      else
        throw .rangeChk
  | .explode maxLen =>
      if maxLen ≤ 15 then
        return natToBits (0x6f40 + maxLen) 16
      else
        throw .rangeChk
  | .setIndex idx =>
      if idx ≤ 15 then
        return natToBits (0x6f50 + idx) 16
      else
        throw .rangeChk
  | .indexQ idx =>
      if idx ≤ 15 then
        return natToBits (0x6f60 + idx) 16
      else
        throw .rangeChk
  | .setIndexQ idx =>
      if idx ≤ 15 then
        return natToBits (0x6f70 + idx) 16
      else
        throw .rangeChk
  | .mktupleVar =>
      return natToBits 0x6f80 16
  | .indexVar =>
      return natToBits 0x6f81 16
  | .untupleVar =>
      return natToBits 0x6f82 16
  | .unpackFirstVar =>
      return natToBits 0x6f83 16
  | .explodeVar =>
      return natToBits 0x6f84 16
  | .setIndexVar =>
      return natToBits 0x6f85 16
  | .indexVarQ =>
      return natToBits 0x6f86 16
  | .setIndexVarQ =>
      return natToBits 0x6f87 16
  | .tlen =>
      return natToBits 0x6f88 16
  | .qtlen =>
      return natToBits 0x6f89 16
  | .isTuple =>
      return natToBits 0x6f8a 16
  | .last =>
      return natToBits 0x6f8b 16
  | .tpush =>
      return natToBits 0x6f8c 16
  | .tpop =>
      return natToBits 0x6f8d 16
  | .index2 i j =>
      if i < 4 ∧ j < 4 then
        return natToBits (0x6fb0 + ((i &&& 3) <<< 2) + (j &&& 3)) 16
      else
        throw .rangeChk
  | .index3 i j k =>
      if i < 4 ∧ j < 4 ∧ k < 4 then
        return natToBits (0x6fc0 + ((i &&& 3) <<< 4) + ((j &&& 3) <<< 2) + (k &&& 3)) 16
      else
        throw .rangeChk

def encodeCellInstr (op : CellInstr) : Except Excno BitString := do
  match op with
  | .sdFirst =>
      return natToBits 0xc703 16
  | .sdSfx =>
      return natToBits 0xc70c 16
  | .sdSfxRev =>
      return natToBits 0xc70d 16
  | .sdPsfx =>
      return natToBits 0xc70e 16
  | .sdPsfxRev =>
      return natToBits 0xc70f 16
  | .sdCntLead1 =>
      return natToBits 0xc711 16
  | .sdCntTrail1 =>
      return natToBits 0xc713 16
  | .strefR quiet =>
      return natToBits (if quiet then 0xcf1c else 0xcf14) 16
  | .endxc =>
      return natToBits 0xcf23 16
  | .sdSubstr =>
      return natToBits 0xd724 16
  | .scutfirst =>
      return natToBits 0xd730 16
  | .sskipfirst =>
      return natToBits 0xd731 16
  | .scutlast =>
      return natToBits 0xd732 16
  | .sskiplast =>
      return natToBits 0xd733 16
  | .subslice =>
      return natToBits 0xd734 16
  | .split quiet =>
      return natToBits (if quiet then 0xd737 else 0xd736) 16
  | .pldRefVar =>
      return natToBits 0xd748 16
  | .loadLeInt unsigned bytes prefetch quiet =>
      let lenBit : Nat ←
        if bytes = 4 then
          pure 0
        else if bytes = 8 then
          pure 2
        else
          throw .rangeChk
      let args4 : Nat :=
        (if unsigned then 1 else 0) +
          lenBit +
            (if prefetch then 4 else 0) +
              (if quiet then 8 else 0)
      return natToBits (0xd750 + args4) 16
  | .ldZeroes =>
      return natToBits 0xd760 16
  | .ldOnes =>
      return natToBits 0xd761 16
  | .ldSame =>
      return natToBits 0xd762 16
  | .sdepth =>
      return natToBits 0xd764 16
  | .clevel =>
      return natToBits 0xd766 16
  | .clevelMask =>
      return natToBits 0xd767 16
  | .chashI i =>
      if i ≤ 3 then
        return natToBits (0xd768 + i) 16
      else
        throw .rangeChk
  | .cdepthI i =>
      if i ≤ 3 then
        return natToBits (0xd76c + i) 16
      else
        throw .rangeChk
  | .chashIX =>
      return natToBits 0xd770 16
  | .cdepthIX =>
      return natToBits 0xd771 16
  | .schkBits quiet =>
      return natToBits (if quiet then 0xd745 else 0xd741) 16
  | .schkRefs quiet =>
      return natToBits (if quiet then 0xd746 else 0xd742) 16
  | .schkBitRefs quiet =>
      return natToBits (if quiet then 0xd747 else 0xd743) 16
  | .bdepth =>
      return natToBits 0xcf30 16
  | .brefs =>
      return natToBits 0xcf32 16
  | .bbitrefs =>
      return natToBits 0xcf33 16
  | .brembits =>
      return natToBits 0xcf35 16
  | .bremrefs =>
      return natToBits 0xcf36 16
  | .brembitrefs =>
      return natToBits 0xcf37 16
  | .bchkBitsImm bits quiet =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      return natToBits (if quiet then 0xcf3c else 0xcf38) 16 ++ natToBits (bits - 1) 8
  | .bchk needBits needRefs quiet =>
      let base : Nat :=
        if needBits && needRefs then
          if quiet then 0xcf3f else 0xcf3b
        else if needBits then
          if quiet then 0xcf3d else 0xcf39
        else if needRefs then
          if quiet then 0xcf3e else 0xcf3a
        else
          0
      if base = 0 then
        throw .invOpcode
      return natToBits base 16

def encodeCellExtInstr (op : CellExtInstr) : Except Excno BitString := do
  match op with
  | .btos =>
      return natToBits 0xcf50 16
  | .stLeInt unsigned bytes =>
      let lenBit : Nat ←
        if bytes = 4 then
          pure 0
        else if bytes = 8 then
          pure 2
        else
          throw .rangeChk
      let w16 : Nat := 0xcf28 + (if unsigned then 1 else 0) + lenBit
      return natToBits w16 16
  | .hashbu =>
      return natToBits 0xf916 16
  | .cdataSize quiet =>
      return natToBits (if quiet then 0xf940 else 0xf941) 16
  | .sdataSize quiet =>
      return natToBits (if quiet then 0xf942 else 0xf943) 16
  | _ =>
      -- Some CellExt opcodes embed refs/consts in the code cell (not supported by `encodeCp0`).
      throw .invOpcode

def encodeArithExtInstr (op : ArithExtInstr) : Except Excno BitString := do
  match op with
  | .qaddInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xb7a6 16 ++ natToBits imm 8
      else
        throw .rangeChk
  | .qmulInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xb7a7 16 ++ natToBits imm 8
      else
        throw .rangeChk
  | .qeqInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xb7c0 16 ++ natToBits imm 8
      else
        throw .rangeChk
  | .qgtInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xb7c2 16 ++ natToBits imm 8
      else
        throw .rangeChk
  | .fitsConst unsigned quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let imm : Nat := bits - 1
      if quiet then
        let p16 : Nat := if unsigned then 0xb7b5 else 0xb7b4
        return natToBits p16 16 ++ natToBits imm 8
      else
        let p8 : Nat := if unsigned then 0xb5 else 0xb4
        return natToBits p8 8 ++ natToBits imm 8
  | .lshiftVar quiet =>
      if quiet then
        return natToBits 0xb7ac 16
      else
        throw .invOpcode
  | .rshiftVar quiet =>
      if quiet then
        return natToBits 0xb7ad 16
      else
        throw .invOpcode
  | .shrMod mul add d roundMode quiet zOpt =>
      let roundOfs : Nat ←
        if roundMode = -1 then
          pure 0
        else if roundMode = 0 then
          pure 1
        else if roundMode = 1 then
          pure 2
        else
          throw .invOpcode
      let baseNoHash? : Option Nat :=
        match mul, add, d with
        | false, true, 3 => some 0xa920
        | false, false, 1 => some 0xa924
        | false, false, 2 => some 0xa928
        | false, false, 3 => some 0xa92c
        | true, true, 3 => some 0xa9a0
        | true, false, 1 => some 0xa9a4
        | true, false, 2 => some 0xa9a8
        | true, false, 3 => some 0xa9ac
        | _, _, _ => none
      let p16NoHash ←
        match baseNoHash? with
        | some p16 => pure (p16 + roundOfs)
        | none => throw .invOpcode
      match zOpt with
      | none =>
          if quiet then
            return natToBits 0xb7 8 ++ natToBits p16NoHash 16
          else
            return natToBits p16NoHash 16
      | some z =>
          if quiet then
            throw .invOpcode
          if z = 0 ∨ z > 256 then
            throw .rangeChk
          let baseHash? : Option Nat :=
            match mul, add, d with
            | false, true, 3 => some 0xa930
            | false, false, 1 => some 0xa934
            | false, false, 2 => some 0xa938
            | false, false, 3 => some 0xa93c
            | true, true, 3 => some 0xa9b0
            | _, _, _ => none
          let p16Hash ←
            match baseHash? with
            | some p16 => pure (p16 + roundOfs)
            | none => throw .invOpcode
          return natToBits p16Hash 16 ++ natToBits (z - 1) 8
  | .shlDivMod d roundMode addMode quiet zOpt =>
      let roundOfs : Nat ←
        if roundMode = -1 then
          pure 0
        else if roundMode = 0 then
          pure 1
        else if roundMode = 1 then
          pure 2
        else
          throw .invOpcode
      let baseNoHash? : Option Nat :=
        match addMode, d with
        | true, 3 => some 0xa9c0
        | false, 1 => some 0xa9c4
        | false, 2 => some 0xa9c8
        | false, 3 => some 0xa9cc
        | _, _ => none
      let p16NoHash ←
        match baseNoHash? with
        | some p16 => pure (p16 + roundOfs)
        | none => throw .invOpcode
      match zOpt with
      | none =>
          if quiet then
            return natToBits 0xb7 8 ++ natToBits p16NoHash 16
          else
            return natToBits p16NoHash 16
      | some z =>
          if quiet then
            throw .invOpcode
          if z = 0 ∨ z > 256 then
            throw .rangeChk
          let baseHash? : Option Nat :=
            match addMode, d with
            | true, 3 => some 0xa9d0
            | false, 1 => some 0xa9d4
            | false, 2 => some 0xa9d8
            | false, 3 => some 0xa9dc
            | _, _ => none
          let p16Hash ←
            match baseHash? with
            | some p16 => pure (p16 + roundOfs)
            | none => throw .invOpcode
          return natToBits p16Hash 16 ++ natToBits (z - 1) 8
def encodeCryptoInstr (op : CryptoInstr) : Except Excno BitString := do
  match op with
  | .hashExt hashId append rev =>
      if hashId > 255 then
        throw .rangeChk
      let args10 : Nat :=
        (hashId &&& 0xff) +
          (if rev then (1 <<< 8) else 0) +
            (if append then (1 <<< 9) else 0)
      let word24 : Nat := ((0xf904 >>> 2) <<< 10) + (args10 &&& 0x3ff)
      return natToBits word24 24
  | .hashCU =>
      return natToBits 0xf900 16
  | .hashSU =>
      return natToBits 0xf901 16
  | .sha256U =>
      return natToBits 0xf902 16
  | .chkSignU =>
      return natToBits 0xf910 16
  | .chkSignS =>
      return natToBits 0xf911 16
  | .ext _ =>
      throw .invOpcode

def encodeTonEnvInstr (op : TonEnvInstr) : Except Excno BitString := do
  match op with
  | .balance =>
      return natToBits 0xf827 16
  | .now =>
      return natToBits 0xf823 16
  | .blockLt =>
      return natToBits 0xf824 16
  | .lTime =>
      return natToBits 0xf825 16
  | .randSeed =>
      return natToBits 0xf826 16
  | .myAddr =>
      return natToBits 0xf828 16
  | .configRoot =>
      return natToBits 0xf829 16
  | .configDict =>
      return natToBits 0xf830 16
  | .configParam opt =>
      return natToBits (if opt then 0xf833 else 0xf832) 16
  | .myCode =>
      return natToBits 0xf82a 16
  | .incomingValue =>
      return natToBits 0xf82b 16
  | .storageFees =>
      return natToBits 0xf82c 16
  | .prevBlocksInfoTuple =>
      return natToBits 0xf82d 16
  | .prevMcBlocks =>
      return natToBits 0xf83400 24
  | .prevKeyBlock =>
      return natToBits 0xf83401 24
  | .prevMcBlocks100 =>
      return natToBits 0xf83402 24
  | .unpackedConfigTuple =>
      return natToBits 0xf82e 16
  | .duePayment =>
      return natToBits 0xf82f 16
  | .getParam idx =>
      -- The short 16-bit opcodes 0xf823..0xf82f are used by dedicated aliases (NOW/BALANCE/.../DUEPAYMENT).
      -- To keep decode∘encode a roundtrip on the `getParam` AST node, only use the short form for 0..2.
      if idx ≤ 2 then
        return natToBits (0xf820 + idx) 16
      else if idx ≤ 254 then
        return natToBits (0xf88100 + idx) 24
      else
        throw .rangeChk
  | .randu256 =>
      return natToBits 0xf810 16
  | .rand =>
      return natToBits 0xf811 16
  | .setRand mix =>
      return natToBits (if mix then 0xf815 else 0xf814) 16
  | .getGlobVar =>
      return natToBits 0xf840 16
  | .getGlob idx =>
      if idx = 0 ∨ idx > 31 then
        throw .rangeChk
      else
        return natToBits (0xf840 + idx) 16
  | .setGlobVar =>
      return natToBits 0xf860 16
  | .setGlob idx =>
      if idx = 0 ∨ idx > 31 then
        throw .rangeChk
      else
        return natToBits (0xf860 + idx) 16
  | .accept =>
      return natToBits 0xf800 16
  | .setGasLimit =>
      return natToBits 0xf801 16
  | .gasConsumed =>
      return natToBits 0xf807 16
  | .commit =>
      return natToBits 0xf80f 16
  | .ldGrams =>
      return natToBits 0xfa00 16
  | .stGrams =>
      return natToBits 0xfa02 16
  | .ldMsgAddr quiet =>
      return natToBits (if quiet then 0xfa41 else 0xfa40) 16
  | .parseMsgAddr quiet =>
      return natToBits (if quiet then 0xfa43 else 0xfa42) 16
  | .rewriteStdAddr quiet =>
      return natToBits (if quiet then 0xfa45 else 0xfa44) 16
  | .rewriteVarAddr quiet =>
      return natToBits (if quiet then 0xfa47 else 0xfa46) 16
  | .ldStdAddr quiet =>
      return natToBits (if quiet then 0xfa49 else 0xfa48) 16
  | .ldOptStdAddr quiet =>
      return natToBits (if quiet then 0xfa51 else 0xfa50) 16
  | .stStdAddr quiet =>
      return natToBits (if quiet then 0xfa53 else 0xfa52) 16
  | .stOptStdAddr quiet =>
      return natToBits (if quiet then 0xfa55 else 0xfa54) 16
  | .globalId =>
      return natToBits 0xf835 16
  | .getGasFee =>
      return natToBits 0xf836 16
  | .getStorageFee =>
      return natToBits 0xf837 16
  | .getForwardFee =>
      return natToBits 0xf838 16
  | .getPrecompiledGas =>
      return natToBits 0xf839 16
  | .getOriginalFwdFee =>
      return natToBits 0xf83a 16
  | .getGasFeeSimple =>
      return natToBits 0xf83b 16
  | .getForwardFeeSimple =>
      return natToBits 0xf83c 16
  | .getExtraBalance =>
      return natToBits 0xf880 16
  | .inMsgParam idx =>
      if idx ≤ 15 then
        return natToBits (0xf890 + idx) 16
      else
        throw .rangeChk
  | .sendMsg =>
      return natToBits 0xfb08 16
  | .sendRawMsg =>
      return natToBits 0xfb00 16
  | .rawReserve =>
      return natToBits 0xfb02 16
  | .rawReserveX =>
      return natToBits 0xfb03 16
  | .setCode =>
      return natToBits 0xfb04 16
  | .setLibCode =>
      return natToBits 0xfb06 16
  | .changeLib =>
      return natToBits 0xfb07 16

def encodeDebugInstr (op : DebugInstr) : Except Excno BitString := do
  match op with
  | .dumpStk =>
      return natToBits 0xfe00 16
  | .strDump =>
      return natToBits 0xfe14 16
  | .dump idx =>
      if idx ≤ 15 then
        return natToBits (0xfe20 + idx) 16
      else
        throw .rangeChk
  | .debug i =>
      if 0x01 ≤ i ∧ i ≤ 0x13 then
        return natToBits 0xfe 8 ++ natToBits i 8
      else
        throw .rangeChk
  | .debug1 t =>
      if 0x15 ≤ t ∧ t ≤ 0x1f then
        return natToBits 0xfe 8 ++ natToBits t 8
      else
        throw .rangeChk
  | .debug2 t =>
      if 0x30 ≤ t ∧ t ≤ 0xef then
        return natToBits 0xfe 8 ++ natToBits t 8
      else
        throw .rangeChk
  | .debugStr s =>
      if s.refsRemaining ≠ 0 then
        throw .rangeChk
      let dataBits : Nat := s.bitsRemaining
      if dataBits = 0 ∨ dataBits % 8 ≠ 0 then
        throw .rangeChk
      let lenBytes : Nat := dataBits / 8
      if lenBytes > 16 then
        throw .rangeChk
      let bits4 : Nat := lenBytes - 1
      let header : Nat := 0xfef0 + bits4
      return natToBits header 16 ++ s.readBits dataBits
  | .extCall id =>
      if id ≤ 1_000_000 ∧ id < (1 <<< 32) then
        return natToBits 0xfc00 16 ++ natToBits id 32
      else
        throw .rangeChk

def encodeCp0 (i : Instr) : Except Excno BitString := do
  match i with
  | .nop =>
      return natToBits 0x00 8
  | .pushInt .nan =>
      return natToBits 0x83ff 16
  | .pushInt (.num n) =>
      if (-5 ≤ n ∧ n ≤ 10) then
        let imm : Nat :=
          if n ≥ 0 then
            n.toNat
          else
            (16 + n).toNat
        return natToBits (0x70 + imm) 8
      else if (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0x80 8 ++ natToBits imm 8
      else if (-32768 ≤ n ∧ n ≤ 32767) then
        let imm : Nat := if n ≥ 0 then n.toNat else (65536 - (-n).toNat)
        return natToBits 0x81 8 ++ natToBits imm 16
      else
        -- PUSHINT_LONG encoding (0x82 + len5 + value bits).
        -- C++ reserves len5=31; use the smallest valid len5 in [0,30].
        let len5 : Nat := Id.run do
          let mut out : Nat := 30
          let mut found : Bool := false
          for k in [0:31] do
            if !found then
              let widthK : Nat := 3 + (k + 2) * 8
              if intSignedFitsBits n widthK then
                out := k
                found := true
          return out
        let l := len5 + 2
        let width := 3 + l * 8
        let prefix13 : Nat := (0x82 <<< 5) + len5
        let valBits ← intToBitsTwos n width
        return natToBits prefix13 13 ++ valBits
  | .pushPow2 exp =>
      if 0 < exp ∧ exp ≤ 255 then
        return natToBits (0x8300 + (exp - 1)) 16
      else
        throw .rangeChk
  | .pushPow2Dec exp =>
      if 0 < exp ∧ exp ≤ 256 then
        return natToBits 0x84 8 ++ natToBits (exp - 1) 8
      else
        throw .rangeChk
  | .pushNegPow2 exp =>
      if 0 < exp ∧ exp ≤ 256 then
        return natToBits 0x85 8 ++ natToBits (exp - 1) 8
      else
        throw .rangeChk
  | .push idx =>
      if idx = 0 then
        return natToBits 0x20 8
      else if idx = 1 then
        return natToBits 0x21 8
      else if idx ≤ 15 then
        return natToBits (0x20 + idx) 8
      else if idx ≤ 255 then
        return natToBits 0x56 8 ++ natToBits idx 8
      else
        throw .rangeChk
  | .pop idx =>
      if idx = 0 then
        return natToBits 0x30 8
      else if idx = 1 then
        return natToBits 0x31 8
      else if idx ≤ 15 then
        return natToBits (0x30 + idx) 8
      else if idx ≤ 255 then
        return natToBits 0x57 8 ++ natToBits idx 8
      else
        throw .rangeChk
  | .xchg0 idx =>
      if idx = 0 then
        return natToBits 0x00 8
      else if idx = 1 then
        return natToBits 0x01 8
      else if idx ≤ 15 then
        return natToBits idx 8
      else if idx ≤ 255 then
        return natToBits 0x11 8 ++ natToBits idx 8
      else
        throw .rangeChk
  | .xchg1 idx =>
      if 2 ≤ idx ∧ idx ≤ 15 then
        return natToBits (0x10 + idx) 8
      else
        throw .rangeChk
  | .xchg x y =>
      if x ≤ 15 ∧ y ≤ 15 ∧ 0 < x ∧ x < y then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x10 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .xchg2 x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x50 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .xchg3 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        return natToBits (0x4000 + args) 16
      else
        throw .rangeChk
  | .xcpu x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x51 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .xc2pu x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x541 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .xcpuxc x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x542 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .xcpu2 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x543 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .puxc2 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x544 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .puxc x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x52 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .puxcpu x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x545 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .pu2xc x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x546 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .push2 x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        return natToBits 0x53 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .push3 x y z =>
      if x ≤ 15 ∧ y ≤ 15 ∧ z ≤ 15 then
        let args : Nat := (x <<< 8) + (y <<< 4) + z
        let word24 : Nat := (0x547 <<< 12) + args
        return natToBits word24 24
      else
        throw .rangeChk
  | .blkSwap x y =>
      if 1 ≤ x ∧ x ≤ 16 ∧ 1 ≤ y ∧ y ≤ 16 then
        let args : Nat := ((x - 1) <<< 4) + (y - 1)
        return natToBits 0x55 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .blkPush x y =>
      if 1 ≤ x ∧ x ≤ 15 ∧ y ≤ 15 then
        let args8 : Nat := (x <<< 4) + y
        return natToBits (0x5f00 + args8) 16
      else
        throw .rangeChk
  | .rot =>
      return natToBits 0x58 8
  | .rotRev =>
      return natToBits 0x59 8
  | .twoSwap =>
      return natToBits 0x5a 8
  | .twoDup =>
      return natToBits 0x5c 8
  | .twoOver =>
      return natToBits 0x5d 8
  | .reverse x y =>
      if 2 ≤ x ∧ x ≤ 17 ∧ y ≤ 15 then
        let args : Nat := ((x - 2) <<< 4) + y
        return natToBits 0x5e 8 ++ natToBits args 8
      else
        throw .rangeChk
  | .pick =>
      return natToBits 0x60 8
  | .roll =>
      return natToBits 0x61 8
  | .rollRev =>
      return natToBits 0x62 8
  | .blkSwapX =>
      return natToBits 0x63 8
  | .reverseX =>
      return natToBits 0x64 8
  | .dropX =>
      return natToBits 0x65 8
  | .tuck =>
      return natToBits 0x66 8
  | .xchgX =>
      return natToBits 0x67 8
  | .depth =>
      return natToBits 0x68 8
  | .chkDepth =>
      return natToBits 0x69 8
  | .onlyTopX =>
      return natToBits 0x6a 8
  | .onlyX =>
      return natToBits 0x6b 8
  | .pushCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed40 + idx) 16
  | .popCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed50 + idx) 16
  | .setContCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed60 + idx) 16
  | .saveCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xeda0 + idx) 16
  | .sameAlt =>
      return natToBits 0xedfa 16
  | .sameAltSave =>
      return natToBits 0xedfb 16
  | .boolAnd =>
      return natToBits 0xedf0 16
  | .boolOr =>
      return natToBits 0xedf1 16
  | .composBoth =>
      return natToBits 0xedf2 16
  | .contExt op =>
      match op with
      | .atexit => return natToBits 0xedf3 16
      | .atexitAlt => return natToBits 0xedf4 16
      | .setExitAlt => return natToBits 0xedf5 16
      | .thenret => return natToBits 0xedf6 16
      | .thenretAlt => return natToBits 0xedf7 16
      | .invert => return natToBits 0xedf8 16
      | .booleval => return natToBits 0xedf9 16
      | .condSel => return natToBits 0xe304 16
      | .condSelChk => return natToBits 0xe305 16
      | .ifretAlt => return natToBits 0xe308 16
      | .ifnotretAlt => return natToBits 0xe309 16
      | .pow2 => return natToBits 0xae 8
      | .fitsx => return natToBits 0xb600 16
      | .ufitsx => return natToBits 0xb601 16
      | .qand => return natToBits 0xb7b0 16
      | .qor => return natToBits 0xb7b1 16
      | .qxor => return natToBits 0xb7b2 16
      | .qnot => return natToBits 0xb7b3 16
      | .qfitsx => return natToBits 0xb7b600 24
      | .qufitsx => return natToBits 0xb7b601 24
      | .qbitsize => return natToBits 0xb7b602 24
      | .qmin => return natToBits 0xb7b608 24
      | .isnan => return natToBits 0xc4 8
      | .chknan => return natToBits 0xc5 8
      | .qsgn => return natToBits 0xb7b8 16
      | .qless => return natToBits 0xb7b9 16
      | .qequal => return natToBits 0xb7ba 16
      | .qleq => return natToBits 0xb7bb 16
      | .qgreater => return natToBits 0xb7bc 16
      | .qneq => return natToBits 0xb7bd 16
      | .qgeq => return natToBits 0xb7be 16
      | .repeat false => return natToBits 0xe4 8
      | .repeat true => return natToBits 0xe314 16
      | .repeatEnd false => return natToBits 0xe5 8
      | .repeatEnd true => return natToBits 0xe315 16
      | .until false => return natToBits 0xe6 8
      | .until true => return natToBits 0xe316 16
      | .untilEnd false => return natToBits 0xe7 8
      | .untilEnd true => return natToBits 0xe317 16
      | .while false => return natToBits 0xe8 8
      | .while true => return natToBits 0xe318 16
      | .whileEnd false => return natToBits 0xe9 8
      | .whileEnd true => return natToBits 0xe319 16
      | .again false => return natToBits 0xea 8
      | .again true => return natToBits 0xe31a 16
      | .againEnd false => return natToBits 0xeb 8
      | .againEnd true => return natToBits 0xe31b 16
      | .ifbitjmp i =>
          if i > 31 then throw .rangeChk
          return natToBits ((0x71c <<< 5) + i) 16
      | .ifnbitjmp i =>
          if i > 31 then throw .rangeChk
          return natToBits ((0x71d <<< 5) + i) 16
      | .ifbitjmpref _ _ => throw .invOpcode
      | .ifnbitjmpref _ _ => throw .invOpcode
      | .jmpDict idx =>
          if idx > 0x3fff then throw .rangeChk
          let prefix10 : Nat := 0x3c5
          let word24 : Nat := (prefix10 <<< 14) + (idx &&& 0x3fff)
          return natToBits word24 24
      | .pushCtrX => return natToBits 0xede0 16
      | .popCtrX => return natToBits 0xede1 16
      | .setContCtrX => return natToBits 0xede2 16
      | .setContCtrMany mask =>
          if mask ≥ 256 then throw .rangeChk
          return natToBits 0xede3 16 ++ natToBits (mask &&& 0xff) 8
      | .setContCtrManyX => return natToBits 0xede4 16
      | .setRetCtr idx =>
          if idx = 6 ∨ idx > 7 then throw .rangeChk
          return natToBits (0xed70 + idx) 16
      | .setAltCtr idx =>
          if idx = 6 ∨ idx > 7 then throw .rangeChk
          return natToBits (0xed80 + idx) 16
      | .popSave idx =>
          if idx = 6 ∨ idx > 7 then throw .rangeChk
          return natToBits (0xed90 + idx) 16
      | .saveAltCtr idx =>
          if idx = 6 ∨ idx > 7 then throw .rangeChk
          return natToBits (0xedb0 + idx) 16
      | .saveBothCtr idx =>
          if idx = 6 ∨ idx > 7 then throw .rangeChk
          return natToBits (0xedc0 + idx) 16
      | .runvm mode =>
          if mode ≥ 512 then throw .rangeChk
          let word24 : Nat := (0xdb4 <<< 12) + (mode &&& 0xfff)
          return natToBits word24 24
      | .runvmx =>
          return natToBits 0xdb50 16
  | .setContArgs copy more =>
      if copy > 15 then
        throw .rangeChk
      if more < -1 ∨ more > 14 then
        throw .rangeChk
      let moreNib : Nat := if more = -1 then 15 else more.toNat
      let args8 : Nat := (copy <<< 4) + moreNib
      return natToBits 0xec 8 ++ natToBits args8 8
  | .setContVarArgs =>
      return natToBits 0xed11 16
  | .returnArgs count =>
      if count > 15 then
        throw .rangeChk
      return natToBits (0xed00 + count) 16
  | .returnVarArgs =>
      return natToBits 0xed10 16
  | .setNumVarArgs =>
      return natToBits 0xed12 16
  | .bless =>
      return natToBits 0xed1e 16
  | .blessVarArgs =>
      return natToBits 0xed1f 16
  | .blessArgs copy more =>
      if copy > 15 then
        throw .rangeChk
      if more < -1 ∨ more > 14 then
        throw .rangeChk
      let moreNib : Nat := if more = -1 then 15 else more.toNat
      let args8 : Nat := (copy <<< 4) + moreNib
      return natToBits 0xee 8 ++ natToBits args8 8
  | .ctos =>
      return natToBits 0xd0 8
  | .xctos =>
      return natToBits 0xd739 16
  | .newc =>
      return natToBits 0xc8 8
  | .endc =>
      return natToBits 0xc9 8
  | .endcst =>
      return natToBits 0xcd 8
  | .ends =>
      return natToBits 0xd1 8
  | .ldu bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xd3 8 ++ natToBits (bits - 1) 8
  | .loadInt _ _ _ _ =>
      throw .invOpcode
  | .loadIntVar unsigned prefetch quiet =>
      let args3 : Nat := (if unsigned then 1 else 0) + (if prefetch then 2 else 0) + (if quiet then 4 else 0)
      return natToBits (0xd700 + args3) 16
  | .ldref =>
      return natToBits 0xd4 8
  | .ldrefRtos =>
      return natToBits 0xd5 8
  | .pldRefIdx idx =>
      if idx < 4 then
        return natToBits (0xd74c + idx) 16
      else
        throw .rangeChk
  | .loadSliceX prefetch quiet =>
      let args : Nat := (if prefetch then 1 else 0) + (if quiet then 2 else 0)
      return natToBits (0xd718 + args) 16
  | .loadSliceFixed prefetch quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let bits8 : Nat := bits - 1
      let flags2 : Nat := (if prefetch then 1 else 0) + (if quiet then 2 else 0)
      let args10 : Nat := (flags2 <<< 8) + bits8
      let prefix14 : Nat := (0xd71c >>> 2)
      let word24 : Nat := (prefix14 <<< 10) + args10
      return natToBits word24 24
  | .sti bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xca 8 ++ natToBits (bits - 1) 8
  | .stu bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xcb 8 ++ natToBits (bits - 1) 8
  | .stIntVar unsigned rev quiet =>
      let args3 : Nat := (if unsigned then 1 else 0) + (if rev then 2 else 0) + (if quiet then 4 else 0)
      return natToBits (0xcf00 + args3) 16
  | .stIntFixed unsigned rev quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let bits8 : Nat := bits - 1
      let flags3 : Nat := (if unsigned then 1 else 0) + (if rev then 2 else 0) + (if quiet then 4 else 0)
      let args11 : Nat := (flags3 <<< 8) + bits8
      let prefix13 : Nat := (0xcf08 >>> 3)
      let word24 : Nat := (prefix13 <<< 11) + args11
      return natToBits word24 24
  | .stSlice rev quiet =>
      if !rev && !quiet then
        return natToBits 0xce 8
      else if rev && !quiet then
        return natToBits 0xcf16 16
      else if !rev && quiet then
        return natToBits 0xcf1a 16
      else
        return natToBits 0xcf1e 16
  | .stb rev quiet =>
      if !rev && !quiet then
        return natToBits 0xcf13 16
      else if rev && !quiet then
        return natToBits 0xcf17 16
      else if !rev && quiet then
        return natToBits 0xcf1b 16
      else
        return natToBits 0xcf1f 16
  | .stbRef rev quiet =>
      if !rev && !quiet then
        return natToBits 0xcf11 16
      else if rev && !quiet then
        return natToBits 0xcf15 16
      else if !rev && quiet then
        return natToBits 0xcf19 16
      else
        return natToBits 0xcf1d 16
  | .stSliceConst _ =>
      throw .invOpcode
  | .stZeroes =>
      return natToBits 0xcf40 16
  | .stOnes =>
      return natToBits 0xcf41 16
  | .stSame =>
      return natToBits 0xcf42 16
  | .stref =>
      return natToBits 0xcc 8
  | .strefq =>
      return natToBits 0xcf18 16
  | .bbits =>
      return natToBits 0xcf31 16
  | .setcp cp =>
      -- Encode only the immediate SETCP form (no SETCPX), matching C++ `exec_set_cp`.
      if cp = -16 then throw .invOpcode
      if decide (-15 ≤ cp ∧ cp ≤ 239) then
        let b : Nat :=
          if cp ≥ 0 then
            cp.toNat
          else
            (256 + cp).toNat
        return natToBits 0xff 8 ++ natToBits b 8
      else
        throw .invOpcode
  | .setcpX =>
      return natToBits 0xfff0 16
  | .ifret =>
      return natToBits 0xdc 8
  | .ifnotret =>
      return natToBits 0xdd 8
  | .if_ =>
      return natToBits 0xde 8
  | .ifnot =>
      return natToBits 0xdf 8
  | .negate =>
      return natToBits 0xa3 8
  | .qnegate =>
      return natToBits 0xb7a3 16
  | .qpow2 =>
      return natToBits 0xb7ae 16
  | .inc =>
      return natToBits 0xa4 8
  | .qinc =>
      return natToBits 0xb7a4 16
  | .dec =>
      return natToBits 0xa5 8
  | .qdec =>
      return natToBits 0xb7a5 16
  | .add =>
      return natToBits 0xa0 8
  | .qadd =>
      return natToBits 0xb7a0 16
  | .addInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xa6 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .sub =>
      return natToBits 0xa1 8
  | .qsub =>
      return natToBits 0xb7a1 16
  | .qsubr =>
      return natToBits 0xb7a2 16
  | .subr =>
      return natToBits 0xa2 8
  | .mulInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xa7 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .mul =>
      return natToBits 0xa8 8
  | .qmul =>
      return natToBits 0xb7a8 16
  | .min =>
      return natToBits 0xb608 16
  | .max =>
      return natToBits 0xb609 16
  | .qmax =>
      return natToBits 0xb7b609 24
  | .minmax =>
      return natToBits 0xb60a 16
  | .qminmax =>
      return natToBits 0xb7b60a 24
  | .abs quiet =>
      if quiet then
        return natToBits 0xb7b60b 24
      else
        return natToBits 0xb60b 16
  | .bitsize =>
      return natToBits 0xb602 16
  | .ubitsize quiet =>
      if quiet then
        return natToBits 0xb7b603 24
      else
        return natToBits 0xb603 16
  | .mulShrModConst _ _ _ =>
      throw .invOpcode
  | .divMod d roundMode addMode quiet =>
      let roundEnc : Int := roundMode + 1
      if roundEnc < 0 ∨ roundEnc > 2 then
        throw .rangeChk
      if d = 0 ∨ d > 3 then
        throw .rangeChk
      if addMode && (d != 3) then
        throw .rangeChk
      let dEnc : Nat := if addMode then 0 else d
      let args4 : Nat := (dEnc <<< 2) + roundEnc.toNat
      if quiet then
        let word24 : Nat := (0xb7a90 <<< 4) + args4
        return natToBits word24 24
      else
        return natToBits (0xa900 + args4) 16
  | .mulDivMod d roundMode addMode quiet =>
      let roundEnc : Int := roundMode + 1
      if roundEnc < 0 ∨ roundEnc > 2 then
        throw .rangeChk
      if d > 3 then
        throw .rangeChk
      if addMode && d != 3 then
        throw .rangeChk
      let dEnc : Nat := if addMode then 0 else d
      if !addMode && dEnc = 0 then
        throw .rangeChk
      let args4 : Nat := (dEnc <<< 2) + roundEnc.toNat
      if quiet then
        let word24 : Nat := (0xb7a98 <<< 4) + args4
        return natToBits word24 24
      else
        return natToBits (0xa980 + args4) 16
  | .lshiftConst quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let imm : Nat := bits - 1
      if quiet then
        return natToBits 0xb7aa 16 ++ natToBits imm 8
      else
        return natToBits 0xaa 8 ++ natToBits imm 8
  | .rshiftConst quiet bits =>
      if bits = 0 ∨ bits > 256 then
        throw .rangeChk
      let imm : Nat := bits - 1
      if quiet then
        return natToBits 0xb7ab 16 ++ natToBits imm 8
      else
        return natToBits 0xab 8 ++ natToBits imm 8
  | .lshift =>
      return natToBits 0xac 8
  | .rshift =>
      return natToBits 0xad 8
  | .equal =>
      return natToBits 0xba 8
  | .neq =>
      return natToBits 0xbd 8
  | .and_ =>
      return natToBits 0xb0 8
  | .or =>
      return natToBits 0xb1 8
  | .xor =>
      return natToBits 0xb2 8
  | .not_ =>
      return natToBits 0xb3 8
  | .sgn =>
      return natToBits 0xb8 8
  | .less =>
      return natToBits 0xb9 8
  | .leq =>
      return natToBits 0xbb 8
  | .greater =>
      return natToBits 0xbc 8
  | .geq =>
      return natToBits 0xbe 8
  | .cmp =>
      return natToBits 0xbf 8
  | .qcmp =>
      return natToBits 0xb7bf 16
  | .sbits =>
      return natToBits 0xd749 16
  | .srefs =>
      return natToBits 0xd74a 16
  | .sbitrefs =>
      return natToBits 0xd74b 16
  | .cdepth =>
      return natToBits 0xd765 16
  | .sempty =>
      return natToBits 0xc700 16
  | .sdempty =>
      return natToBits 0xc701 16
  | .srempty =>
      return natToBits 0xc702 16
  | .sdCntLead0 =>
      return natToBits 0xc710 16
  | .sdCntTrail0 =>
      return natToBits 0xc712 16
  | .sdEq =>
      return natToBits 0xc705 16
  | .sdPpfx =>
      return natToBits 0xc70a 16
  | .sdPpfxRev =>
      return natToBits 0xc70b 16
  | .sdPfx =>
      return natToBits 0xc708 16
  | .sdPfxRev =>
      return natToBits 0xc709 16
  | .sdLexCmp =>
      return natToBits 0xc704 16
  | .sdcutfirst =>
      return natToBits 0xd720 16
  | .sdskipfirst =>
      return natToBits 0xd721 16
  | .sdcutlast =>
      return natToBits 0xd722 16
  | .sdskiplast =>
      return natToBits 0xd723 16
  | .sdBeginsX quiet =>
      return natToBits (if quiet then 0xd727 else 0xd726) 16
  | .sdBeginsConst .. =>
      throw .invOpcode
  | .lessInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc1 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .qlessInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xb7c1 16 ++ natToBits imm 8
      else
        throw .rangeChk
  | .eqInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc0 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .gtInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc2 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .neqInt n =>
      if decide (-128 ≤ n ∧ n ≤ 127) then
        let imm : Nat := if n ≥ 0 then n.toNat else (256 - (-n).toNat)
        return natToBits 0xc3 8 ++ natToBits imm 8
      else
        throw .rangeChk
  | .pushNull =>
      return natToBits 0x6d 8
  | .isNull =>
      return natToBits 0x6e 8
  | .nullSwapIf =>
      return natToBits 0x6fa0 16
  | .nullSwapIfNot =>
      return natToBits 0x6fa1 16
  | .nullRotrIf =>
      return natToBits 0x6fa2 16
  | .nullRotrIfNot =>
      return natToBits 0x6fa3 16
  | .nullSwapIf2 =>
      return natToBits 0x6fa4 16
  | .nullSwapIfNot2 =>
      return natToBits 0x6fa5 16
  | .nullRotrIf2 =>
      return natToBits 0x6fa6 16
  | .nullRotrIfNot2 =>
      return natToBits 0x6fa7 16
  | .tupleOp op =>
      encodeTupleInstr op
  | .cellOp op =>
      encodeCellInstr op
  | .cellExt op =>
      encodeCellExtInstr op
  | .cryptoOp op =>
      encodeCryptoInstr op
  | .tonEnvOp op =>
      encodeTonEnvInstr op
  | .debugOp op =>
      encodeDebugInstr op
  | .arithExt op =>
      encodeArithExtInstr op
  | .dictExt _ =>
      throw .invOpcode
  | .blkdrop2 x y =>
      if x ≤ 15 ∧ y ≤ 15 then
        let args : Nat := (x <<< 4) + y
        if args < 0x10 then
          throw .rangeChk
        return natToBits (0x6c00 + args) 16
      else
        throw .rangeChk
  | .pushSliceConst _ =>
      throw .invOpcode
  | .pushCont _ =>
      throw .invOpcode
  | .pushRef _ =>
      throw .invOpcode
  | .pushRefSlice _ =>
      throw .invOpcode
  | .pushRefCont _ =>
      throw .invOpcode
  | .execute =>
      return natToBits 0xd8 8
  | .jmpx =>
      return natToBits 0xd9 8
  | .callxArgs params retVals =>
      if params > 15 then
        throw .rangeChk
      if retVals = -1 then
        return natToBits (0xdb00 + params) 16
      if decide (0 ≤ retVals ∧ retVals ≤ 15) then
        let args8 : Nat := (params <<< 4) + retVals.toNat
        return natToBits 0xda 8 ++ natToBits args8 8
      else
        throw .rangeChk
  | .jmpxArgs params =>
      if params > 15 then
        throw .rangeChk
      return natToBits (0xdb10 + params) 16
  | .callcc =>
      return natToBits 0xdb34 16
  | .jmpxData =>
      return natToBits 0xdb35 16
  | .callccArgs params retVals =>
      if params > 15 then
        throw .rangeChk
      if retVals < -1 ∨ retVals > 14 then
        throw .rangeChk
      let lo : Nat := if retVals = -1 then 15 else retVals.toNat
      let args8 : Nat := (params <<< 4) + lo
      return natToBits 0xdb36 16 ++ natToBits args8 8
  | .callxVarArgs =>
      return natToBits 0xdb38 16
  | .jmpxVarArgs =>
      return natToBits 0xdb3a 16
  | .callccVarArgs =>
      return natToBits 0xdb3b 16
  | .ret =>
      return natToBits 0xdb30 16
  | .retAlt =>
      return natToBits 0xdb31 16
  | .retBool =>
      return natToBits 0xdb32 16
  | .retVarArgs =>
      return natToBits 0xdb39 16
  | .retData =>
      return natToBits 0xdb3f 16
  | .retArgs n =>
      if n > 15 then
        throw .rangeChk
      return natToBits (0xdb20 + n) 16
  | .ifjmp =>
      return natToBits 0xe0 8
  | .ifnotjmp =>
      return natToBits 0xe1 8
  | .ifelse =>
      return natToBits 0xe2 8
  | .ifref _ =>
      throw .invOpcode
  | .ifnotref _ =>
      throw .invOpcode
  | .ifjmpref _ =>
      throw .invOpcode
  | .ifnotjmpref _ =>
      throw .invOpcode
  | .ifrefElse _ =>
      throw .invOpcode
  | .ifelseRef _ =>
      throw .invOpcode
  | .ifrefElseRef _ _ =>
      throw .invOpcode
  | .callRef _ =>
      throw .invOpcode
  | .jmpRef _ =>
      throw .invOpcode
  | .jmpRefData _ =>
      throw .invOpcode
  | .callDict idx =>
      if idx < 256 then
        return natToBits (0xf000 + idx) 16
      else if idx ≤ 0x3fff then
        -- CALLDICT_LONG: 10-bit prefix (0x3c4) + 14-bit args.
        let prefix10 : Nat := 0x3c4
        let word24 : Nat := (prefix10 <<< 14) + (idx &&& 0x3fff)
        return natToBits word24 24
      else
        throw .rangeChk
  | .prepareDict idx =>
      if idx > 0x3fff then
        throw .rangeChk
      let prefix10 : Nat := 0xf180 >>> 6
      let word24 : Nat := (prefix10 <<< 14) + (idx &&& 0x3fff)
      return natToBits word24 24
  | .until =>
      return natToBits 0xe6 8
  | .while_ =>
      return natToBits 0xe8 8
  | .blkdrop n =>
      if n < 16 then
        return natToBits (0x5f00 + n) 16
      else
        throw .rangeChk
  | .drop2 =>
      return natToBits 0x5b 8
  | .throw exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 63 then
        let prefix10 : Nat := 0xf200 >>> 6
        let word16 : Nat := (prefix10 <<< 6) + exc.toNat
        return natToBits word16 16
      else if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2c0 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwIf exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 63 then
        let prefix10 : Nat := 0xf240 >>> 6
        let word16 : Nat := (prefix10 <<< 6) + exc.toNat
        return natToBits word16 16
      else if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2d0 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwIfNot exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 63 then
        let prefix10 : Nat := 0xf280 >>> 6
        let word16 : Nat := (prefix10 <<< 6) + exc.toNat
        return natToBits word16 16
      else if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2e0 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwArg exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2c8 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwArgIf exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2d8 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwArgIfNot exc =>
      if exc < 0 then throw .rangeChk
      if exc ≤ 0x7ff then
        let prefix13 : Nat := 0xf2e8 >>> 3
        let word24 : Nat := (prefix13 <<< 11) + exc.toNat
        return natToBits word24 24
      else
        throw .rangeChk
  | .throwAny hasParam hasCond throwCond =>
      if !hasCond && throwCond then
        throw .rangeChk
      let args : Nat :=
        if !hasCond then
          if hasParam then 1 else 0
        else if throwCond then
          if hasParam then 3 else 2
        else
          if hasParam then 5 else 4
      return natToBits (0xf2f0 + args) 16
  | .try_ =>
      return natToBits 0xf2ff 16
  | .tryArgs params retVals =>
      if params > 15 ∨ retVals > 15 then
        throw .rangeChk
      let args8 : Nat := (params <<< 4) + retVals
      return natToBits 0xf3 8 ++ natToBits args8 8
  | .stdict =>
      return natToBits 0xf400 16
  | .skipdict =>
      return natToBits 0xf401 16
  | .lddict preload quiet =>
      let args : Nat := (if preload then 1 else 0) + (if quiet then 2 else 0)
      return natToBits (0xf404 + args) 16
  | .dictGet intKey unsigned byRef =>
      if intKey then
        let flags : Nat := (if byRef then 1 else 0) + (if unsigned then 2 else 0)
        return natToBits (0xf40c + flags) 16
      else
        if unsigned then throw .invOpcode
        return natToBits (if byRef then 0xf40b else 0xf40a) 16
  | .dictGetNear args4 =>
      if args4 < 4 ∨ args4 > 15 then
        throw .rangeChk
      return natToBits (0xf470 + args4) 16
  | .dictGetMinMax args5 =>
      if args5 > 31 then
        throw .rangeChk
      -- Only the four fixed ranges used by TON: MIN, MAX, REMMIN, REMMAX.
      let ok :=
        (2 ≤ args5 ∧ args5 ≤ 7) ∨ (10 ≤ args5 ∧ args5 ≤ 15) ∨ (18 ≤ args5 ∧ args5 ≤ 23) ∨
          (26 ≤ args5 ∧ args5 ≤ 31)
      if !ok then
        throw .invOpcode
      return natToBits (0xf480 + args5) 16
  | .dictSet intKey unsigned byRef mode =>
      -- DICT{I,U}{SET,REPLACE,ADD}{REF?}: 0xf412..0xf417 / 0xf422..0xf427 / 0xf432..0xf437.
      let base : Nat :=
        match mode with
        | .set => 0xf412
        | .replace => 0xf422
        | .add => 0xf432
      let w16 : Nat :=
        if !intKey then
          if unsigned then
            -- Unsigned is only meaningful for intKey.
            0
          else
            base + (if byRef then 1 else 0)
        else
          let kind : Nat := if unsigned then 4 else 2
          base + kind + (if byRef then 1 else 0)
      if w16 = 0 then
        throw .invOpcode
      return natToBits w16 16
  | .dictSetB intKey unsigned mode =>
      -- DICT{I,U}?SETB (builder value): 0xf441..0xf443.
      -- MVP: only SETB is supported by the cp0 encoding/decoding in this repo.
      if mode != .set then
        throw .invOpcode
      let w16 : Nat :=
        if !intKey then
          if unsigned then 0 else 0xf441
        else
          if unsigned then 0xf443 else 0xf442
      if w16 = 0 then
        throw .invOpcode
      return natToBits w16 16
  | .dictReplaceB intKey unsigned =>
      if intKey then
        return natToBits (if unsigned then 0xf44b else 0xf44a) 16
      else
        if unsigned then throw .invOpcode
        return natToBits 0xf449 16
  | .dictPushConst _ _ =>
      throw .invOpcode
  | .dictGetExec unsigned doCall pushZ =>
      -- DICT{I,U}GET{JMP,EXEC}{Z}: 0xf4a0..0xf4a3 (no Z) and 0xf4bc..0xf4bf (Z).
      let base : Nat := if pushZ then 0xf4bc else 0xf4a0
      let w16 : Nat := base + (if unsigned then 1 else 0) + (if doCall then 2 else 0)
      return natToBits w16 16

def assembleCp0 (code : List Instr) : Except Excno Cell := do
  let mut bits : BitString := #[]
  for i in code do
    bits := bits ++ (← encodeCp0 i)
  return Cell.mkOrdinary bits #[]

end TvmLean
