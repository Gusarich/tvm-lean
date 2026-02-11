import TvmLean.Semantics.Exec.Common

namespace TvmLean

def leBytesToBitString (bs : BitString) (bytes : Nat) : BitString :=
  -- `bs` is `bytes*8` bits, big-endian overall. Convert to little-endian byte order.
  let bits : Nat := bytes * 8
  Id.run do
    let mut out : BitString := #[]
    for i in [0:bytes] do
      let start : Nat := bits - (i + 1) * 8
      out := out ++ bs.extract start (start + 8)
    return out

def intSignedBitSizeTwos (n : Int) : Nat :=
  -- Mirrors `BigInt::bit_size(true)` enough for TVM VarInt encoding.
  if n = 0 then
    0
  else if n > 0 then
    natLenBits n.toNat + 1
  else
    natLenBits (-n - 1).toNat + 1

def lookupLibraryIn? (hashBits : BitString) (libCollection : Cell) : Option Cell :=
  -- Mirrors TON `lookup_library_in` used by `VmState::load_library`.
  -- Returns `none` if dictionary lookup fails or the value does not match the expected layout.
  match dictLookup (some libCollection) hashBits with
  | .error _ => none
  | .ok none => none
  | .ok (some val) =>
      if !val.haveRefs 1 then
        none
      else
        let root := val.cell.refs[val.refPos]!
        let keyBytes := bitStringToBytesBE hashBits
        if Cell.hashBytes root == keyBytes then
          some root
        else
          none

set_option maxHeartbeats 1000000 in
def execInstrCellExt (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellExt op =>
      match op with
      | .btos =>
          VM.checkUnderflow 1
          let b ← VM.popBuilder
          let c : Cell := b.finalize
          VM.push (.slice (Slice.ofCell c))
      | .stLeInt unsigned bytes =>
          VM.checkUnderflow 2
          if bytes != 4 ∧ bytes != 8 then
            throw .rangeChk
          let bits : Nat := bytes * 8
          -- Match C++ operand order: builder is on top, integer is below.
          let b ← VM.popBuilder
          let x ← VM.popInt
          if !b.canExtendBy bits then
            throw .cellOv
          match x with
          | .nan => throw .rangeChk
          | .num n =>
              let ok :=
                if unsigned then
                  intUnsignedFitsBits n bits
                else
                  intSignedFitsBits n bits
              if !ok then
                throw .rangeChk
              let be : BitString ←
                if unsigned then
                  pure (natToBits n.toNat bits)
                else
                  match intToBitsTwos n bits with
                  | .error e => throw e
                  | .ok bs => pure bs
              let le := leBytesToBitString be bytes
              VM.push (.builder (b.storeBits le))
      | .stRefConst c =>
          VM.checkUnderflow 1
          let b ← VM.popBuilder
          if !b.canExtendBy 0 1 then
            throw .cellOv
          VM.push (.builder { b with refs := b.refs.push c })
      | .stRef2Const c1 c2 =>
          VM.checkUnderflow 1
          let b ← VM.popBuilder
          if !b.canExtendBy 0 2 then
            throw .cellOv
          VM.push (.builder { b with refs := (b.refs.push c1).push c2 })
      | .hashbu =>
          VM.checkUnderflow 1
          let b ← VM.popBuilder
          let c : Cell := b.finalize
          let h : Nat := bytesToNatBE (Cell.hashBytes c)
          VM.pushIntQuiet (.num (Int.ofNat h)) false
      | .cdataSize _ | .sdataSize _ =>
          next
      | .plduz c =>
          VM.checkUnderflow 1
          -- Mirrors TON `exec_preload_uint_fixed_0e` (cellops.cpp): prefetch `bits` with zero-extension.
          let bits : Nat := 32 * (c + 1)
          let s ← VM.popSlice
          let ldBits : Nat := Nat.min bits s.bitsRemaining
          let u : Nat := bitsToNat (s.readBits ldBits)
          let u' : Nat := u <<< (bits - ldBits)
          VM.push (.slice s)
          VM.push (.int (.num (Int.ofNat u')))
      | .ldVarInt signed kind =>
          VM.checkUnderflow 1
          -- Mirrors TON `exec_load_var_integer` with quiet=false (tonops.cpp).
          let lenBits : Nat ←
            if kind = 16 then
              pure 4
            else if kind = 32 then
              pure 5
            else
              throw .invOpcode
          let s0 ← VM.popSlice
          let (lenBytes, s1) ← s0.takeBitsAsNatCellUnd lenBits
          let dataBits : Nat := lenBytes * 8
          if !s1.haveBits dataBits then
            throw .cellUnd
          let bs := s1.readBits dataBits
          let n : Int :=
            if signed then
              bitsToIntSignedTwos bs
            else
              Int.ofNat (bitsToNat bs)
          VM.push (.int (.num n))
          VM.push (.slice (s1.advanceBits dataBits))
      | .stVarInt signed kind =>
          VM.checkUnderflow 2
          -- Mirrors TON `exec_store_var_integer` with quiet=false (tonops.cpp).
          let lenBits : Nat ←
            if kind = 16 then
              pure 4
            else if kind = 32 then
              pure 5
            else
              throw .invOpcode
          -- Stack: ... builder x -- ...
          let x ← VM.popInt
          let b ← VM.popBuilder
          match x with
          | .nan => throw .rangeChk
          | .num n =>
              if !signed && n < 0 then
                -- Unsigned VarInt cannot encode negative numbers.
                throw .rangeChk
              let lenBytes : Nat :=
                if signed then
                  (intSignedBitSizeTwos n + 7) / 8
                else
                  (natLenBits n.toNat + 7) / 8
              if lenBytes ≥ (1 <<< lenBits) then
                throw .rangeChk
              let totalBits : Nat := lenBits + lenBytes * 8
              if !b.canExtendBy totalBits then
                throw .cellOv
              let payload : BitString ←
                if signed then
                  match intToBitsTwos n (lenBytes * 8) with
                  | .ok bs => pure bs
                  | .error e => throw e
                else
                  pure (natToBits n.toNat (lenBytes * 8))
              let bs := natToBits lenBytes lenBits ++ payload
              VM.push (.builder (b.storeBits bs))
      | .xload quiet =>
          VM.checkUnderflow 1
          -- Mirrors TON `exec_load_special_cell` (cellops.cpp) for modern TVM:
          -- - Always charges a cell load for the popped cell.
          -- - Resolves library exotic cells via the library collections in `VmState.libraries`.
          let c0 ← VM.popCell
          VM.registerCellLoad c0
          let st ← get
          let resolve : Except Excno Cell := do
            if !c0.special then
              return c0
            if c0.bits.size < 8 then
              throw .cellUnd
            let tyByte : Nat := bitsToNat (c0.bits.extract 0 8)
            match CellSpecialType.ofByte? tyByte with
            | some .library =>
                if c0.bits.size != 8 * (1 + 32) || c0.refs.size != 0 then
                  throw .cellUnd
                let hashBits : BitString := c0.bits.extract 8 (8 + 256)
                let mut found : Option Cell := none
                for lib in st.libraries do
                  match lookupLibraryIn? hashBits lib with
                  | some c =>
                      found := some c
                      break
                  | none => pure ()
                match found with
                | some c => return c
                | none => throw .cellUnd
            | _ =>
                throw .cellUnd
          match resolve with
          | .ok c =>
              VM.push (.cell c)
              if quiet then
                VM.pushSmallInt (-1)
          | .error e =>
              if quiet then
                VM.pushSmallInt 0
              else
                throw e
  | _ => next

end TvmLean
