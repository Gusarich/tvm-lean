import Std

namespace TvmLean

/-! A small, executable “Milestone 1” core:

- Core datatypes (`IntVal`, `Value`, `Continuation`, `VmState`)
- A tiny instruction AST and an executable `step`
- Minimal cp0 decode/encode utilities (Milestone 2)
- WF predicates + theorem statements (mostly `sorry` for now)

This is intentionally minimal and designed to be refactored as we add decoding/cells/dicts/opcodes.
-/

inductive Excno : Type
  | none
  | alt
  | stkUnd
  | stkOv
  | intOv
  | rangeChk
  | invOpcode
  | typeChk
  | cellOv
  | cellUnd
  | dictErr
  | unknown
  | fatal
  | outOfGas
  | virtErr
  deriving DecidableEq, Repr

def Excno.toInt : Excno → Int
  | .none => 0
  | .alt => 1
  | .stkUnd => 2
  | .stkOv => 3
  | .intOv => 4
  | .rangeChk => 5
  | .invOpcode => 6
  | .typeChk => 7
  | .cellOv => 8
  | .cellUnd => 9
  | .dictErr => 10
  | .unknown => 11
  | .fatal => 12
  | .outOfGas => 13
  | .virtErr => 14

instance : ToString Excno := ⟨fun
  | .none => "none"
  | .alt => "alt"
  | .stkUnd => "stkUnd"
  | .stkOv => "stkOv"
  | .intOv => "intOv"
  | .rangeChk => "rangeChk"
  | .invOpcode => "invOpcode"
  | .typeChk => "typeChk"
  | .cellOv => "cellOv"
  | .cellUnd => "cellUnd"
  | .dictErr => "dictErr"
  | .unknown => "unknown"
  | .fatal => "fatal"
  | .outOfGas => "outOfGas"
  | .virtErr => "virtErr"⟩

inductive IntVal : Type
  | nan
  | num (n : Int)
  deriving DecidableEq, Repr

def IntVal.isValid : IntVal → Bool
  | .nan => false
  | .num _ => true

def IntVal.signedFits257 : IntVal → Bool
  | .nan => false
  | .num n =>
      -- [-2^256, 2^256)
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      decide (lo ≤ n ∧ n < hi)

def IntVal.add (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => .num (a + b)
  | _, _ => .nan

def IntVal.inc (x : IntVal) : IntVal :=
  x.add (.num 1)

def IntVal.equalResult (x y : IntVal) : IntVal :=
  match x, y with
  | .num a, .num b => if a = b then .num (-1) else .num 0
  | _, _ => .nan

def IntVal.toBool? (x : IntVal) : Except Excno Bool :=
  match x with
  | .nan => .error .intOv
  | .num n => .ok (n ≠ 0)

abbrev BitString := Array Bool

def bitsToNat (bs : BitString) : Nat :=
  bs.foldl (fun acc b => (acc <<< 1) + (if b then 1 else 0)) 0

def natToBits (n bits : Nat) : BitString :=
  Array.ofFn (n := bits) fun i =>
    let k := bits - 1 - i.1
    n.testBit k

def intPow2 (bits : Nat) : Int :=
  (2 : Int) ^ bits

structure Cell where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Cell.empty : Cell :=
  { bits := #[], refs := #[] }

instance : Inhabited Cell := ⟨Cell.empty⟩

partial def Cell.beq (a b : Cell) : Bool :=
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
  { bits := natToBits n bits, refs := #[] }

def Cell.depthLe (c : Cell) : Nat → Bool
  | 0 => false
  | limit + 1 =>
      c.refs.all (fun r => r.depthLe limit)

structure Slice where
  cell : Cell
  bitPos : Nat
  refPos : Nat
  deriving Repr

def Slice.ofCell (c : Cell) : Slice :=
  { cell := c, bitPos := 0, refPos := 0 }

def Slice.bitsRemaining (s : Slice) : Nat :=
  s.cell.bits.size - s.bitPos

def Slice.refsRemaining (s : Slice) : Nat :=
  s.cell.refs.size - s.refPos

def Slice.haveBits (s : Slice) (n : Nat) : Bool :=
  decide (s.bitPos + n ≤ s.cell.bits.size)

def Slice.readBits (s : Slice) (n : Nat) : BitString :=
  s.cell.bits.extract s.bitPos (s.bitPos + n)

def Slice.advanceBits (s : Slice) (n : Nat) : Slice :=
  { s with bitPos := s.bitPos + n }

structure Builder where
  bits : BitString
  refs : Array Cell
  deriving Repr

def Builder.empty : Builder :=
  { bits := #[], refs := #[] }

def Builder.canExtendBy (b : Builder) (bits : Nat) (refs : Nat := 0) : Bool :=
  decide (b.bits.size + bits ≤ 1023 ∧ b.refs.size + refs ≤ 4)

def Builder.storeBits (b : Builder) (bs : BitString) : Builder :=
  { b with bits := b.bits ++ bs }

def Builder.finalize (b : Builder) : Cell :=
  { bits := b.bits, refs := b.refs }

inductive Instr : Type
  | nop
  | pushInt (n : IntVal)
  | push (idx : Nat)    -- PUSH s[idx]
  | pop (idx : Nat)     -- POP s[idx]
  | xchg0 (idx : Nat)   -- XCHG s0,s[idx]
  | pushCtr (idx : Nat) -- PUSHCTRX <idx> (we'll use it for c4/c5/c7 too)
  | popCtr (idx : Nat)  -- POPCTRX <idx>
  | ctos
  | newc
  | endc
  | ends
  | ldu (bits : Nat)
  | stu (bits : Nat)
  | setcp (cp : Int)
  | ifret
  | ifnotret
  | inc
  | equal
  | throwIfNot (exc : Int) -- THROWIFNOT <exc>
  deriving DecidableEq, Repr

inductive Continuation : Type
  | ordinary (code : Slice)
  | quit (exitCode : Int)
  | excQuit
  deriving Repr

inductive Value : Type
  | int (i : IntVal)
  | cell (c : Cell)
  | slice (s : Slice)
  | builder (b : Builder)
  | tuple (t : Array Value)
  | cont (k : Continuation)
  | null
  deriving Repr

instance : Inhabited Value := ⟨.null⟩

def Value.pretty : Value → String
  | .int .nan => "NaN"
  | .int (.num n) => toString n
  | .null => "null"
  | .cell _ => "<cell>"
  | .slice _ => "<slice>"
  | .builder _ => "<builder>"
  | .tuple t => s!"<tuple:{t.size}>"
  | .cont k =>
      match k with
      | .ordinary _ => "<cont:ord>"
      | .quit n => s!"<cont:quit {n}>"
      | .excQuit => "<cont:excquit>"

instance : ToString Value := ⟨Value.pretty⟩

def arrayBeqBy {α : Type} (a b : Array α) (beq : α → α → Bool) : Bool :=
  if a.size != b.size then
    false
  else
    Id.run do
      let mut ok := true
      for i in [0:a.size] do
        match a.get? i, b.get? i with
        | some x, some y =>
            if !(beq x y) then
              ok := false
        | _, _ =>
            ok := false
      return ok

def arrayBeq {α : Type} [BEq α] (a b : Array α) : Bool :=
  arrayBeqBy a b (fun x y => x == y)

instance : BEq Slice := ⟨fun a b => a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell⟩
instance : BEq Builder := ⟨fun a b => a.bits == b.bits && arrayBeq a.refs b.refs⟩

instance : BEq Continuation := ⟨fun a b =>
  match a, b with
  | .quit x, .quit y => x == y
  | .excQuit, .excQuit => true
  | .ordinary x, .ordinary y => x == y
  | _, _ => false⟩

partial def Value.beq : Value → Value → Bool
  | .null, .null => true
  | .int x, .int y => x == y
  | .cell x, .cell y => x == y
  | .slice x, .slice y => x == y
  | .builder x, .builder y => x == y
  | .tuple x, .tuple y => arrayBeqBy x y Value.beq
  | .cont x, .cont y => x == y
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

abbrev Stack := Array Value

structure GasLimits where
  gasMax : Int
  gasLimit : Int
  gasCredit : Int
  gasRemaining : Int
  gasBase : Int
  deriving Repr

def GasLimits.infty : Int := (Int.ofNat (1 <<< 63)) - 1

def GasLimits.default : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := GasLimits.infty
    gasCredit := 0
    gasRemaining := GasLimits.infty
    gasBase := GasLimits.infty }

def GasLimits.ofLimit (limit : Int) : GasLimits :=
  { gasMax := GasLimits.infty
    gasLimit := limit
    gasCredit := 0
    gasRemaining := limit
    gasBase := limit }

def GasLimits.gasConsumed (g : GasLimits) : Int :=
  g.gasBase - g.gasRemaining

def GasLimits.consume (g : GasLimits) (amount : Int) : GasLimits :=
  { g with gasRemaining := g.gasRemaining - amount }

structure CommittedState where
  c4 : Cell
  c5 : Cell
  committed : Bool
  deriving Repr

def CommittedState.empty : CommittedState :=
  { c4 := Cell.empty, c5 := Cell.empty, committed := false }

def gasPerInstr : Int := 10
def exceptionGasPrice : Int := 50
def implicitJmpRefGasPrice : Int := 10
def implicitRetGasPrice : Int := 5
def cellCreateGasPrice : Int := 500

def instrGas (i : Instr) : Int :=
  match i with
  | .endc => gasPerInstr + cellCreateGasPrice
  | _ => gasPerInstr

/-! ### Minimal cp0 decoding (Milestone 2) -/

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

def decodeCp0 (s : Slice) : Except Excno (Instr × Slice) := do
  -- PUSHINT (tinyint4): 4-bit prefix 0x7, 4-bit immediate.
  let p4 ← s.peekBitsAsNat 4
  if p4 = 0x7 then
    let (b8, s') ← s.takeBitsAsNat 8
    let imm4 : Nat := b8 &&& 0xf
    let x : Int := Int.ofNat ((imm4 + 5) &&& 0xf) - 5
    return (.pushInt (.num x), s')

  -- Exception opcodes: THROWIFNOT short/long.
  -- Short: 10-bit prefix (0xf280 >> 6), 6-bit excno.
  if s.haveBits 10 then
    let p10 := bitsToNat (s.readBits 10)
    if p10 = (0xf280 >>> 6) then
      let (_, s10) ← s.takeBitsAsNat 10
      let (exc, s16) ← s10.takeBitsAsNat 6
      return (.throwIfNot (Int.ofNat exc), s16)
  -- Long: 13-bit prefix (0xf2e0 >> 3), 11-bit excno.
  if s.haveBits 13 then
    let p13 := bitsToNat (s.readBits 13)
    if p13 = (0xf2e0 >>> 3) then
      let (_, s13) ← s.takeBitsAsNat 13
      let (exc, s24) ← s13.takeBitsAsNat 11
      return (.throwIfNot (Int.ofNat exc), s24)

  -- PUSHINT (8/16/long)
  let b8 ← s.peekBitsAsNat 8
  if b8 = 0x80 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.pushInt (.num (natToIntSignedTwos arg 8)), s16)
  if b8 = 0x81 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s24) ← s8.takeBitsAsNat 16
    return (.pushInt (.num (natToIntSignedTwos arg 16)), s24)
  if b8 = 0x82 then
    -- Extended constant: 0x82 (8) + len (5) + value (3 + 8*(len+2)).
    if !s.haveBits 13 then
      throw .invOpcode
    let (_, s8) ← s.takeBitsAsNat 8
    let (len5, s13) ← s8.takeBitsAsNat 5
    let l : Nat := len5 + 2
    let width : Nat := 3 + l * 8
    if !s13.haveBits width then
      throw .invOpcode
    let bs := s13.readBits width
    let s' := s13.advanceBits width
    return (.pushInt (.num (bitsToIntSignedTwos bs)), s')

  -- 16-bit control register ops: PUSH c<i>, POP c<i>.
  if s.haveBits 16 then
    let w16 := bitsToNat (s.readBits 16)
    if w16 &&& 0xfff8 = 0xed40 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.pushCtr idx, s16)
    if w16 &&& 0xfff8 = 0xed50 then
      let idx : Nat := w16 &&& 0xf
      if idx = 6 then throw .invOpcode
      let (_, s16) ← s.takeBitsAsNat 16
      return (.popCtr idx, s16)
    if w16 &&& 0xff00 = 0xff00 then
      let b : Nat := w16 &&& 0xff
      if b = 0xf0 then
        throw .invOpcode
      -- Match `exec_set_cp`: cp = ((b + 0x10) & 0xff) - 0x10.
      let cp : Int := Int.ofNat ((b + 0x10) &&& 0xff) - 0x10
      let (_, s16) ← s.takeBitsAsNat 16
      return (.setcp cp, s16)

  -- 8-bit opcodes / fixed+arg opcodes
  if b8 = 0x00 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.nop, s')
  if b8 = 0x01 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg0 1, s')
  if 0x02 ≤ b8 ∧ b8 ≤ 0x0f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.xchg0 idx, s')
  if b8 = 0x11 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.xchg0 idx, s16)
  if b8 = 0x20 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.push 0, s')
  if b8 = 0x21 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.push 1, s')
  if 0x22 ≤ b8 ∧ b8 ≤ 0x2f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.push idx, s')
  if b8 = 0x30 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop 0, s')
  if b8 = 0x31 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop 1, s')
  if 0x32 ≤ b8 ∧ b8 ≤ 0x3f then
    let idx : Nat := b8 &&& 0xf
    let (_, s') ← s.takeBitsAsNat 8
    return (.pop idx, s')
  if b8 = 0x56 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.push idx, s16)
  if b8 = 0x57 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (idx, s16) ← s8.takeBitsAsNat 8
    return (.pop idx, s16)
  if b8 = 0xa4 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.inc, s')
  if b8 = 0xba then
    let (_, s') ← s.takeBitsAsNat 8
    return (.equal, s')
  if b8 = 0xc8 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.newc, s')
  if b8 = 0xc9 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.endc, s')
  if b8 = 0xcb then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.stu (arg + 1), s16)
  if b8 = 0xd0 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ctos, s')
  if b8 = 0xd1 then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ends, s')
  if b8 = 0xd3 then
    let (_, s8) ← s.takeBitsAsNat 8
    let (arg, s16) ← s8.takeBitsAsNat 8
    return (.ldu (arg + 1), s16)
  if b8 = 0xdc then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifret, s')
  if b8 = 0xdd then
    let (_, s') ← s.takeBitsAsNat 8
    return (.ifnotret, s')

  throw .invOpcode

def intToBitsTwos (n : Int) (bits : Nat) : Except Excno BitString := do
  if bits = 0 then
    return #[]
  let modulus : Nat := 1 <<< bits
  if n ≥ 0 then
    let u := n.toNat
    if u ≥ modulus then
      throw .rangeChk
    return natToBits u bits
  else
    -- two's complement: 2^bits - |n|
    let abs : Nat := (-n).toNat
    if abs = 0 ∨ abs ≥ modulus then
      throw .rangeChk
    return natToBits (modulus - abs) bits

def encodeCp0 (i : Instr) : Except Excno BitString := do
  match i with
  | .nop =>
      return natToBits 0x00 8
  | .pushInt .nan =>
      throw .invOpcode
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
        -- For MVP assembly, pick the max width; it always decodes correctly and stays within 257-bit range checks.
        let len5 : Nat := 31
        let l := len5 + 2
        let width := 3 + l * 8
        let prefix13 : Nat := (0x82 <<< 5) + len5
        let valBits ← intToBitsTwos n width
        return natToBits prefix13 13 ++ valBits
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
  | .pushCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed40 + idx) 16
  | .popCtr idx =>
      if idx = 6 ∨ idx > 7 then throw .rangeChk
      return natToBits (0xed50 + idx) 16
  | .ctos =>
      return natToBits 0xd0 8
  | .newc =>
      return natToBits 0xc8 8
  | .endc =>
      return natToBits 0xc9 8
  | .ends =>
      return natToBits 0xd1 8
  | .ldu bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xd3 8 ++ natToBits (bits - 1) 8
  | .stu bits =>
      if bits = 0 ∨ bits > 256 then throw .rangeChk
      return natToBits 0xcb 8 ++ natToBits (bits - 1) 8
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
  | .ifret =>
      return natToBits 0xdc 8
  | .ifnotret =>
      return natToBits 0xdd 8
  | .inc =>
      return natToBits 0xa4 8
  | .equal =>
      return natToBits 0xba 8
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

def assembleCp0 (code : List Instr) : Except Excno Cell := do
  let mut bits : BitString := #[]
  for i in code do
    bits := bits ++ (← encodeCp0 i)
  return { bits, refs := #[] }

structure Regs where
  c0 : Continuation
  c1 : Continuation
  c2 : Continuation
  c3 : Continuation
  c4 : Cell
  c5 : Cell
  c7 : Array Value
  deriving Repr

def Regs.initial : Regs :=
  { c0 := .quit 0
    c1 := .quit 1
    c2 := .excQuit
    c3 := .quit 11
    c4 := Cell.empty
    c5 := Cell.empty
    c7 := #[] }

structure VmState where
  stack : Stack
  regs : Regs
  cc : Continuation
  cp : Int
  gas : GasLimits
  cstate : CommittedState
  maxDataDepth : Nat
  deriving Repr

def VmState.initial (code : Cell) (gasLimit : Int := 1_000_000) : VmState :=
  { stack := #[]
    regs := Regs.initial
    cc := .ordinary (Slice.ofCell code)
    cp := 0
    gas := GasLimits.ofLimit gasLimit
    cstate := CommittedState.empty
    maxDataDepth := 512 }

abbrev VM := ExceptT Excno (StateM VmState)

def VM.push (v : Value) : VM Unit := do
  modify fun st => { st with stack := st.stack.push v }

def VM.pop : VM Value := do
  let st ← get
  if h : 0 < st.stack.size then
    let v := st.stack.back (h := h)
    modify fun st => { st with stack := st.stack.pop }
    return v
  else
    throw .stkUnd

def VM.fetch (idxFromTop : Nat) : VM Value := do
  let st ← get
  if _h : idxFromTop < st.stack.size then
    let pos := st.stack.size - 1 - idxFromTop
    return st.stack[pos]!
  else
    throw .stkUnd

def VM.swap (iFromTop jFromTop : Nat) : VM Unit := do
  let st ← get
  let need := Nat.max iFromTop jFromTop
  if _h : need < st.stack.size then
    let pi := st.stack.size - 1 - iFromTop
    let pj := st.stack.size - 1 - jFromTop
    let vi := st.stack[pi]!
    let vj := st.stack[pj]!
    modify fun st =>
      let s := st.stack
      { st with stack := (s.set! pi vj).set! pj vi }
  else
    throw .stkUnd

def VM.popInt : VM IntVal := do
  let v ← VM.pop
  match v with
  | .int i => return i
  | _ => throw .typeChk

def VM.popCell : VM Cell := do
  let v ← VM.pop
  match v with
  | .cell c => return c
  | _ => throw .typeChk

def VM.popSlice : VM Slice := do
  let v ← VM.pop
  match v with
  | .slice s => return s
  | _ => throw .typeChk

def VM.popBuilder : VM Builder := do
  let v ← VM.pop
  match v with
  | .builder b => return b
  | _ => throw .typeChk

def VM.popBool : VM Bool := do
  let i ← VM.popInt
  match i.toBool? with
  | .ok b => return b
  | .error e => throw e

def VM.pushIntQuiet (i : IntVal) (quiet : Bool) : VM Unit := do
  if i.signedFits257 then
    VM.push (.int i)
  else
    if quiet then
      VM.push (.int .nan)
    else
      throw .intOv

def VM.pushSmallInt (n : Int) : VM Unit := do
  -- Always fits 257-bit in practice for our uses.
  VM.push (.int (.num n))

def VmState.consumeGas (st : VmState) (amount : Int) : VmState :=
  { st with gas := st.gas.consume amount }

def VmState.throwException (st : VmState) (exc : Int) : VmState :=
  let stack : Stack := #[.int (.num 0), .int (.num exc)]
  { st with
    stack := stack
    cc := st.regs.c2 }

def VmState.ret (st : VmState) : VmState :=
  let old := st.regs.c0
  { st with regs := { st.regs with c0 := .quit 0 }, cc := old }

def VmState.retAlt (st : VmState) : VmState :=
  let old := st.regs.c1
  { st with regs := { st.regs with c1 := .quit 1 }, cc := old }

def VmState.getCtr (st : VmState) (idx : Nat) : Except Excno Value :=
  match idx with
  | 0 => .ok (.cont st.regs.c0)
  | 1 => .ok (.cont st.regs.c1)
  | 2 => .ok (.cont st.regs.c2)
  | 3 => .ok (.cont st.regs.c3)
  | 4 => .ok (.cell st.regs.c4)
  | 5 => .ok (.cell st.regs.c5)
  | 7 => .ok (.tuple st.regs.c7)
  | _ => .error .rangeChk

def VmState.setCtr (st : VmState) (idx : Nat) (v : Value) : Except Excno VmState :=
  match idx, v with
  | 0, .cont k => .ok { st with regs := { st.regs with c0 := k } }
  | 1, .cont k => .ok { st with regs := { st.regs with c1 := k } }
  | 2, .cont k => .ok { st with regs := { st.regs with c2 := k } }
  | 3, .cont k => .ok { st with regs := { st.regs with c3 := k } }
  | 4, .cell c => .ok { st with regs := { st.regs with c4 := c } }
  | 5, .cell c => .ok { st with regs := { st.regs with c5 := c } }
  | 7, .tuple t => .ok { st with regs := { st.regs with c7 := t } }
  | 6, _ => .error .rangeChk
  | _, _ => .error .typeChk

def execInstr (i : Instr) : VM Unit := do
  match i with
  | .nop =>
      pure ()
  | .pushInt n =>
      VM.pushIntQuiet n false
  | .push idx =>
      let v ← VM.fetch idx
      VM.push v
  | .pop idx =>
      -- Mirror the C++ behavior: swap top with s[idx], then pop the top.
      VM.swap 0 idx
      let _ ← VM.pop
      pure ()
  | .xchg0 idx =>
      VM.swap 0 idx
  | .pushCtr idx =>
      let st ← get
      match st.getCtr idx with
      | .ok v => VM.push v
      | .error e => throw e
  | .popCtr idx =>
      let v ← VM.pop
      let st ← get
      match st.setCtr idx v with
      | .ok st' => set st'
      | .error e => throw e
  | .ctos =>
      let c ← VM.popCell
      VM.push (.slice (Slice.ofCell c))
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
  | .setcp cp =>
      if cp = 0 then
        modify fun st => { st with cp := 0 }
      else
        throw .invOpcode
  | .ifret =>
      if (← VM.popBool) then
        modify fun st => st.ret
      else
        pure ()
  | .ifnotret =>
      if !(← VM.popBool) then
        modify fun st => st.ret
      else
        pure ()
  | .inc =>
      let x ← VM.popInt
      VM.pushIntQuiet (x.inc) false
  | .equal =>
      let y ← VM.popInt
      let x ← VM.popInt
      VM.pushIntQuiet (x.equalResult y) false
  | .throwIfNot exc =>
      let flag ← VM.popBool
      if flag then
        pure ()
      else
        modify fun st => (st.throwException exc).consumeGas exceptionGasPrice

inductive StepResult : Type
  | continue (st : VmState)
  | halt (exitCode : Int) (st : VmState)
  deriving Repr

structure TraceEntry where
  step : Nat
  event : String
  cp : Int
  cc_before : String
  cc_after : String
  gas_before : Int
  gas_after : Int
  stack_before : String
  stack_after : String
  deriving Repr

instance : Inhabited TraceEntry where
  default :=
    { step := 0
      event := ""
      cp := 0
      cc_before := ""
      cc_after := ""
      gas_before := 0
      gas_after := 0
      stack_before := ""
      stack_after := "" }

def stackStr (s : Stack) : String :=
  let elems := s.toList.map (fun v => v.pretty)
  "[" ++ String.intercalate ", " elems ++ "]"

def Stack.pretty (s : Stack) : String :=
  stackStr s

def Slice.peekByteHex (s : Slice) : String :=
  if s.haveBits 8 then
    let b := bitsToNat (s.readBits 8)
    let hex := String.mk (Nat.toDigits 16 b)
    let hex := if b < 16 then "0" ++ hex else hex
    s!"0x{hex}"
  else
    "<eof>"

def VmState.ccSummary (cc : Continuation) : String :=
  match cc with
  | .quit n => s!"quit {n}"
  | .excQuit => "excquit"
  | .ordinary code =>
      s!"ord(bitPos={code.bitPos},refPos={code.refPos},bitsRem={code.bitsRemaining},refsRem={code.refsRemaining},next8={code.peekByteHex})"

def VmState.outOfGasHalt (st : VmState) : StepResult :=
  let consumed := st.gas.gasConsumed
  let st' := { st with stack := #[.int (.num consumed)] }
  StepResult.halt Excno.outOfGas.toInt st'

def VmState.step (st : VmState) : StepResult :=
  match st.cc with
  | .quit n =>
      .halt (~~~ n) st
  | .excQuit =>
      let action : VM Int := do
        -- Match `pop_smallint_range(0xffff)` behavior closely enough for MVP.
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res, st') := (action.run st)
      let n : Int :=
        match res with
        | .ok n => n
        | .error e => e.toInt
      .halt (~~~ n) st'
  | .ordinary code =>
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          -- Implicit RET.
          let st0 := st.consumeGas implicitRetGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            st0.outOfGasHalt
          else
            .continue (st0.ret)
        else
          -- Implicit JMPREF to the first reference.
          let st0 := st.consumeGas implicitJmpRefGasPrice
          if decide (st0.gas.gasRemaining < 0) then
            st0.outOfGasHalt
          else
            if code.refPos < code.cell.refs.size then
              let refCell := code.cell.refs[code.refPos]!
              .continue { st0 with cc := .ordinary (Slice.ofCell refCell) }
            else
              let stExc := st0.throwException Excno.cellUnd.toInt
              let stExcGas := stExc.consumeGas exceptionGasPrice
              if decide (stExcGas.gas.gasRemaining < 0) then
                stExcGas.outOfGasHalt
              else
                .continue stExcGas
      else
        let decoded : Except Excno (Instr × Slice) :=
          if st.cp = 0 then
            decodeCp0 code
          else
            .error .invOpcode
        match decoded with
        | .error e =>
            let st0 := st.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              .continue st0
        | .ok (instr, rest) =>
            let st0 := { st with cc := .ordinary rest }
            let stGas := st0.consumeGas (instrGas instr)
            if decide (stGas.gas.gasRemaining < 0) then
              stGas.outOfGasHalt
            else
              let (res, st1) := (execInstr instr).run stGas
              match res with
              | .ok _ =>
                  if decide (st1.gas.gasRemaining < 0) then
                    st1.outOfGasHalt
                  else
                    .continue st1
              | .error e =>
                  -- TVM behavior: convert VM errors into an exception jump to c2.
                  let stExc := st1.throwException e.toInt
                  let stExcGas := stExc.consumeGas exceptionGasPrice
                  if decide (stExcGas.gas.gasRemaining < 0) then
                    stExcGas.outOfGasHalt
                  else
                .continue stExcGas

def VmState.stepTrace (st : VmState) (step : Nat) : TraceEntry × StepResult :=
  let mk (event : String) (stAfter : VmState) (res : StepResult) : TraceEntry × StepResult :=
    ({ step
       event
       cp := st.cp
       cc_before := VmState.ccSummary st.cc
       cc_after := VmState.ccSummary stAfter.cc
       gas_before := st.gas.gasRemaining
       gas_after := stAfter.gas.gasRemaining
       stack_before := stackStr st.stack
       stack_after := stackStr stAfter.stack },
     res)

  match st.cc with
  | .quit n =>
      let res := StepResult.halt (~~~ n) st
      mk s!"quit({n})" st res
  | .excQuit =>
      let action : VM Int := do
        let v ← VM.popInt
        match v with
        | .nan => throw .rangeChk
        | .num n =>
            if n < 0 ∨ n > 0xffff then
              throw .rangeChk
            else
              return n
      let (res0, st') := (action.run st)
      let n : Int :=
        match res0 with
        | .ok n => n
        | .error e => e.toInt
      let res := StepResult.halt (~~~ n) st'
      mk s!"excquit({n})" st' res
  | .ordinary code =>
      if code.bitsRemaining == 0 then
        if code.refsRemaining == 0 then
          let st0 := st.consumeGas implicitRetGasPrice
          let res :=
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              .continue (st0.ret)
          let stAfter :=
            match res with
            | .continue st' => st'
            | .halt _ st' => st'
          mk "implicit_ret" stAfter res
        else
          let st0 := st.consumeGas implicitJmpRefGasPrice
          let res :=
            if decide (st0.gas.gasRemaining < 0) then
              st0.outOfGasHalt
            else
              if code.refPos < code.cell.refs.size then
                let refCell := code.cell.refs[code.refPos]!
                .continue { st0 with cc := .ordinary (Slice.ofCell refCell) }
              else
                let stExc := st0.throwException Excno.cellUnd.toInt
                let stExcGas := stExc.consumeGas exceptionGasPrice
                if decide (stExcGas.gas.gasRemaining < 0) then
                  stExcGas.outOfGasHalt
                else
                  .continue stExcGas
          let stAfter :=
            match res with
            | .continue st' => st'
            | .halt _ st' => st'
          mk "implicit_jmpref" stAfter res
      else
        let decoded : Except Excno (Instr × Slice) :=
          if st.cp = 0 then
            decodeCp0 code
          else
            .error .invOpcode
        match decoded with
        | .error e =>
            let st0 := st.throwException e.toInt
            let st0 := st0.consumeGas exceptionGasPrice
            let res :=
              if decide (st0.gas.gasRemaining < 0) then
                st0.outOfGasHalt
              else
                .continue st0
            let stAfter :=
              match res with
              | .continue st' => st'
              | .halt _ st' => st'
            mk s!"decode_error({e})" stAfter res
        | .ok (instr, rest) =>
            let st0 := { st with cc := .ordinary rest }
            let stGas := st0.consumeGas (instrGas instr)
            let (event, res) :=
              if decide (stGas.gas.gasRemaining < 0) then
                (s!"exec({reprStr instr}) out_of_gas", stGas.outOfGasHalt)
              else
                let (res1, st1) := (execInstr instr).run stGas
                match res1 with
                | .ok _ =>
                    if decide (st1.gas.gasRemaining < 0) then
                      (s!"exec({reprStr instr}) out_of_gas", st1.outOfGasHalt)
                    else
                      (s!"exec({reprStr instr})", .continue st1)
                | .error e =>
                    let stExc := st1.throwException e.toInt
                    let stExcGas := stExc.consumeGas exceptionGasPrice
                    if decide (stExcGas.gas.gasRemaining < 0) then
                      (s!"exec_error({reprStr instr},{reprStr e}) out_of_gas", stExcGas.outOfGasHalt)
                    else
                      (s!"exec_error({reprStr instr},{reprStr e})", .continue stExcGas)
            let stAfter :=
              match res with
              | .continue st' => st'
              | .halt _ st' => st'
            mk event stAfter res

def VmState.tryCommit (st : VmState) : Bool × VmState :=
  -- C++ also checks `level == 0`; our MVP has only ordinary cells (level 0).
  if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
    (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } })
  else
    (false, st)

def VmState.runTrace (fuel : Nat) (st : VmState) (maxTrace : Nat := 200) :
    StepResult × Array TraceEntry × Bool :=
  Id.run do
    let mut stCur := st
    let mut fuelCur := fuel
    let mut step : Nat := 0
    let mut trace : Array TraceEntry := #[]
    let mut pos : Nat := 0
    let mut wrapped : Bool := false
    let mut res : StepResult := .continue stCur

    while fuelCur > 0 do
      let (entry, stepRes) := stCur.stepTrace step
      if maxTrace > 0 then
        if trace.size < maxTrace then
          trace := trace.push entry
        else
          trace := trace.set! pos entry
          pos := (pos + 1) % maxTrace
          wrapped := true

      match stepRes with
      | .continue st' =>
          stCur := st'
          res := .continue st'
          fuelCur := fuelCur - 1
          step := step + 1
      | .halt exitCode st' =>
          res := .halt exitCode st'
          stCur := st'
          fuelCur := 0

    match res with
    | .continue st' =>
        res := .halt (Excno.fatal.toInt) st'
    | .halt _ _ => pure ()

    -- Mirror the C++ commit wrapper shape; precise commit checks come later.
    let res' :=
      match res with
      | .continue st' => .halt (Excno.fatal.toInt) st'
      | .halt exitCode st' =>
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

    let traceOut :=
      if wrapped && trace.size > 0 then
        let n := trace.size
        Array.ofFn (n := n) fun i =>
          let idx := (pos + i.1) % n
          trace[idx]!
      else
        trace

    return (res', traceOut, wrapped)

def VmState.run (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.step with
      | .continue st' => VmState.run fuel st'
      | .halt exitCode st' =>
          -- Mirror the C++ commit wrapper shape; precise commit checks come later.
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

/-! ### Proof scaffolding (Milestone 1, mostly `sorry`) -/

def WF_Int : IntVal → Prop
  | .nan => True
  | .num n =>
      let lo : Int := -((2 : Int) ^ (256 : Nat))
      let hi : Int := (2 : Int) ^ (256 : Nat)
      lo ≤ n ∧ n < hi

def WF_Cell (c : Cell) : Prop :=
  c.bits.size ≤ 1023 ∧ c.refs.size ≤ 4

def WF_Slice (s : Slice) : Prop :=
  WF_Cell s.cell ∧ s.bitPos ≤ s.cell.bits.size ∧ s.refPos ≤ s.cell.refs.size

def WF_Builder (b : Builder) : Prop :=
  b.bits.size ≤ 1023 ∧ b.refs.size ≤ 4

def WF_Tuple (t : Array Value) : Prop :=
  t.size ≤ 255

def WF_Value : Value → Prop
  | .int i => WF_Int i
  | .cell c => WF_Cell c
  | .slice s => WF_Slice s
  | .builder b => WF_Builder b
  | .tuple t => WF_Tuple t
  | .cont _ => True
  | .null => True

def WF_Gas (g : GasLimits) : Prop :=
  g.gasLimit ≤ g.gasMax ∧ g.gasBase = g.gasLimit + g.gasCredit ∧ g.gasRemaining ≤ g.gasBase

def WF_Regs (r : Regs) : Prop :=
  WF_Cell r.c4 ∧ WF_Cell r.c5 ∧ WF_Tuple r.c7

def WF_State (st : VmState) : Prop :=
  (∀ v ∈ st.stack.toList, WF_Value v) ∧ WF_Regs st.regs ∧ WF_Gas st.gas

theorem step_preserves_wf {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem run_preserves_wf {fuel : Nat} {st : VmState} :
    WF_State st →
      match VmState.run fuel st with
      | .continue st' => WF_State st'
      | .halt _ st' => WF_State st' := by
  sorry

theorem step_progress {st : VmState} :
    WF_State st →
      match st.step with
      | .continue _ => True
      | .halt _ _ => True := by
  sorry

theorem step_gas_monotone {st : VmState} :
    WF_State st →
      match st.step with
      | .continue st' => st'.gas.gasRemaining ≤ st.gas.gasRemaining
      | .halt _ st' => st'.gas.gasRemaining ≤ st.gas.gasRemaining := by
  sorry

end TvmLean
