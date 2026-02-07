import TvmLean.Model.Cell.Cell

namespace TvmLean

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

def Slice.toCellRemaining (s : Slice) : Cell :=
  Cell.mkOrdinary
    (s.cell.bits.extract s.bitPos s.cell.bits.size)
    (s.cell.refs.extract s.refPos s.cell.refs.size)

def Slice.haveBits (s : Slice) (n : Nat) : Bool :=
  decide (s.bitPos + n ≤ s.cell.bits.size)

def Slice.haveRefs (s : Slice) (n : Nat) : Bool :=
  decide (s.refPos + n ≤ s.cell.refs.size)

def Slice.readBits (s : Slice) (n : Nat) : BitString :=
  s.cell.bits.extract s.bitPos (s.bitPos + n)

def Slice.prefetchBytesCellUnd (s : Slice) (bytes : Nat) : Except Excno (Array UInt8) := do
  let bits : Nat := bytes * 8
  if s.haveBits bits then
    return bitStringToBytesBE (s.readBits bits)
  else
    throw .cellUnd

def Slice.advanceBits (s : Slice) (n : Nat) : Slice :=
  { s with bitPos := s.bitPos + n }

def Slice.takeRefCell (s : Slice) : Except Excno (Cell × Slice) := do
  if s.haveRefs 1 then
    let c := s.cell.refs[s.refPos]!
    let s' := { s with refPos := s.refPos + 1 }
    return (c, s')
  else
    throw .cellUnd

instance : BEq Slice := ⟨fun a b => a.bitPos == b.bitPos && a.refPos == b.refPos && a.cell == b.cell⟩

end TvmLean
