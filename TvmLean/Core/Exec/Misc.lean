import TvmLean.Core.Exec.Common

namespace TvmLean

open Std

structure DataSizeAcc where
  visited : HashSet ByteArray
  cells : Nat
  bits : Nat
  refs : Nat

def DataSizeAcc.empty : DataSizeAcc :=
  { visited := {}
    cells := 0
    bits := 0
    refs := 0 }

partial def DataSizeAcc.visitCell (limit : Nat) (c : Cell) (acc : DataSizeAcc) : Except Excno DataSizeAcc := do
  let h : ByteArray := ByteArray.mk (Cell.hashBytes c)
  if acc.visited.contains h then
    return acc
  if acc.cells ≥ limit then
    throw .cellOv
  let acc :=
    { visited := acc.visited.insert h
      cells := acc.cells + 1
      bits := acc.bits + c.bits.size
      refs := acc.refs + c.refs.size }
  let mut acc := acc
  for r in c.refs do
    acc ← DataSizeAcc.visitCell limit r acc
  return acc

def VM.execCdataSize (quiet : Bool) : VM Unit := do
  let n ← VM.popIntFinite
  if n < 0 then
    throw .rangeChk
  let limit : Nat := n.toNat
  let c? ← VM.popMaybeCell
  let out : Except Excno (Nat × Nat × Nat) :=
    match c? with
    | none => .ok (0, 0, 0)
    | some c =>
        match (DataSizeAcc.visitCell limit c DataSizeAcc.empty) with
        | .ok acc => .ok (acc.cells, acc.bits, acc.refs)
        | .error e => .error e
  match out with
  | .ok (x, y, z) =>
      VM.pushSmallInt (Int.ofNat x)
      VM.pushSmallInt (Int.ofNat y)
      VM.pushSmallInt (Int.ofNat z)
      if quiet then
        VM.pushSmallInt (-1)
  | .error .cellOv =>
      if quiet then
        VM.pushSmallInt 0
      else
        throw .cellOv
  | .error e =>
      throw e

def VM.execSdataSize (quiet : Bool) : VM Unit := do
  let n ← VM.popIntFinite
  if n < 0 then
    throw .rangeChk
  let limit : Nat := n.toNat
  let s ← VM.popSlice
  let mut acc : DataSizeAcc :=
    { DataSizeAcc.empty with bits := s.bitsRemaining, refs := s.refsRemaining }
  let mut ok : Bool := true
  for i in [s.refPos:s.cell.refs.size] do
    let c := s.cell.refs[i]!
    match (DataSizeAcc.visitCell limit c acc) with
    | .ok acc' => acc := acc'
    | .error .cellOv =>
        ok := false
        break
    | .error e => throw e

  if ok then
    VM.pushSmallInt (Int.ofNat acc.cells)
    VM.pushSmallInt (Int.ofNat acc.bits)
    VM.pushSmallInt (Int.ofNat acc.refs)
    if quiet then
      VM.pushSmallInt (-1)
  else
    if quiet then
      VM.pushSmallInt 0
    else
      throw .cellOv

set_option maxHeartbeats 1000000 in
def execInstrMisc (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellExt (.cdataSize quiet) => VM.execCdataSize quiet
  | .cellExt (.sdataSize quiet) => VM.execSdataSize quiet
  | _ => next

end TvmLean
