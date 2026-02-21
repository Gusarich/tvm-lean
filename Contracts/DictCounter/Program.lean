import TvmLean.Model.Cell.Primitives

namespace Contracts.DictCounter.Program

open TvmLean

def keyBits : Nat := 32

def keyFromNat (n : Nat) : BitString :=
  natToBits n keyBits

def defaultCounterValue : Slice :=
  Slice.ofCell Cell.empty

def lookup (root : Option Cell) (k : BitString) : Except Excno (Option Slice) :=
  dictLookup root k

def lookupWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option Slice × Array Cell) :=
  dictLookupWithCells root k

def setWithTrace (root : Option Cell) (k : BitString) (v : Slice) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) :=
  dictSetSliceWithCells root k v .set

def setDefaultWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) :=
  setWithTrace root k defaultCounterValue

def nearestWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option (Slice × BitString) × Array Cell) :=
  dictNearestWithCells root k true false false

def minWithTrace (root : Option Cell) :
    Except Excno (Option (Slice × BitString) × Array Cell) :=
  dictMinMaxWithCells root keyBits false false

def deleteWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) :=
  dictDeleteWithCells root k

@[simp] theorem lookup_some_shape (cell : Cell) (k : BitString) :
    lookup (some cell) k = dictLookupAux cell k 0 k.size := by
  rfl

@[simp] theorem lookupWithTrace_some_shape (cell : Cell) (k : BitString) :
    lookupWithTrace (some cell) k = dictLookupAuxWithCells cell k 0 k.size := by
  rfl

@[simp] theorem setWithTrace_some_shape (cell : Cell) (k : BitString) (v : Slice) :
    setWithTrace (some cell) k v =
      dictSetGenAuxWithCells (some cell) k (fun b => builderAppendCellChecked b v.toCellRemaining) .set := by
  rfl

@[simp] theorem setDefaultWithTrace_shape (root : Option Cell) (k : BitString) :
    setDefaultWithTrace root k = setWithTrace root k defaultCounterValue := by
  rfl

@[simp] theorem deleteWithTrace_some_shape (cell : Cell) (k : BitString) :
    deleteWithTrace (some cell) k = dictDeleteAuxWithCells cell k 0 k.size := by
  rfl

end Contracts.DictCounter.Program
