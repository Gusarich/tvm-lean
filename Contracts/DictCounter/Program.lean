import TvmLean.Model.Cell.Primitives

namespace Contracts.DictCounter.Program

open TvmLean

def keyBits : Nat := 32

def keyFromNat (n : Nat) : BitString :=
  natToBits n keyBits

def lookup (root : Option Cell) (k : BitString) : Except Excno (Option Slice) :=
  dictLookup root k

def lookupWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option Slice × Array Cell) :=
  dictLookupWithCells root k

def nearestWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option (Slice × BitString) × Array Cell) :=
  dictNearestWithCells root k true false false

def minWithTrace (root : Option Cell) :
    Except Excno (Option (Slice × BitString) × Array Cell) :=
  dictMinMaxWithCells root keyBits false false

def deleteWithTrace (root : Option Cell) (k : BitString) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) :=
  dictDeleteWithCells root k

end Contracts.DictCounter.Program
