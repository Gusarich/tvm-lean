import TvmLean.Model.Cell.Primitives

namespace TvmLean

@[simp] theorem dictLookup_none (key : BitString) :
    dictLookup none key = .ok none := by
  rfl

@[simp] theorem dictLookupWithCells_none (key : BitString) :
    dictLookupWithCells none key = .ok (none, #[]) := by
  rfl

@[simp] theorem dictLookupVisitedCells_none (key : BitString) :
    dictLookupVisitedCells none key = #[] := by
  simp [dictLookupVisitedCells]

@[simp] theorem dictMinMaxVisitedCells_none (n : Nat) (fetchMax invertFirst : Bool) :
    dictMinMaxVisitedCells none n fetchMax invertFirst = #[] := by
  simp [dictMinMaxVisitedCells]

@[simp] theorem dictDeleteVisitedCells_none (key : BitString) :
    dictDeleteVisitedCells none key = #[] := by
  simp [dictDeleteVisitedCells]

@[simp] theorem dictNearestVisitedCells_none (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    dictNearestVisitedCells none hint fetchNext allowEq invertFirst = #[] := by
  simp [dictNearestVisitedCells]

@[simp] theorem dictMinMaxWithCells_none (n : Nat) (fetchMax invertFirst : Bool) :
    dictMinMaxWithCells none n fetchMax invertFirst = .ok (none, #[]) := by
  rfl

@[simp] theorem dictNearestWithCells_none (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    dictNearestWithCells none hint fetchNext allowEq invertFirst = .ok (none, #[]) := by
  rfl

@[simp] theorem dictDeleteWithCells_none (key : BitString) :
    dictDeleteWithCells none key = .ok (none, none, 0, #[]) := by
  rfl

end TvmLean
