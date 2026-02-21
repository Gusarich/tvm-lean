import TvmLean.Model.Cell.Primitives

namespace TvmLean

@[simp] theorem dictLookup_none (key : BitString) :
    dictLookup none key = .ok none := by
  rfl

@[simp] theorem dictLookup_some (cell : Cell) (key : BitString) :
    dictLookup (some cell) key = dictLookupAux cell key 0 key.size := by
  rfl

@[simp] theorem dictLookupWithCells_none (key : BitString) :
    dictLookupWithCells none key = .ok (none, #[]) := by
  rfl

@[simp] theorem dictLookupWithCells_some (cell : Cell) (key : BitString) :
    dictLookupWithCells (some cell) key = dictLookupAuxWithCells cell key 0 key.size := by
  rfl

@[simp] theorem dictLookupVisitedCells_none (key : BitString) :
    dictLookupVisitedCells none key = #[] := by
  simp [dictLookupVisitedCells]

@[simp] theorem dictLookupVisitedCells_some (cell : Cell) (key : BitString) :
    dictLookupVisitedCells (some cell) key = dictLookupVisitedCellsAux cell key 0 key.size := by
  rfl

@[simp] theorem dictMinMaxVisitedCells_none (n : Nat) (fetchMax invertFirst : Bool) :
    dictMinMaxVisitedCells none n fetchMax invertFirst = #[] := by
  simp [dictMinMaxVisitedCells]

@[simp] theorem dictMinMaxVisitedCells_some (cell : Cell) (n : Nat) (fetchMax invertFirst : Bool) :
    dictMinMaxVisitedCells (some cell) n fetchMax invertFirst =
      dictMinMaxVisitedCellsAux cell n 0 (fetchMax != invertFirst) fetchMax := by
  rfl

@[simp] theorem dictDeleteVisitedCells_none (key : BitString) :
    dictDeleteVisitedCells none key = #[] := by
  simp [dictDeleteVisitedCells]

@[simp] theorem dictNearestVisitedCells_none (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    dictNearestVisitedCells none hint fetchNext allowEq invertFirst = #[] := by
  simp [dictNearestVisitedCells]

@[simp] theorem dictMinMaxWithCells_none (n : Nat) (fetchMax invertFirst : Bool) :
    dictMinMaxWithCells none n fetchMax invertFirst = .ok (none, #[]) := by
  rfl

@[simp] theorem dictMinMaxWithCells_some (cell : Cell) (n : Nat) (fetchMax invertFirst : Bool) :
    dictMinMaxWithCells (some cell) n fetchMax invertFirst = do
      let restBit : Bool := fetchMax
      let firstBit : Bool := restBit != invertFirst
      let (val, keyBits, loaded) ← dictMinMaxAuxWithCells cell n 0 firstBit restBit
      return (some (val, keyBits), loaded) := by
  rfl

@[simp] theorem dictNearestWithCells_none (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    dictNearestWithCells none hint fetchNext allowEq invertFirst = .ok (none, #[]) := by
  rfl

@[simp] theorem dictNearestWithCells_some (cell : Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool) :
    dictNearestWithCells (some cell) hint fetchNext allowEq invertFirst =
      dictNearestAuxWithCells cell hint hint.size 0 allowEq (fetchNext != invertFirst) fetchNext := by
  rfl

@[simp] theorem dictDeleteWithCells_none (key : BitString) :
    dictDeleteWithCells none key = .ok (none, none, 0, #[]) := by
  rfl

@[simp] theorem dictDeleteWithCells_some (cell : Cell) (key : BitString) :
    dictDeleteWithCells (some cell) key = dictDeleteAuxWithCells cell key 0 key.size := by
  rfl

@[simp] theorem dictLookupWithCells_none_ok_iff_trace_shape (key : BitString)
    (res : Option Slice) (loaded : Array Cell) :
    dictLookupWithCells none key = .ok (res, loaded) ↔
      (res, loaded) = (none, #[]) := by
  constructor
  · intro h
    simpa using h.symm
  · intro hpair
    cases hpair
    simp

@[simp] theorem dictLookupWithCells_some_ok_iff_aux_shape (cell : Cell) (key : BitString)
    (res : Option Slice) (loaded : Array Cell) :
    dictLookupWithCells (some cell) key = .ok (res, loaded) ↔
      dictLookupAuxWithCells cell key 0 key.size = .ok (res, loaded) := by
  rfl

@[simp] theorem dictDeleteWithCells_none_ok_iff_trace_shape (key : BitString)
    (oldVal : Option Slice) (root' : Option Cell) (created : Nat) (loaded : Array Cell) :
    dictDeleteWithCells none key = .ok (oldVal, root', created, loaded) ↔
      (oldVal, root', created, loaded) = (none, none, 0, #[]) := by
  constructor
  · intro h
    simpa using h.symm
  · intro hshape
    cases hshape
    simp

@[simp] theorem dictDeleteWithCells_some_ok_iff_aux_shape (cell : Cell) (key : BitString)
    (oldVal : Option Slice) (root' : Option Cell) (created : Nat) (loaded : Array Cell) :
    dictDeleteWithCells (some cell) key = .ok (oldVal, root', created, loaded) ↔
      dictDeleteAuxWithCells cell key 0 key.size = .ok (oldVal, root', created, loaded) := by
  rfl

@[simp] theorem dictNearestWithCells_none_ok_iff_trace_shape (hint : BitString)
    (fetchNext allowEq invertFirst : Bool) (res : Option (Slice × BitString)) (loaded : Array Cell) :
    dictNearestWithCells none hint fetchNext allowEq invertFirst = .ok (res, loaded) ↔
      (res, loaded) = (none, #[]) := by
  constructor
  · intro h
    simpa using h.symm
  · intro hpair
    cases hpair
    simp

@[simp] theorem dictNearestWithCells_some_ok_iff_aux_shape (cell : Cell) (hint : BitString)
    (fetchNext allowEq invertFirst : Bool) (res : Option (Slice × BitString)) (loaded : Array Cell) :
    dictNearestWithCells (some cell) hint fetchNext allowEq invertFirst = .ok (res, loaded) ↔
      dictNearestAuxWithCells cell hint hint.size 0 allowEq (fetchNext != invertFirst) fetchNext =
        .ok (res, loaded) := by
  rfl

@[simp] theorem dictMinMaxWithCells_none_ok_iff_trace_shape (n : Nat) (fetchMax invertFirst : Bool)
    (res : Option (Slice × BitString)) (loaded : Array Cell) :
    dictMinMaxWithCells none n fetchMax invertFirst = .ok (res, loaded) ↔
      (res, loaded) = (none, #[]) := by
  constructor
  · intro h
    simpa using h.symm
  · intro hpair
    cases hpair
    simp

theorem dictMinMaxWithCells_some_ok_of_aux_shape (cell : Cell) (n : Nat)
    (fetchMax invertFirst : Bool) (val : Slice) (keyBits : BitString) (loaded : Array Cell)
    (haux : dictMinMaxAuxWithCells cell n 0 (fetchMax != invertFirst) fetchMax = .ok (val, keyBits, loaded)) :
    dictMinMaxWithCells (some cell) n fetchMax invertFirst = .ok (some (val, keyBits), loaded) := by
  simp [dictMinMaxWithCells, haux]
  rfl

theorem dictMinMaxWithCells_some_error_of_aux_shape (cell : Cell) (n : Nat)
    (fetchMax invertFirst : Bool) (e : Excno)
    (haux : dictMinMaxAuxWithCells cell n 0 (fetchMax != invertFirst) fetchMax = .error e) :
    dictMinMaxWithCells (some cell) n fetchMax invertFirst = .error e := by
  simp [dictMinMaxWithCells, haux]
  rfl

@[simp] theorem dictKeyBits_none_of_zero_width_nonzero_index (idx : Int) (unsigned : Bool)
    (hidx : idx ≠ 0) :
    dictKeyBits? idx 0 unsigned = none := by
  simp [dictKeyBits?, hidx]

theorem dictLookupWithCells_error_dictErr_of_aux_malformed_shape
    (cell : Cell) (key : BitString)
    (haux : dictLookupAuxWithCells cell key 0 key.size = .error .dictErr) :
    dictLookupWithCells (some cell) key = .error .dictErr := by
  simpa using haux

@[simp] theorem dictSetRefWithCells_shape (root : Option Cell) (key : BitString)
    (valRef : Cell) (mode : DictSetMode) :
    dictSetRefWithCells root key valRef mode =
      dictSetGenAuxWithCells root key (fun b => builderStoreRefChecked b valRef) mode := by
  rfl

@[simp] theorem dictSetRefWithCells_some_shape (cell : Cell) (key : BitString)
    (valRef : Cell) (mode : DictSetMode) :
    dictSetRefWithCells (some cell) key valRef mode =
      dictSetGenAuxWithCells (some cell) key (fun b => builderStoreRefChecked b valRef) mode := by
  rfl

@[simp] theorem dictSetSliceWithCells_shape (root : Option Cell) (key : BitString)
    (val : Slice) (mode : DictSetMode) :
    dictSetSliceWithCells root key val mode =
      dictSetGenAuxWithCells root key (fun b => builderAppendCellChecked b val.toCellRemaining) mode := by
  rfl

@[simp] theorem dictSetSliceWithCells_some_shape (cell : Cell) (key : BitString)
    (val : Slice) (mode : DictSetMode) :
    dictSetSliceWithCells (some cell) key val mode =
      dictSetGenAuxWithCells (some cell) key (fun b => builderAppendCellChecked b val.toCellRemaining) mode := by
  rfl

@[simp] theorem dictSetBuilderWithCells_shape (root : Option Cell) (key : BitString)
    (val : Builder) (mode : DictSetMode) :
    dictSetBuilderWithCells root key val mode =
      dictSetGenAuxWithCells root key (fun b => builderAppendBuilderChecked b val) mode := by
  rfl

@[simp] theorem dictSetBuilderWithCells_some_shape (cell : Cell) (key : BitString)
    (val : Builder) (mode : DictSetMode) :
    dictSetBuilderWithCells (some cell) key val mode =
      dictSetGenAuxWithCells (some cell) key (fun b => builderAppendBuilderChecked b val) mode := by
  rfl

@[simp] theorem dictLookupSetRefWithCells_shape (root : Option Cell) (key : BitString)
    (valRef : Cell) (mode : DictSetMode) :
    dictLookupSetRefWithCells root key valRef mode =
      dictLookupSetGenAuxWithCells root key (fun b => builderStoreRefChecked b valRef) mode := by
  rfl

@[simp] theorem dictLookupSetRefWithCells_some_shape (cell : Cell) (key : BitString)
    (valRef : Cell) (mode : DictSetMode) :
    dictLookupSetRefWithCells (some cell) key valRef mode =
      dictLookupSetGenAuxWithCells (some cell) key (fun b => builderStoreRefChecked b valRef) mode := by
  rfl

@[simp] theorem dictLookupSetSliceWithCells_shape (root : Option Cell) (key : BitString)
    (val : Slice) (mode : DictSetMode) :
    dictLookupSetSliceWithCells root key val mode =
      dictLookupSetGenAuxWithCells root key (fun b => builderAppendCellChecked b val.toCellRemaining) mode := by
  rfl

@[simp] theorem dictLookupSetSliceWithCells_some_shape (cell : Cell) (key : BitString)
    (val : Slice) (mode : DictSetMode) :
    dictLookupSetSliceWithCells (some cell) key val mode =
      dictLookupSetGenAuxWithCells (some cell) key (fun b => builderAppendCellChecked b val.toCellRemaining) mode := by
  rfl

@[simp] theorem dictLookupSetBuilderWithCells_shape (root : Option Cell) (key : BitString)
    (val : Builder) (mode : DictSetMode) :
    dictLookupSetBuilderWithCells root key val mode =
      dictLookupSetGenAuxWithCells root key (fun b => builderAppendBuilderChecked b val) mode := by
  rfl

@[simp] theorem dictLookupSetBuilderWithCells_some_shape (cell : Cell) (key : BitString)
    (val : Builder) (mode : DictSetMode) :
    dictLookupSetBuilderWithCells (some cell) key val mode =
      dictLookupSetGenAuxWithCells (some cell) key (fun b => builderAppendBuilderChecked b val) mode := by
  rfl

theorem dictLookup_preserved_of_root_eq (root root' : Option Cell) (key : BitString)
    (hroot : root' = root) :
    dictLookup root' key = dictLookup root key := by
  simp [hroot]

theorem dictLookupWithCells_preserved_of_root_eq (root root' : Option Cell) (key : BitString)
    (hroot : root' = root) :
    dictLookupWithCells root' key = dictLookupWithCells root key := by
  simp [hroot]

theorem dictLookup_unaffected_key_of_root_preserved
    (root root' : Option Cell) (updatedKey lookupKey : BitString)
    (_hkey : lookupKey ≠ updatedKey) (hroot : root' = root) :
    dictLookup root' lookupKey = dictLookup root lookupKey := by
  exact dictLookup_preserved_of_root_eq root root' lookupKey hroot

theorem dictLookupWithCells_unaffected_key_of_root_preserved
    (root root' : Option Cell) (updatedKey lookupKey : BitString)
    (_hkey : lookupKey ≠ updatedKey) (hroot : root' = root) :
    dictLookupWithCells root' lookupKey = dictLookupWithCells root lookupKey := by
  exact dictLookupWithCells_preserved_of_root_eq root root' lookupKey hroot

theorem dictLookup_unaffected_key_of_setSliceWithCells_root_preserved
    (root root' : Option Cell) (setKey lookupKey : BitString) (val : Slice) (mode : DictSetMode)
    (ok : Bool) (created : Nat) (loaded : Array Cell)
    (_hset : dictSetSliceWithCells root setKey val mode = .ok (root', ok, created, loaded))
    (hkey : lookupKey ≠ setKey) (hroot : root' = root) :
    dictLookup root' lookupKey = dictLookup root lookupKey := by
  exact dictLookup_unaffected_key_of_root_preserved root root' setKey lookupKey hkey hroot

theorem dictLookup_unaffected_key_of_deleteWithCells_root_preserved
    (root root' : Option Cell) (deleteKey lookupKey : BitString)
    (oldVal : Option Slice) (created : Nat) (loaded : Array Cell)
    (_hdelete : dictDeleteWithCells root deleteKey = .ok (oldVal, root', created, loaded))
    (hkey : lookupKey ≠ deleteKey) (hroot : root' = root) :
    dictLookup root' lookupKey = dictLookup root lookupKey := by
  exact dictLookup_unaffected_key_of_root_preserved root root' deleteKey lookupKey hkey hroot

end TvmLean
