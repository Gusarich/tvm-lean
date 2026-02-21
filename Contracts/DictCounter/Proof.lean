import TvmLean.Proof
import Contracts.DictCounter.Program
import Contracts.DictCounter.Spec

namespace Contracts.DictCounter.Proof

open TvmLean
open Contracts.DictCounter.Program
open Contracts.DictCounter.Spec

section Toolkit

theorem postLookup_of_eq (res : Except Excno (Option Slice))
    (h : res = .ok none) : PostLookup res := by
  simpa [PostLookup] using h

theorem postDelete_of_eq (res : Except Excno (Option Slice × SpecState × Nat × Array Cell))
    (h : res = .ok (none, init, 0, #[])) : PostDelete res := by
  simpa [PostDelete] using h

theorem postSeeded_of_root_some (st : SpecState)
    (h : st.dictRoot.isSome = true) : PostSeeded st := by
  simpa [PostSeeded] using h

theorem postLookupHit_of_lookupHit (res : Except Excno (Option Slice))
    (h : lookupHit res = true) : PostLookupHit res := by
  simpa [PostLookupHit] using h

theorem postDeleteHit_of_deleteHit (res : Except Excno (Option Slice × SpecState × Nat × Array Cell))
    (h : deleteHit res = true) : PostDeleteHit res := by
  simpa [PostDeleteHit] using h

theorem postDeleteClearsRoot_of_deleteClearsRoot
    (res : Except Excno (Option Slice × SpecState × Nat × Array Cell))
    (h : deleteClearsRoot res = true) : PostDeleteClearsRoot res := by
  simpa [PostDeleteClearsRoot] using h

theorem postSetThenLookupHit_of_flag
    (res : Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell))
    (h : setThenLookupHit res = true) : PostSetThenLookupHit res := by
  simpa [PostSetThenLookupHit] using h

theorem postSetThenLookupMiss_of_flag
    (res : Except Excno (Bool × Option Slice × SpecState × Nat × Array Cell))
    (h : setThenLookupMiss res = true) : PostSetThenLookupMiss res := by
  simpa [PostSetThenLookupMiss] using h

end Toolkit

theorem lookup_empty_none (n : Nat) :
    lookupCounter init n = .ok none := by
  simp [lookupCounter, init, lookup, keyFromNat]

theorem lookup_with_trace_empty_none (n : Nat) :
    lookupWithTrace none (keyFromNat n) = .ok (none, #[]) := by
  simp [lookupWithTrace]

theorem nearest_empty_none (n : Nat) :
    nearestWithTrace none (keyFromNat n) = .ok (none, #[]) := by
  simp [nearestWithTrace]

theorem min_empty_none :
    minWithTrace none = .ok (none, #[]) := by
  simp [minWithTrace, keyBits]

theorem delete_empty_none (n : Nat) :
    deleteCounter init n = .ok (none, init, 0, #[]) := by
  unfold deleteCounter init deleteWithTrace keyFromNat
  rfl

theorem lookup_empty_post (n : Nat) : PostLookup (lookupCounter init n) := by
  exact postLookup_of_eq _ (lookup_empty_none n)

theorem delete_empty_post (n : Nat) : PostDelete (deleteCounter init n) := by
  exact postDelete_of_eq _ (delete_empty_none n)

theorem seeded_post : PostSeeded seeded := by
  exact postSeeded_of_root_some _ (by native_decide)

theorem lookup_seeded_hit : PostLookupHit (lookupCounter seeded 0) := by
  exact postLookupHit_of_lookupHit _ (by native_decide)

theorem delete_seeded_hit : PostDeleteHit (deleteCounter seeded 0) := by
  exact postDeleteHit_of_deleteHit _ (by native_decide)

theorem delete_seeded_clears_root : PostDeleteClearsRoot (deleteCounter seeded 0) := by
  exact postDeleteClearsRoot_of_deleteClearsRoot _ (by native_decide)

theorem seeded_update_then_lookup_hit :
    PostSetThenLookupHit (seededSetThenLookup 0 0) := by
  exact postSetThenLookupHit_of_flag _ (by native_decide)

theorem seeded_update_preserves_other_key_miss :
    PostSetThenLookupMiss (seededSetThenLookup 0 1) := by
  exact postSetThenLookupMiss_of_flag _ (by native_decide)

end Contracts.DictCounter.Proof
