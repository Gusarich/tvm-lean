import TvmLean.Proof
import Contracts.DictCounter.Program
import Contracts.DictCounter.Spec

namespace Contracts.DictCounter.Proof

open TvmLean
open Contracts.DictCounter.Program
open Contracts.DictCounter.Spec

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
  simpa [PostLookup] using lookup_empty_none n

theorem delete_empty_post (n : Nat) : PostDelete (deleteCounter init n) := by
  simpa [PostDelete] using delete_empty_none n

end Contracts.DictCounter.Proof
