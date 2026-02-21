import TvmLean.Proof
import Contracts.NonceGuard.Program
import Contracts.NonceGuard.Spec

namespace Contracts.NonceGuard.Proof

open Contracts.NonceGuard.Spec

abbrev sampleNonce : Nat :=
  7

theorem first_nonce_is_accepted : PostFirstAccept sampleNonce := by
  unfold PostFirstAccept
  native_decide

theorem replay_nonce_is_rejected : PostReplayReject sampleNonce := by
  unfold PostReplayReject
  native_decide

theorem nonce_is_marked_after_first_use : PostMarkedAfterFirstUse sampleNonce := by
  unfold PostMarkedAfterFirstUse
  native_decide

end Contracts.NonceGuard.Proof
