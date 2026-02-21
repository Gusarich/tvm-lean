import TvmLean.Proof
import Contracts.MsgParser.Program
import Contracts.MsgParser.Spec

namespace Contracts.MsgParser.Proof

open Contracts.MsgParser.Program
open Contracts.MsgParser.Spec

theorem parse_none_extracts_tag0 : PostValidTag initValid := by
  unfold PostValidTag runTagCheck initValid
  native_decide

theorem parse_none_preserves_tail_bits : PostValidTail initValid := by
  unfold PostValidTail runTailCheck initValid
  native_decide

theorem parse_guard_rejects_short_prefix : PostInvalidGuard initInvalid := by
  unfold PostInvalidGuard runGuard initInvalid
  native_decide

end Contracts.MsgParser.Proof
