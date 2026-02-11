import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlowCallDict (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .callDict idx =>
      -- C++ handlers mask immediate args before pushing:
      --   short: args &= 0xff
      --   long : args &= 0x3fff
      -- Our decoded/assembled CALLDICT domain is already <= 0x3fff; masking keeps
      -- direct raw `.callDict` execution consistent with handler behavior.
      let idx' : Nat := idx &&& 0x3fff
      VM.pushSmallInt (Int.ofNat idx')
      let st ← get
      VM.call st.regs.c3
  | _ => next

end TvmLean
