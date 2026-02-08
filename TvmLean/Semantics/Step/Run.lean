import TvmLean.Semantics.Step.Step

namespace TvmLean

def VmState.tryCommit (st : VmState) : Bool × VmState :=
  -- C++ also checks `level == 0`; our MVP has only ordinary cells (level 0).
  if st.regs.c4.depthLe st.maxDataDepth && st.regs.c5.depthLe st.maxDataDepth then
    (true, { st with cstate := { c4 := st.regs.c4, c5 := st.regs.c5, committed := true } })
  else
    (false, st)

def VmState.run (host : Host) (fuel : Nat) (st : VmState) : StepResult :=
  match fuel with
  | 0 => .halt (Excno.fatal.toInt) st
  | fuel + 1 =>
      match st.step host with
      | .continue st' => VmState.run host fuel st'
      | .halt exitCode st' =>
          -- Mirror the C++ commit wrapper shape; precise commit checks come later.
          if exitCode = -1 ∨ exitCode = -2 then
            let (ok, st'') := st'.tryCommit
            if ok then
              .halt exitCode st''
            else
              -- C++: clear stack, push 0, return ~cell_ov on commit failure.
              let stFail := { st'' with stack := #[.int (.num 0)] }
              .halt (~~~ Excno.cellOv.toInt) stFail
          else
            .halt exitCode st'

end TvmLean
