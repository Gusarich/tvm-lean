import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrContPopCtr (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .popCtr idx =>
      let v ← VM.pop
      let st ← get
      match st.setCtr idx v with
      | .ok st' => set st'
      -- C++ `exec_pop_ctr` wraps `st->set(...)` with `throw_typechk(...)`,
      -- so any failure (bad type or invalid index if invoked directly) is `typeChk`.
      | .error _ => throw .typeChk
  | _ => next

end TvmLean
