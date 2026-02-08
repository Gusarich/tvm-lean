import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDebug (_host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .debugOp op =>
      match op with
      | .dumpStk =>
          pure ()
      | .strDump =>
          -- TON `runvmx` treats STRDUMP as a pure debug opcode: never throws, only logs when enabled.
          pure ()
      | .dump idx =>
          -- TON `runvmx` treats DUMP as a pure debug opcode: never throws, only logs when enabled.
          let _ := idx
          pure ()
      | .debug _ =>
          pure ()
      | .debug1 _ =>
          pure ()
      | .debug2 _ =>
          pure ()
      | .debugStr _ =>
          pure ()
      | .extCall _ =>
          -- Not supported by TON `runvmx` (treated as invalid opcode).
          throw .invOpcode
  | _ => next

end TvmLean
