import TvmLean.Model.Error.Excno
import TvmLean.Model.Instr.Id

namespace TvmLean

/--
Structured VM error surface used by validation/reporting layers.

The executable VM core still throws `Excno` directly; `VmError` provides an explicit
slot for instruction-level unimplemented status and can be bridged from/to `Excno`.
-/
inductive VmError where
  | excno (e : Excno)
  | unimplemented (id : InstrId) (msg : String := "not yet implemented")
  deriving Repr, Inhabited, DecidableEq, BEq

def VmError.toExcno : VmError → Excno
  | .excno e => e
  | .unimplemented _ _ => .unknown

def Excno.toVmError (e : Excno) : VmError :=
  .excno e

instance : ToString VmError where
  toString
    | .excno e => toString e
    | .unimplemented id msg => s!"unimplemented({id.name}): {msg}"

end TvmLean
