import TvmLean.Model.State.VmState

namespace TvmLean

abbrev VM := ExceptT Excno (StateM VmState)

end TvmLean
