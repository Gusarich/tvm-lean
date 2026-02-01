import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Exception.Throw
import TvmLean.Core.Exec.Exception.ThrowIf
import TvmLean.Core.Exec.Exception.ThrowIfNot
import TvmLean.Core.Exec.Exception.ThrowArg
import TvmLean.Core.Exec.Exception.ThrowArgIf
import TvmLean.Core.Exec.Exception.ThrowArgIfNot
import TvmLean.Core.Exec.Exception.ThrowAny
import TvmLean.Core.Exec.Exception.Try

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrException (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrExceptionThrow i <|
  execInstrExceptionThrowIf i <|
  execInstrExceptionThrowIfNot i <|
  execInstrExceptionThrowArg i <|
  execInstrExceptionThrowArgIf i <|
  execInstrExceptionThrowArgIfNot i <|
  execInstrExceptionThrowAny i <|
  execInstrExceptionTry i <|
    next

end TvmLean
