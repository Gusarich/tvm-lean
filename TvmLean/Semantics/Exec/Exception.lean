import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Exception.Throw
import TvmLean.Semantics.Exec.Exception.ThrowIf
import TvmLean.Semantics.Exec.Exception.ThrowIfNot
import TvmLean.Semantics.Exec.Exception.ThrowArg
import TvmLean.Semantics.Exec.Exception.ThrowArgIf
import TvmLean.Semantics.Exec.Exception.ThrowArgIfNot
import TvmLean.Semantics.Exec.Exception.ThrowAny
import TvmLean.Semantics.Exec.Exception.Try

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrException (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
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
