import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Flow.Setcp
import TvmLean.Core.Exec.Flow.Ifret
import TvmLean.Core.Exec.Flow.Ifnotret
import TvmLean.Core.Exec.Flow.IfretAlt
import TvmLean.Core.Exec.Flow.If
import TvmLean.Core.Exec.Flow.Ifnot
import TvmLean.Core.Exec.Flow.PushSliceConst
import TvmLean.Core.Exec.Flow.PushCont
import TvmLean.Core.Exec.Flow.PushRef
import TvmLean.Core.Exec.Flow.PushRefSlice
import TvmLean.Core.Exec.Flow.PushRefCont
import TvmLean.Core.Exec.Flow.Execute
import TvmLean.Core.Exec.Flow.Jmpx
import TvmLean.Core.Exec.Flow.CallxArgs
import TvmLean.Core.Exec.Flow.JmpxArgs
import TvmLean.Core.Exec.Flow.Callcc
import TvmLean.Core.Exec.Flow.CallxVarArgs
import TvmLean.Core.Exec.Flow.Ret
import TvmLean.Core.Exec.Flow.RetAlt
import TvmLean.Core.Exec.Flow.RetBool
import TvmLean.Core.Exec.Flow.RetArgs
import TvmLean.Core.Exec.Flow.RetVarArgs
import TvmLean.Core.Exec.Flow.RetData
import TvmLean.Core.Exec.Flow.JmpxVarArgs
import TvmLean.Core.Exec.Flow.JmpxData
import TvmLean.Core.Exec.Flow.Runvm
import TvmLean.Core.Exec.Flow.Ifjmp
import TvmLean.Core.Exec.Flow.Ifnotjmp
import TvmLean.Core.Exec.Flow.Ifelse
import TvmLean.Core.Exec.Flow.Ifref
import TvmLean.Core.Exec.Flow.Ifnotref
import TvmLean.Core.Exec.Flow.Ifjmpref
import TvmLean.Core.Exec.Flow.Ifnotjmpref
import TvmLean.Core.Exec.Flow.IfrefElse
import TvmLean.Core.Exec.Flow.IfelseRef
import TvmLean.Core.Exec.Flow.IfrefElseRef
import TvmLean.Core.Exec.Flow.IfBitJmp
import TvmLean.Core.Exec.Flow.CallRef
import TvmLean.Core.Exec.Flow.JmpRef
import TvmLean.Core.Exec.Flow.CallDict
import TvmLean.Core.Exec.Flow.PrepareDict
import TvmLean.Core.Exec.Flow.Until
import TvmLean.Core.Exec.Flow.While
import TvmLean.Core.Exec.Flow.LoopExt
import TvmLean.Core.Exec.Flow.Blkdrop2
import TvmLean.Core.Exec.Flow.Blkdrop
import TvmLean.Core.Exec.Flow.Drop2

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlow (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrFlowSetcp i <|
  execInstrFlowIfret i <|
  execInstrFlowIfnotret i <|
  execInstrFlowIfretAlt i <|
  execInstrFlowIf i <|
  execInstrFlowIfnot i <|
  execInstrFlowPushSliceConst i <|
  execInstrFlowPushCont i <|
  execInstrFlowPushRef i <|
  execInstrFlowPushRefSlice i <|
  execInstrFlowPushRefCont i <|
  execInstrFlowExecute i <|
  execInstrFlowJmpx i <|
  execInstrFlowCallxArgs i <|
  execInstrFlowJmpxArgs i <|
  execInstrFlowCallcc i <|
  execInstrFlowCallxVarArgs i <|
  execInstrFlowRet i <|
  execInstrFlowRetAlt i <|
  execInstrFlowRetBool i <|
  execInstrFlowRetArgs i <|
  execInstrFlowRetVarArgs i <|
  execInstrFlowRetData i <|
  execInstrFlowJmpxVarArgs i <|
  execInstrFlowJmpxData i <|
  execInstrFlowRunvm i <|
  execInstrFlowIfjmp i <|
  execInstrFlowIfnotjmp i <|
  execInstrFlowIfelse i <|
  execInstrFlowIfref i <|
  execInstrFlowIfnotref i <|
  execInstrFlowIfjmpref i <|
  execInstrFlowIfnotjmpref i <|
  execInstrFlowIfrefElse i <|
  execInstrFlowIfelseRef i <|
  execInstrFlowIfrefElseRef i <|
  execInstrFlowIfBitJmp i <|
  execInstrFlowCallRef i <|
  execInstrFlowJmpRef i <|
  execInstrFlowCallDict i <|
  execInstrFlowPrepareDict i <|
  execInstrFlowUntil i <|
  execInstrFlowWhile i <|
  execInstrFlowLoopExt i <|
  execInstrFlowBlkdrop2 i <|
  execInstrFlowBlkdrop i <|
  execInstrFlowDrop2 i <|
    next

end TvmLean
