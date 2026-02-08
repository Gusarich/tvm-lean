import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Flow.Setcp
import TvmLean.Semantics.Exec.Flow.Ifret
import TvmLean.Semantics.Exec.Flow.Ifnotret
import TvmLean.Semantics.Exec.Flow.IfretAlt
import TvmLean.Semantics.Exec.Flow.If
import TvmLean.Semantics.Exec.Flow.Ifnot
import TvmLean.Semantics.Exec.Flow.PushSliceConst
import TvmLean.Semantics.Exec.Flow.PushCont
import TvmLean.Semantics.Exec.Flow.PushRef
import TvmLean.Semantics.Exec.Flow.PushRefSlice
import TvmLean.Semantics.Exec.Flow.PushRefCont
import TvmLean.Semantics.Exec.Flow.Execute
import TvmLean.Semantics.Exec.Flow.Jmpx
import TvmLean.Semantics.Exec.Flow.CallxArgs
import TvmLean.Semantics.Exec.Flow.JmpxArgs
import TvmLean.Semantics.Exec.Flow.Callcc
import TvmLean.Semantics.Exec.Flow.CallxVarArgs
import TvmLean.Semantics.Exec.Flow.Ret
import TvmLean.Semantics.Exec.Flow.RetAlt
import TvmLean.Semantics.Exec.Flow.RetBool
import TvmLean.Semantics.Exec.Flow.RetArgs
import TvmLean.Semantics.Exec.Flow.RetVarArgs
import TvmLean.Semantics.Exec.Flow.RetData
import TvmLean.Semantics.Exec.Flow.JmpxVarArgs
import TvmLean.Semantics.Exec.Flow.JmpxData
import TvmLean.Semantics.Exec.Flow.Runvm
import TvmLean.Semantics.Exec.Flow.Ifjmp
import TvmLean.Semantics.Exec.Flow.Ifnotjmp
import TvmLean.Semantics.Exec.Flow.Ifelse
import TvmLean.Semantics.Exec.Flow.Ifref
import TvmLean.Semantics.Exec.Flow.Ifnotref
import TvmLean.Semantics.Exec.Flow.Ifjmpref
import TvmLean.Semantics.Exec.Flow.Ifnotjmpref
import TvmLean.Semantics.Exec.Flow.IfrefElse
import TvmLean.Semantics.Exec.Flow.IfelseRef
import TvmLean.Semantics.Exec.Flow.IfrefElseRef
import TvmLean.Semantics.Exec.Flow.IfBitJmp
import TvmLean.Semantics.Exec.Flow.CallRef
import TvmLean.Semantics.Exec.Flow.JmpRef
import TvmLean.Semantics.Exec.Flow.CallDict
import TvmLean.Semantics.Exec.Flow.PrepareDict
import TvmLean.Semantics.Exec.Flow.Until
import TvmLean.Semantics.Exec.Flow.While
import TvmLean.Semantics.Exec.Flow.LoopExt
import TvmLean.Semantics.Exec.Flow.Blkdrop2
import TvmLean.Semantics.Exec.Flow.Blkdrop
import TvmLean.Semantics.Exec.Flow.Drop2

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrFlow (host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
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
  execInstrFlowRunvm host i <|
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
