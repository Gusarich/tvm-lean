import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Cont.PushCtr
import TvmLean.Semantics.Exec.Cont.PopCtr
import TvmLean.Semantics.Exec.Cont.SetContCtr
import TvmLean.Semantics.Exec.Cont.SetContArgs
import TvmLean.Semantics.Exec.Cont.SetContVarArgs
import TvmLean.Semantics.Exec.Cont.SetNumVarArgs
import TvmLean.Semantics.Exec.Cont.ReturnArgs
import TvmLean.Semantics.Exec.Cont.Bless
import TvmLean.Semantics.Exec.Cont.SaveCtr
import TvmLean.Semantics.Exec.Cont.SameAlt
import TvmLean.Semantics.Exec.Cont.SameAltSave
import TvmLean.Semantics.Exec.Cont.BoolAnd
import TvmLean.Semantics.Exec.Cont.BoolOr
import TvmLean.Semantics.Exec.Cont.ComposBoth
import TvmLean.Semantics.Exec.Cont.CondSel
import TvmLean.Semantics.Exec.Cont.AtExit
import TvmLean.Semantics.Exec.Cont.ChangeExt

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCont (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrContPushCtr i <|
  execInstrContPopCtr i <|
  execInstrContSetContCtr i <|
  execInstrContSetContArgs i <|
  execInstrContSetContVarArgs i <|
  execInstrContSetNumVarArgs i <|
  execInstrContReturnArgs i <|
  execInstrContBless i <|
  execInstrContSaveCtr i <|
  execInstrContChangeExt i <|
  execInstrContSameAlt i <|
  execInstrContSameAltSave i <|
  execInstrContBoolAnd i <|
  execInstrContBoolOr i <|
  execInstrContComposBoth i <|
  execInstrContCondSel i <|
  execInstrContAtExit i <|
    next

end TvmLean
