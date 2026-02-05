import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Cont.PushCtr
import TvmLean.Core.Exec.Cont.PopCtr
import TvmLean.Core.Exec.Cont.SetContCtr
import TvmLean.Core.Exec.Cont.SetContArgs
import TvmLean.Core.Exec.Cont.SetContVarArgs
import TvmLean.Core.Exec.Cont.SetNumVarArgs
import TvmLean.Core.Exec.Cont.ReturnArgs
import TvmLean.Core.Exec.Cont.Bless
import TvmLean.Core.Exec.Cont.SaveCtr
import TvmLean.Core.Exec.Cont.SameAlt
import TvmLean.Core.Exec.Cont.SameAltSave
import TvmLean.Core.Exec.Cont.BoolAnd
import TvmLean.Core.Exec.Cont.BoolOr
import TvmLean.Core.Exec.Cont.ComposBoth
import TvmLean.Core.Exec.Cont.CondSel
import TvmLean.Core.Exec.Cont.AtExit
import TvmLean.Core.Exec.Cont.ChangeExt

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCont (i : Instr) (next : VM Unit) : VM Unit :=
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
