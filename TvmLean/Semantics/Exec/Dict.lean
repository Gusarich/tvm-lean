import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Dict.Stdict
import TvmLean.Semantics.Exec.Dict.Skipdict
import TvmLean.Semantics.Exec.Dict.DictPushConst
import TvmLean.Semantics.Exec.Dict.DictGet
import TvmLean.Semantics.Exec.Dict.DictGetNear
import TvmLean.Semantics.Exec.Dict.DictGetMinMax
import TvmLean.Semantics.Exec.Dict.DictSet
import TvmLean.Semantics.Exec.Dict.DictSetB
import TvmLean.Semantics.Exec.Dict.DictReplaceB
import TvmLean.Semantics.Exec.Dict.DictGetExec
import TvmLean.Semantics.Exec.Dict.Ext
import TvmLean.Semantics.Exec.Dict.Lddict

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDict (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrDictStdict i <|
  execInstrDictSkipdict i <|
  execInstrDictDictPushConst i <|
  execInstrDictDictGet i <|
  execInstrDictDictGetNear i <|
  execInstrDictDictGetMinMax i <|
  execInstrDictDictSet i <|
  execInstrDictDictSetB i <|
  execInstrDictDictReplaceB i <|
  execInstrDictDictGetExec i <|
  execInstrDictExt i <|
  execInstrDictLddict i <|
    next

end TvmLean
