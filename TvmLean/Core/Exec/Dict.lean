import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Dict.Stdict
import TvmLean.Core.Exec.Dict.Skipdict
import TvmLean.Core.Exec.Dict.DictPushConst
import TvmLean.Core.Exec.Dict.DictGet
import TvmLean.Core.Exec.Dict.DictGetNear
import TvmLean.Core.Exec.Dict.DictGetMinMax
import TvmLean.Core.Exec.Dict.DictSet
import TvmLean.Core.Exec.Dict.DictSetB
import TvmLean.Core.Exec.Dict.DictReplaceB
import TvmLean.Core.Exec.Dict.DictGetExec
import TvmLean.Core.Exec.Dict.Lddict

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrDict (i : Instr) (next : VM Unit) : VM Unit :=
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
  execInstrDictLddict i <|
    next

end TvmLean
