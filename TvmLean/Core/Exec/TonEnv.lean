import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.TonEnv.Balance
import TvmLean.Core.Exec.TonEnv.Now
import TvmLean.Core.Exec.TonEnv.GetParam
import TvmLean.Core.Exec.TonEnv.GetPrecompiledGas
import TvmLean.Core.Exec.TonEnv.Randu256
import TvmLean.Core.Exec.TonEnv.Rand
import TvmLean.Core.Exec.TonEnv.SetRand
import TvmLean.Core.Exec.TonEnv.GetGlobVar
import TvmLean.Core.Exec.TonEnv.GetGlob
import TvmLean.Core.Exec.TonEnv.SetGlobVar
import TvmLean.Core.Exec.TonEnv.SetGlob
import TvmLean.Core.Exec.TonEnv.Accept
import TvmLean.Core.Exec.TonEnv.SetGasLimit
import TvmLean.Core.Exec.TonEnv.GasConsumed
import TvmLean.Core.Exec.TonEnv.Commit
import TvmLean.Core.Exec.TonEnv.LdGrams
import TvmLean.Core.Exec.TonEnv.StGrams
import TvmLean.Core.Exec.TonEnv.LdMsgAddr
import TvmLean.Core.Exec.TonEnv.RewriteStdAddr
import TvmLean.Core.Exec.TonEnv.GlobalId
import TvmLean.Core.Exec.TonEnv.GetGasFee
import TvmLean.Core.Exec.TonEnv.GetStorageFee
import TvmLean.Core.Exec.TonEnv.GetForwardFee
import TvmLean.Core.Exec.TonEnv.GetOriginalFwdFee
import TvmLean.Core.Exec.TonEnv.GetGasFeeSimple
import TvmLean.Core.Exec.TonEnv.GetForwardFeeSimple
import TvmLean.Core.Exec.TonEnv.InMsgParam

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnv (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrTonEnvBalance i <|
  execInstrTonEnvNow i <|
  execInstrTonEnvGetParam i <|
  execInstrTonEnvGetPrecompiledGas i <|
  execInstrTonEnvRandu256 i <|
  execInstrTonEnvRand i <|
  execInstrTonEnvSetRand i <|
  execInstrTonEnvGetGlobVar i <|
  execInstrTonEnvGetGlob i <|
  execInstrTonEnvSetGlobVar i <|
  execInstrTonEnvSetGlob i <|
  execInstrTonEnvAccept i <|
  execInstrTonEnvSetGasLimit i <|
  execInstrTonEnvGasConsumed i <|
  execInstrTonEnvCommit i <|
  execInstrTonEnvLdGrams i <|
  execInstrTonEnvStGrams i <|
  execInstrTonEnvLdMsgAddr i <|
  execInstrTonEnvRewriteStdAddr i <|
  execInstrTonEnvGlobalId i <|
  execInstrTonEnvGetGasFee i <|
  execInstrTonEnvGetStorageFee i <|
  execInstrTonEnvGetForwardFee i <|
  execInstrTonEnvGetOriginalFwdFee i <|
  execInstrTonEnvGetGasFeeSimple i <|
  execInstrTonEnvGetForwardFeeSimple i <|
  execInstrTonEnvInMsgParam i <|
    next

end TvmLean
