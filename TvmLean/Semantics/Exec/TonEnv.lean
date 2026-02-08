import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.TonEnv.Balance
import TvmLean.Semantics.Exec.TonEnv.Now
import TvmLean.Semantics.Exec.TonEnv.GetParamAliases
import TvmLean.Semantics.Exec.TonEnv.GetParam
import TvmLean.Semantics.Exec.TonEnv.ConfigDict
import TvmLean.Semantics.Exec.TonEnv.ConfigParam
import TvmLean.Semantics.Exec.TonEnv.PrevBlocksInfo
import TvmLean.Semantics.Exec.TonEnv.GetPrecompiledGas
import TvmLean.Semantics.Exec.TonEnv.Randu256
import TvmLean.Semantics.Exec.TonEnv.Rand
import TvmLean.Semantics.Exec.TonEnv.SetRand
import TvmLean.Semantics.Exec.TonEnv.GetExtraBalance
import TvmLean.Semantics.Exec.TonEnv.GetGlobVar
import TvmLean.Semantics.Exec.TonEnv.GetGlob
import TvmLean.Semantics.Exec.TonEnv.SetGlobVar
import TvmLean.Semantics.Exec.TonEnv.SetGlob
import TvmLean.Semantics.Exec.TonEnv.Accept
import TvmLean.Semantics.Exec.TonEnv.SetGasLimit
import TvmLean.Semantics.Exec.TonEnv.GasConsumed
import TvmLean.Semantics.Exec.TonEnv.Commit
import TvmLean.Semantics.Exec.TonEnv.LdGrams
import TvmLean.Semantics.Exec.TonEnv.StGrams
import TvmLean.Semantics.Exec.TonEnv.LdMsgAddr
import TvmLean.Semantics.Exec.TonEnv.ParseMsgAddr
import TvmLean.Semantics.Exec.TonEnv.RewriteStdAddr
import TvmLean.Semantics.Exec.TonEnv.RewriteVarAddr
import TvmLean.Semantics.Exec.TonEnv.StdAddr
import TvmLean.Semantics.Exec.TonEnv.GlobalId
import TvmLean.Semantics.Exec.TonEnv.GetGasFee
import TvmLean.Semantics.Exec.TonEnv.GetStorageFee
import TvmLean.Semantics.Exec.TonEnv.GetForwardFee
import TvmLean.Semantics.Exec.TonEnv.GetOriginalFwdFee
import TvmLean.Semantics.Exec.TonEnv.GetGasFeeSimple
import TvmLean.Semantics.Exec.TonEnv.GetForwardFeeSimple
import TvmLean.Semantics.Exec.TonEnv.InMsgParam

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTonEnv (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrTonEnvBalance i <|
  execInstrTonEnvNow i <|
  execInstrTonEnvGetParamAliases i <|
  execInstrTonEnvGetParam i <|
  execInstrTonEnvConfigDict i <|
  execInstrTonEnvConfigParam i <|
  execInstrTonEnvPrevBlocksInfo i <|
  execInstrTonEnvGetPrecompiledGas i <|
  execInstrTonEnvRandu256 i <|
  execInstrTonEnvRand i <|
  execInstrTonEnvSetRand i <|
  execInstrTonEnvGetExtraBalance i <|
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
  execInstrTonEnvParseMsgAddr i <|
  execInstrTonEnvRewriteStdAddr i <|
  execInstrTonEnvRewriteVarAddr i <|
  execInstrTonEnvStdAddr i <|
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
