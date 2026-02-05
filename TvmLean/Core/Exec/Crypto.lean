import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Crypto.HashExt
import TvmLean.Core.Exec.Crypto.HashCU
import TvmLean.Core.Exec.Crypto.HashSU
import TvmLean.Core.Exec.Crypto.Sha256U
import TvmLean.Core.Exec.Crypto.ChkSignU
import TvmLean.Core.Exec.Crypto.ChkSignS
import TvmLean.Core.Exec.Crypto.Ext

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCrypto (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrCryptoHashExt i <|
  execInstrCryptoHashCU i <|
  execInstrCryptoHashSU i <|
  execInstrCryptoSha256U i <|
  execInstrCryptoChkSignU i <|
  execInstrCryptoChkSignS i <|
  execInstrCryptoExt i <|
    next

end TvmLean
