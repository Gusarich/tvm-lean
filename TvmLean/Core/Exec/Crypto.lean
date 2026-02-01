import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Crypto.HashExt
import TvmLean.Core.Exec.Crypto.HashCU
import TvmLean.Core.Exec.Crypto.HashSU
import TvmLean.Core.Exec.Crypto.ChkSignU
import TvmLean.Core.Exec.Crypto.ChkSignS

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCrypto (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrCryptoHashExt i <|
  execInstrCryptoHashCU i <|
  execInstrCryptoHashSU i <|
  execInstrCryptoChkSignU i <|
  execInstrCryptoChkSignS i <|
    next

end TvmLean
