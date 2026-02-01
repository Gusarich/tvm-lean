import TvmLean.Core.Prelude
import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Stack
import TvmLean.Core.Exec.Cont
import TvmLean.Core.Exec.Cell
import TvmLean.Core.Exec.Flow
import TvmLean.Core.Exec.Arith
import TvmLean.Core.Exec.Tuple
import TvmLean.Core.Exec.CellOp
import TvmLean.Core.Exec.TonEnv
import TvmLean.Core.Exec.Crypto
import TvmLean.Core.Exec.Msg
import TvmLean.Core.Exec.Exception
import TvmLean.Core.Exec.Dict

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstr (i : Instr) : VM Unit :=
  execInstrStack i <|
    execInstrCont i <|
      execInstrCell i <|
        execInstrFlow i <|
          execInstrArith i <|
            execInstrTuple i <|
              execInstrCellOp i <|
                execInstrTonEnv i <|
                  execInstrCrypto i <|
                    execInstrMsg i <|
                      execInstrException i <|
                        execInstrDict i <|
                          throw .invOpcode

end TvmLean
