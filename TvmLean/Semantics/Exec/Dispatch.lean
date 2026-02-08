import TvmLean.Model
import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Stack
import TvmLean.Semantics.Exec.Cont
import TvmLean.Semantics.Exec.Cell
import TvmLean.Semantics.Exec.Flow
import TvmLean.Semantics.Exec.Arith
import TvmLean.Semantics.Exec.Tuple
import TvmLean.Semantics.Exec.CellOp
import TvmLean.Semantics.Exec.TonEnv
import TvmLean.Semantics.Exec.Crypto
import TvmLean.Semantics.Exec.Msg
import TvmLean.Semantics.Exec.Misc
import TvmLean.Semantics.Exec.Debug
import TvmLean.Semantics.Exec.Exception
import TvmLean.Semantics.Exec.Dict

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstr (host : Host) (i : Instr) : VM Unit :=
  execInstrStack host i <|
    execInstrCont host i <|
      execInstrCell host i <|
        execInstrFlow host i <|
          execInstrArith host i <|
            execInstrTuple host i <|
              execInstrCellOp host i <|
                execInstrTonEnv host i <|
                  execInstrCrypto host i <|
                    execInstrMsg host i <|
                      execInstrMisc host i <|
                      execInstrDebug host i <|
                      execInstrException host i <|
                        execInstrDict host i <|
                          VM.unimplementedInstr { name := Instr.pretty i } "no exec handler"

end TvmLean
