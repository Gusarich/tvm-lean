import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Arith.Inc
import TvmLean.Core.Exec.Arith.Dec
import TvmLean.Core.Exec.Arith.Qdec
import TvmLean.Core.Exec.Arith.Negate
import TvmLean.Core.Exec.Arith.Qnegate
import TvmLean.Core.Exec.Arith.Add
import TvmLean.Core.Exec.Arith.Qadd
import TvmLean.Core.Exec.Arith.AddInt
import TvmLean.Core.Exec.Arith.Sub
import TvmLean.Core.Exec.Arith.Qsub
import TvmLean.Core.Exec.Arith.Subr
import TvmLean.Core.Exec.Arith.MulInt
import TvmLean.Core.Exec.Arith.Mul
import TvmLean.Core.Exec.Arith.Min
import TvmLean.Core.Exec.Arith.Max
import TvmLean.Core.Exec.Arith.Minmax
import TvmLean.Core.Exec.Arith.Abs
import TvmLean.Core.Exec.Arith.MulShrModConst
import TvmLean.Core.Exec.Arith.DivMod
import TvmLean.Core.Exec.Arith.MulDivMod
import TvmLean.Core.Exec.Arith.LshiftConst
import TvmLean.Core.Exec.Arith.RshiftConst
import TvmLean.Core.Exec.Arith.Lshift
import TvmLean.Core.Exec.Arith.Rshift
import TvmLean.Core.Exec.Arith.Equal
import TvmLean.Core.Exec.Arith.Neq
import TvmLean.Core.Exec.Arith.And
import TvmLean.Core.Exec.Arith.Or
import TvmLean.Core.Exec.Arith.Xor
import TvmLean.Core.Exec.Arith.Not
import TvmLean.Core.Exec.Arith.Sgn
import TvmLean.Core.Exec.Arith.Less
import TvmLean.Core.Exec.Arith.Leq
import TvmLean.Core.Exec.Arith.Greater
import TvmLean.Core.Exec.Arith.Geq
import TvmLean.Core.Exec.Arith.Cmp
import TvmLean.Core.Exec.Arith.LessInt
import TvmLean.Core.Exec.Arith.EqInt
import TvmLean.Core.Exec.Arith.GtInt
import TvmLean.Core.Exec.Arith.NeqInt
import TvmLean.Core.Exec.Arith.PushNull
import TvmLean.Core.Exec.Arith.IsNull
import TvmLean.Core.Exec.Arith.NullSwapIf
import TvmLean.Core.Exec.Arith.NullSwapIfNot
import TvmLean.Core.Exec.Arith.NullRotrIf
import TvmLean.Core.Exec.Arith.NullRotrIfNot
import TvmLean.Core.Exec.Arith.NullSwapIf2
import TvmLean.Core.Exec.Arith.NullSwapIfNot2
import TvmLean.Core.Exec.Arith.NullRotrIf2
import TvmLean.Core.Exec.Arith.NullRotrIfNot2

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArith (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrArithInc i <|
  execInstrArithDec i <|
  execInstrArithQdec i <|
  execInstrArithNegate i <|
  execInstrArithQnegate i <|
  execInstrArithAdd i <|
  execInstrArithQadd i <|
  execInstrArithAddInt i <|
  execInstrArithSub i <|
  execInstrArithQsub i <|
  execInstrArithSubr i <|
  execInstrArithMulInt i <|
  execInstrArithMul i <|
  execInstrArithMin i <|
  execInstrArithMax i <|
  execInstrArithMinmax i <|
  execInstrArithAbs i <|
  execInstrArithMulShrModConst i <|
  execInstrArithDivMod i <|
  execInstrArithMulDivMod i <|
  execInstrArithLshiftConst i <|
  execInstrArithRshiftConst i <|
  execInstrArithLshift i <|
  execInstrArithRshift i <|
  execInstrArithEqual i <|
  execInstrArithNeq i <|
  execInstrArithAnd i <|
  execInstrArithOr i <|
  execInstrArithXor i <|
  execInstrArithNot i <|
  execInstrArithSgn i <|
  execInstrArithLess i <|
  execInstrArithLeq i <|
  execInstrArithGreater i <|
  execInstrArithGeq i <|
  execInstrArithCmp i <|
  execInstrArithLessInt i <|
  execInstrArithEqInt i <|
  execInstrArithGtInt i <|
  execInstrArithNeqInt i <|
  execInstrArithPushNull i <|
  execInstrArithIsNull i <|
  execInstrArithNullSwapIf i <|
  execInstrArithNullSwapIfNot i <|
  execInstrArithNullRotrIf i <|
  execInstrArithNullRotrIfNot i <|
  execInstrArithNullSwapIf2 i <|
  execInstrArithNullSwapIfNot2 i <|
  execInstrArithNullRotrIf2 i <|
  execInstrArithNullRotrIfNot2 i <|
    next

end TvmLean
