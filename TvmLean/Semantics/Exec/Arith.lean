import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Arith.ContExt
import TvmLean.Semantics.Exec.Arith.Ext
import TvmLean.Semantics.Exec.Arith.Inc
import TvmLean.Semantics.Exec.Arith.Qinc
import TvmLean.Semantics.Exec.Arith.Dec
import TvmLean.Semantics.Exec.Arith.Qdec
import TvmLean.Semantics.Exec.Arith.Negate
import TvmLean.Semantics.Exec.Arith.Qnegate
import TvmLean.Semantics.Exec.Arith.Qpow2
import TvmLean.Semantics.Exec.Arith.Add
import TvmLean.Semantics.Exec.Arith.Qadd
import TvmLean.Semantics.Exec.Arith.AddInt
import TvmLean.Semantics.Exec.Arith.Sub
import TvmLean.Semantics.Exec.Arith.Qsub
import TvmLean.Semantics.Exec.Arith.Qsubr
import TvmLean.Semantics.Exec.Arith.Subr
import TvmLean.Semantics.Exec.Arith.MulInt
import TvmLean.Semantics.Exec.Arith.Mul
import TvmLean.Semantics.Exec.Arith.Qmul
import TvmLean.Semantics.Exec.Arith.Min
import TvmLean.Semantics.Exec.Arith.Max
import TvmLean.Semantics.Exec.Arith.Qmax
import TvmLean.Semantics.Exec.Arith.Minmax
import TvmLean.Semantics.Exec.Arith.Abs
import TvmLean.Semantics.Exec.Arith.Bitsize
import TvmLean.Semantics.Exec.Arith.Ubitsize
import TvmLean.Semantics.Exec.Arith.MulShrModConst
import TvmLean.Semantics.Exec.Arith.DivMod
import TvmLean.Semantics.Exec.Arith.MulDivMod
import TvmLean.Semantics.Exec.Arith.LshiftConst
import TvmLean.Semantics.Exec.Arith.RshiftConst
import TvmLean.Semantics.Exec.Arith.Lshift
import TvmLean.Semantics.Exec.Arith.Rshift
import TvmLean.Semantics.Exec.Arith.Equal
import TvmLean.Semantics.Exec.Arith.Neq
import TvmLean.Semantics.Exec.Arith.And
import TvmLean.Semantics.Exec.Arith.Or
import TvmLean.Semantics.Exec.Arith.Xor
import TvmLean.Semantics.Exec.Arith.Not
import TvmLean.Semantics.Exec.Arith.Sgn
import TvmLean.Semantics.Exec.Arith.Less
import TvmLean.Semantics.Exec.Arith.Leq
import TvmLean.Semantics.Exec.Arith.Greater
import TvmLean.Semantics.Exec.Arith.Geq
import TvmLean.Semantics.Exec.Arith.Cmp
import TvmLean.Semantics.Exec.Arith.LessInt
import TvmLean.Semantics.Exec.Arith.EqInt
import TvmLean.Semantics.Exec.Arith.GtInt
import TvmLean.Semantics.Exec.Arith.NeqInt
import TvmLean.Semantics.Exec.Arith.PushNull
import TvmLean.Semantics.Exec.Arith.IsNull
import TvmLean.Semantics.Exec.Arith.NullSwapIf
import TvmLean.Semantics.Exec.Arith.NullSwapIfNot
import TvmLean.Semantics.Exec.Arith.NullRotrIf
import TvmLean.Semantics.Exec.Arith.NullRotrIfNot
import TvmLean.Semantics.Exec.Arith.NullSwapIf2
import TvmLean.Semantics.Exec.Arith.NullSwapIfNot2
import TvmLean.Semantics.Exec.Arith.NullRotrIf2
import TvmLean.Semantics.Exec.Arith.NullRotrIfNot2

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrArith (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrArithContExt i <|
  execInstrArithExt i <|
  execInstrArithInc i <|
  execInstrArithQinc i <|
  execInstrArithDec i <|
  execInstrArithQdec i <|
  execInstrArithNegate i <|
  execInstrArithQnegate i <|
  execInstrArithQpow2 i <|
  execInstrArithAdd i <|
  execInstrArithQadd i <|
  execInstrArithAddInt i <|
  execInstrArithSub i <|
  execInstrArithQsub i <|
  execInstrArithQsubr i <|
  execInstrArithSubr i <|
  execInstrArithMulInt i <|
  execInstrArithMul i <|
  execInstrArithQmul i <|
  execInstrArithMin i <|
  execInstrArithMax i <|
  execInstrArithQmax i <|
  execInstrArithMinmax i <|
  execInstrArithAbs i <|
  execInstrArithBitsize i <|
  execInstrArithUbitsize i <|
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
