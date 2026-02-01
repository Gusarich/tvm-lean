import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Tuple.Mktuple
import TvmLean.Core.Exec.Tuple.Index
import TvmLean.Core.Exec.Tuple.Index2
import TvmLean.Core.Exec.Tuple.Index3
import TvmLean.Core.Exec.Tuple.Untuple
import TvmLean.Core.Exec.Tuple.UnpackFirst
import TvmLean.Core.Exec.Tuple.Explode
import TvmLean.Core.Exec.Tuple.SetIndex
import TvmLean.Core.Exec.Tuple.IndexQ
import TvmLean.Core.Exec.Tuple.SetIndexQ
import TvmLean.Core.Exec.Tuple.MktupleVar
import TvmLean.Core.Exec.Tuple.IndexVar
import TvmLean.Core.Exec.Tuple.UntupleVar
import TvmLean.Core.Exec.Tuple.UnpackFirstVar
import TvmLean.Core.Exec.Tuple.ExplodeVar
import TvmLean.Core.Exec.Tuple.SetIndexVar
import TvmLean.Core.Exec.Tuple.IndexVarQ
import TvmLean.Core.Exec.Tuple.SetIndexVarQ
import TvmLean.Core.Exec.Tuple.Tlen
import TvmLean.Core.Exec.Tuple.Qtlen
import TvmLean.Core.Exec.Tuple.IsTuple
import TvmLean.Core.Exec.Tuple.Last
import TvmLean.Core.Exec.Tuple.Tpush
import TvmLean.Core.Exec.Tuple.Tpop

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTuple (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .tupleOp op =>
      execTupleOpMktuple op <|
      execTupleOpIndex op <|
      execTupleOpIndex2 op <|
      execTupleOpIndex3 op <|
      execTupleOpUntuple op <|
      execTupleOpUnpackFirst op <|
      execTupleOpExplode op <|
      execTupleOpSetIndex op <|
      execTupleOpIndexQ op <|
      execTupleOpSetIndexQ op <|
      execTupleOpMktupleVar op <|
      execTupleOpIndexVar op <|
      execTupleOpUntupleVar op <|
      execTupleOpUnpackFirstVar op <|
      execTupleOpExplodeVar op <|
      execTupleOpSetIndexVar op <|
      execTupleOpIndexVarQ op <|
      execTupleOpSetIndexVarQ op <|
      execTupleOpTlen op <|
      execTupleOpQtlen op <|
      execTupleOpIsTuple op <|
      execTupleOpLast op <|
      execTupleOpTpush op <|
      execTupleOpTpop op <|
        next
  | _ => next

end TvmLean
