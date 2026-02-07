import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Tuple.Mktuple
import TvmLean.Semantics.Exec.Tuple.Index
import TvmLean.Semantics.Exec.Tuple.Index2
import TvmLean.Semantics.Exec.Tuple.Index3
import TvmLean.Semantics.Exec.Tuple.Untuple
import TvmLean.Semantics.Exec.Tuple.UnpackFirst
import TvmLean.Semantics.Exec.Tuple.Explode
import TvmLean.Semantics.Exec.Tuple.SetIndex
import TvmLean.Semantics.Exec.Tuple.IndexQ
import TvmLean.Semantics.Exec.Tuple.SetIndexQ
import TvmLean.Semantics.Exec.Tuple.MktupleVar
import TvmLean.Semantics.Exec.Tuple.IndexVar
import TvmLean.Semantics.Exec.Tuple.UntupleVar
import TvmLean.Semantics.Exec.Tuple.UnpackFirstVar
import TvmLean.Semantics.Exec.Tuple.ExplodeVar
import TvmLean.Semantics.Exec.Tuple.SetIndexVar
import TvmLean.Semantics.Exec.Tuple.IndexVarQ
import TvmLean.Semantics.Exec.Tuple.SetIndexVarQ
import TvmLean.Semantics.Exec.Tuple.Tlen
import TvmLean.Semantics.Exec.Tuple.Qtlen
import TvmLean.Semantics.Exec.Tuple.IsTuple
import TvmLean.Semantics.Exec.Tuple.Last
import TvmLean.Semantics.Exec.Tuple.Tpush
import TvmLean.Semantics.Exec.Tuple.Tpop

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrTuple (_host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
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
