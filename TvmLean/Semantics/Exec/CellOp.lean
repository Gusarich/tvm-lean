import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.CellOp.Ext
import TvmLean.Semantics.Exec.CellOp.Subslice
import TvmLean.Semantics.Exec.CellOp.Split
import TvmLean.Semantics.Exec.CellOp.PldRefVar
import TvmLean.Semantics.Exec.CellOp.LoadLeInt
import TvmLean.Semantics.Exec.CellOp.LdZeroes
import TvmLean.Semantics.Exec.CellOp.LdOnes
import TvmLean.Semantics.Exec.CellOp.LdSame
import TvmLean.Semantics.Exec.CellOp.Sdepth
import TvmLean.Semantics.Exec.CellOp.Clevel
import TvmLean.Semantics.Exec.CellOp.ClevelMask
import TvmLean.Semantics.Exec.CellOp.ChashI
import TvmLean.Semantics.Exec.CellOp.CdepthI
import TvmLean.Semantics.Exec.CellOp.ChashIX
import TvmLean.Semantics.Exec.CellOp.CdepthIX
import TvmLean.Semantics.Exec.CellOp.SchkBits
import TvmLean.Semantics.Exec.CellOp.SchkRefs
import TvmLean.Semantics.Exec.CellOp.SchkBitRefs
import TvmLean.Semantics.Exec.CellOp.Bdepth
import TvmLean.Semantics.Exec.CellOp.Brefs
import TvmLean.Semantics.Exec.CellOp.Bbitrefs
import TvmLean.Semantics.Exec.CellOp.Brembits
import TvmLean.Semantics.Exec.CellOp.Bremrefs
import TvmLean.Semantics.Exec.CellOp.Brembitrefs
import TvmLean.Semantics.Exec.CellOp.BchkBitsImm
import TvmLean.Semantics.Exec.CellOp.Bchk

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellOp (_host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cellOp op =>
      execCellOpExt op <|
      execCellOpSubslice op <|
      execCellOpSplit op <|
      execCellOpPldRefVar op <|
      execCellOpLoadLeInt op <|
      execCellOpLdZeroes op <|
      execCellOpLdOnes op <|
      execCellOpLdSame op <|
      execCellOpSdepth op <|
      execCellOpClevel op <|
      execCellOpClevelMask op <|
      execCellOpChashI op <|
      execCellOpCdepthI op <|
      execCellOpChashIX op <|
      execCellOpCdepthIX op <|
      execCellOpSchkBits op <|
      execCellOpSchkRefs op <|
      execCellOpSchkBitRefs op <|
      execCellOpBdepth op <|
      execCellOpBrefs op <|
      execCellOpBbitrefs op <|
      execCellOpBrembits op <|
      execCellOpBremrefs op <|
      execCellOpBrembitrefs op <|
      execCellOpBchkBitsImm op <|
      execCellOpBchk op <|
        next
  | _ => next

end TvmLean
