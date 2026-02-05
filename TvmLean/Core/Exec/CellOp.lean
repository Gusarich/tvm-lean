import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.CellOp.Ext
import TvmLean.Core.Exec.CellOp.Subslice
import TvmLean.Core.Exec.CellOp.Split
import TvmLean.Core.Exec.CellOp.PldRefVar
import TvmLean.Core.Exec.CellOp.LoadLeInt
import TvmLean.Core.Exec.CellOp.LdZeroes
import TvmLean.Core.Exec.CellOp.LdOnes
import TvmLean.Core.Exec.CellOp.LdSame
import TvmLean.Core.Exec.CellOp.Sdepth
import TvmLean.Core.Exec.CellOp.Clevel
import TvmLean.Core.Exec.CellOp.ClevelMask
import TvmLean.Core.Exec.CellOp.ChashI
import TvmLean.Core.Exec.CellOp.CdepthI
import TvmLean.Core.Exec.CellOp.ChashIX
import TvmLean.Core.Exec.CellOp.CdepthIX
import TvmLean.Core.Exec.CellOp.SchkBits
import TvmLean.Core.Exec.CellOp.SchkRefs
import TvmLean.Core.Exec.CellOp.SchkBitRefs
import TvmLean.Core.Exec.CellOp.Bdepth
import TvmLean.Core.Exec.CellOp.Brefs
import TvmLean.Core.Exec.CellOp.Bbitrefs
import TvmLean.Core.Exec.CellOp.Brembits
import TvmLean.Core.Exec.CellOp.Bremrefs
import TvmLean.Core.Exec.CellOp.Brembitrefs
import TvmLean.Core.Exec.CellOp.BchkBitsImm
import TvmLean.Core.Exec.CellOp.Bchk

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCellOp (i : Instr) (next : VM Unit) : VM Unit := do
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
