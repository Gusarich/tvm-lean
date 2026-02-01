import TvmLean.Core.Exec.Common
import TvmLean.Core.Exec.Cell.Ctos
import TvmLean.Core.Exec.Cell.Xctos
import TvmLean.Core.Exec.Cell.Newc
import TvmLean.Core.Exec.Cell.Endc
import TvmLean.Core.Exec.Cell.Ends
import TvmLean.Core.Exec.Cell.Sbits
import TvmLean.Core.Exec.Cell.Srefs
import TvmLean.Core.Exec.Cell.Sbitrefs
import TvmLean.Core.Exec.Cell.Cdepth
import TvmLean.Core.Exec.Cell.Sempty
import TvmLean.Core.Exec.Cell.Sdempty
import TvmLean.Core.Exec.Cell.Srempty
import TvmLean.Core.Exec.Cell.SdCntLead0
import TvmLean.Core.Exec.Cell.SdCntTrail0
import TvmLean.Core.Exec.Cell.SdEq
import TvmLean.Core.Exec.Cell.SdPpfx
import TvmLean.Core.Exec.Cell.SdPpfxRev
import TvmLean.Core.Exec.Cell.SdPfx
import TvmLean.Core.Exec.Cell.SdPfxRev
import TvmLean.Core.Exec.Cell.SdLexCmp
import TvmLean.Core.Exec.Cell.Sdcutfirst
import TvmLean.Core.Exec.Cell.Sdskipfirst
import TvmLean.Core.Exec.Cell.Sdcutlast
import TvmLean.Core.Exec.Cell.Sdskiplast
import TvmLean.Core.Exec.Cell.SdBeginsX
import TvmLean.Core.Exec.Cell.SdBeginsConst
import TvmLean.Core.Exec.Cell.Ldu
import TvmLean.Core.Exec.Cell.LoadInt
import TvmLean.Core.Exec.Cell.LoadIntVar
import TvmLean.Core.Exec.Cell.Ldref
import TvmLean.Core.Exec.Cell.LdrefRtos
import TvmLean.Core.Exec.Cell.PldRefIdx
import TvmLean.Core.Exec.Cell.LoadSliceX
import TvmLean.Core.Exec.Cell.LoadSliceFixed
import TvmLean.Core.Exec.Cell.Sti
import TvmLean.Core.Exec.Cell.Stu
import TvmLean.Core.Exec.Cell.StIntVar
import TvmLean.Core.Exec.Cell.StIntFixed
import TvmLean.Core.Exec.Cell.StSlice
import TvmLean.Core.Exec.Cell.Stb
import TvmLean.Core.Exec.Cell.StbRef
import TvmLean.Core.Exec.Cell.Stref
import TvmLean.Core.Exec.Cell.Bbits
import TvmLean.Core.Exec.Cell.StSliceConst
import TvmLean.Core.Exec.Cell.StZeroes
import TvmLean.Core.Exec.Cell.StOnes
import TvmLean.Core.Exec.Cell.StSame

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCell (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrCellCtos i <|
  execInstrCellXctos i <|
  execInstrCellNewc i <|
  execInstrCellEndc i <|
  execInstrCellEnds i <|
  execInstrCellSbits i <|
  execInstrCellSrefs i <|
  execInstrCellSbitrefs i <|
  execInstrCellCdepth i <|
  execInstrCellSempty i <|
  execInstrCellSdempty i <|
  execInstrCellSrempty i <|
  execInstrCellSdCntLead0 i <|
  execInstrCellSdCntTrail0 i <|
  execInstrCellSdEq i <|
  execInstrCellSdPpfx i <|
  execInstrCellSdPpfxRev i <|
  execInstrCellSdPfx i <|
  execInstrCellSdPfxRev i <|
  execInstrCellSdLexCmp i <|
  execInstrCellSdcutfirst i <|
  execInstrCellSdskipfirst i <|
  execInstrCellSdcutlast i <|
  execInstrCellSdskiplast i <|
  execInstrCellSdBeginsX i <|
  execInstrCellSdBeginsConst i <|
  execInstrCellLdu i <|
  execInstrCellLoadInt i <|
  execInstrCellLoadIntVar i <|
  execInstrCellLdref i <|
  execInstrCellLdrefRtos i <|
  execInstrCellPldRefIdx i <|
  execInstrCellLoadSliceX i <|
  execInstrCellLoadSliceFixed i <|
  execInstrCellSti i <|
  execInstrCellStu i <|
  execInstrCellStIntVar i <|
  execInstrCellStIntFixed i <|
  execInstrCellStSlice i <|
  execInstrCellStb i <|
  execInstrCellStbRef i <|
  execInstrCellStref i <|
  execInstrCellBbits i <|
  execInstrCellStSliceConst i <|
  execInstrCellStZeroes i <|
  execInstrCellStOnes i <|
  execInstrCellStSame i <|
    next

end TvmLean
