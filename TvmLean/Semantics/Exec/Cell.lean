import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Cell.Ctos
import TvmLean.Semantics.Exec.Cell.Xctos
import TvmLean.Semantics.Exec.Cell.Newc
import TvmLean.Semantics.Exec.Cell.Endc
import TvmLean.Semantics.Exec.Cell.Ends
import TvmLean.Semantics.Exec.Cell.Sbits
import TvmLean.Semantics.Exec.Cell.Srefs
import TvmLean.Semantics.Exec.Cell.Sbitrefs
import TvmLean.Semantics.Exec.Cell.Cdepth
import TvmLean.Semantics.Exec.Cell.Sempty
import TvmLean.Semantics.Exec.Cell.Sdempty
import TvmLean.Semantics.Exec.Cell.Srempty
import TvmLean.Semantics.Exec.Cell.SdCntLead0
import TvmLean.Semantics.Exec.Cell.SdCntTrail0
import TvmLean.Semantics.Exec.Cell.SdEq
import TvmLean.Semantics.Exec.Cell.SdPpfx
import TvmLean.Semantics.Exec.Cell.SdPpfxRev
import TvmLean.Semantics.Exec.Cell.SdPfx
import TvmLean.Semantics.Exec.Cell.SdPfxRev
import TvmLean.Semantics.Exec.Cell.SdLexCmp
import TvmLean.Semantics.Exec.Cell.Sdcutfirst
import TvmLean.Semantics.Exec.Cell.Sdskipfirst
import TvmLean.Semantics.Exec.Cell.Sdcutlast
import TvmLean.Semantics.Exec.Cell.Sdskiplast
import TvmLean.Semantics.Exec.Cell.SdBeginsX
import TvmLean.Semantics.Exec.Cell.SdBeginsConst
import TvmLean.Semantics.Exec.Cell.Ldu
import TvmLean.Semantics.Exec.Cell.LoadInt
import TvmLean.Semantics.Exec.Cell.LoadIntVar
import TvmLean.Semantics.Exec.Cell.Ldref
import TvmLean.Semantics.Exec.Cell.LdrefRtos
import TvmLean.Semantics.Exec.Cell.PldRefIdx
import TvmLean.Semantics.Exec.Cell.LoadSliceX
import TvmLean.Semantics.Exec.Cell.LoadSliceFixed
import TvmLean.Semantics.Exec.Cell.Sti
import TvmLean.Semantics.Exec.Cell.Stu
import TvmLean.Semantics.Exec.Cell.StIntVar
import TvmLean.Semantics.Exec.Cell.StIntFixed
import TvmLean.Semantics.Exec.Cell.StSlice
import TvmLean.Semantics.Exec.Cell.Stb
import TvmLean.Semantics.Exec.Cell.StbRef
import TvmLean.Semantics.Exec.Cell.Stref
import TvmLean.Semantics.Exec.Cell.Bbits
import TvmLean.Semantics.Exec.Cell.StSliceConst
import TvmLean.Semantics.Exec.Cell.StZeroes
import TvmLean.Semantics.Exec.Cell.StOnes
import TvmLean.Semantics.Exec.Cell.StSame
import TvmLean.Semantics.Exec.Cell.Ext

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCell (_host : Host) (i : Instr) (next : VM Unit) : VM Unit :=
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
  execInstrCellExt i <|
    next

end TvmLean
