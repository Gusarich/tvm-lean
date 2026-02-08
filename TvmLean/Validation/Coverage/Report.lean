import TvmLean.Validation.Coverage.InstrStatus

namespace TvmLean

structure CoverageReport where
  rows : Array InstrCoverageRow
  deriving Repr

end TvmLean
