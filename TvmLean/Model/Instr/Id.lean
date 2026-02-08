namespace TvmLean

/-- Canonical instruction identifier used for spec indexing and coverage. -/
structure InstrId where
  name : String
  deriving Repr, Inhabited, DecidableEq, BEq

instance : ToString InstrId where
  toString i := i.name

end TvmLean
