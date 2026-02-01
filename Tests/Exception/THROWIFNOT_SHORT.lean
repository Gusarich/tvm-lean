-- Auto-generated stub for TVM instruction THROWIFNOT_SHORT (category: exception).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.throwIfNot 0)
  Tests.registerRoundtrip (.throwIfNot 63)
