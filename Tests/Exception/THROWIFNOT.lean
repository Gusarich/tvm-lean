-- Auto-generated stub for TVM instruction THROWIFNOT (category: exception).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.throwIfNot 1000)
