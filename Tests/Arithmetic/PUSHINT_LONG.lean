-- Auto-generated stub for TVM instruction PUSHINT_LONG (category: arithmetic).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.pushInt (.num 1000000))
