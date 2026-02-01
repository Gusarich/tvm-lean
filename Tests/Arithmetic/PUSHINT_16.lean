-- Auto-generated stub for TVM instruction PUSHINT_16 (category: arithmetic).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.pushInt (.num 20000))
