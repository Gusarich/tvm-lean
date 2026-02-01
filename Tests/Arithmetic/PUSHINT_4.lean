-- Auto-generated stub for TVM instruction PUSHINT_4 (category: arithmetic).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.pushInt (.num 0))
  Tests.registerRoundtrip (.pushInt (.num (-5)))
