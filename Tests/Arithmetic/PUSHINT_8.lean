-- Auto-generated stub for TVM instruction PUSHINT_8 (category: arithmetic).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.pushInt (.num 127))
  Tests.registerRoundtrip (.pushInt (.num (-128)))
