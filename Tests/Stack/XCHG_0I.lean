-- Auto-generated stub for TVM instruction XCHG_0I (category: stack).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.xchg0 1)
  Tests.registerRoundtrip (.xchg0 15)
