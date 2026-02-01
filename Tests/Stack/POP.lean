-- Auto-generated stub for TVM instruction POP (category: stack).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.pop 0)
  Tests.registerRoundtrip (.pop 9)
