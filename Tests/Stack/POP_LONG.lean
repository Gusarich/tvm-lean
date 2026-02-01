-- Auto-generated stub for TVM instruction POP_LONG (category: stack).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.pop 200)
