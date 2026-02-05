-- Auto-generated stub for TVM instruction PUSH (category: stack).
import Tests.Registry
import Tests.Stack.AllStackOps

open TvmLean

initialize
  Tests.registerRoundtrip (.push 0)
  Tests.registerRoundtrip (.push 7)
