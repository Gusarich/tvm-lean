-- Auto-generated stub for TVM instruction CHKSIGNS (category: crypto).
import Tests.Registry

open TvmLean

initialize
  Tests.registerRoundtrip (.cryptoOp .chkSignS)
