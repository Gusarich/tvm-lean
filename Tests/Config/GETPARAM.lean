-- Auto-generated stub for TVM instruction GETPARAM (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigGetParam : IO Unit := do
  -- Uses the 16-bit encoding (0xf820..0xf82f).
  testC7AliasInstr (.tonEnvOp (.getParam 3)) 3 (.int (.num 123))

initialize
  Tests.registerTest "config/getparam" testConfigGetParam
  Tests.registerRoundtrip (.tonEnvOp (.getParam 0))
  Tests.registerRoundtrip (.tonEnvOp (.getParam 3))
  Tests.registerRoundtrip (.tonEnvOp (.getParam 7))
  Tests.registerRoundtrip (.tonEnvOp (.getParam 15))
