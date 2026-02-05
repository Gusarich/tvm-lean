-- Auto-generated stub for TVM instruction GETPARAMLONG2 (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigGetParamLong2 : IO Unit := do
  -- Uses the 24-bit encoding 0xf88112..0xf881ff (per spec split).
  testC7AliasInstr (.tonEnvOp (.getParam 42)) 42 (.int (.num 4242))

initialize
  Tests.registerTest "config/getparamlong2" testConfigGetParamLong2
  Tests.registerRoundtrip (.tonEnvOp (.getParam 42))
  Tests.registerRoundtrip (.tonEnvOp (.getParam 255))
