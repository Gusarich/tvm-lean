-- Auto-generated stub for TVM instruction GETPARAMLONG (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigGetParamLong : IO Unit := do
  -- Uses the 24-bit encoding 0xf88100..0xf88111 (per spec split).
  testC7AliasInstr (.tonEnvOp (.getParam 16)) 16 (.int (.num 777))

initialize
  Tests.registerTest "config/getparamlong" testConfigGetParamLong
  Tests.registerRoundtrip (.tonEnvOp (.getParam 16))
