-- Auto-generated stub for TVM instruction LTIME (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigLTime : IO Unit := do
  testC7AliasInstr (.tonEnvOp .lTime) 5 (.int (.num 5555))

initialize
  Tests.registerTest "config/ltime" testConfigLTime
  Tests.registerRoundtrip (.tonEnvOp .lTime)
