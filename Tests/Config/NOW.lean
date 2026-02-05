-- Auto-generated stub for TVM instruction NOW (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigNow : IO Unit := do
  testC7AliasInstr (.tonEnvOp .now) 3 (.int (.num 171717))

initialize
  Tests.registerTest "config/now" testConfigNow
  Tests.registerRoundtrip (.tonEnvOp .now)
