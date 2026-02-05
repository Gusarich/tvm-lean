-- Auto-generated stub for TVM instruction INCOMINGVALUE (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigIncomingValue : IO Unit := do
  testC7AliasInstr (.tonEnvOp .incomingValue) 11 (.int (.num 1_000_000))

initialize
  Tests.registerTest "config/incomingvalue" testConfigIncomingValue
  Tests.registerRoundtrip (.tonEnvOp .incomingValue)
