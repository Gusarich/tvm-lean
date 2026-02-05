-- Auto-generated stub for TVM instruction BALANCE (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigBalance : IO Unit := do
  testC7AliasInstr (.tonEnvOp .balance) 7 (.int (.num 999_000_111))

initialize
  Tests.registerTest "config/balance" testConfigBalance
  Tests.registerRoundtrip (.tonEnvOp .balance)
