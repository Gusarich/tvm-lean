-- Auto-generated stub for TVM instruction DUEPAYMENT (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigDuePayment : IO Unit := do
  testC7AliasInstr (.tonEnvOp .duePayment) 15 (.int (.num 777))

initialize
  Tests.registerTest "config/duepayment" testConfigDuePayment
  Tests.registerRoundtrip (.tonEnvOp .duePayment)
