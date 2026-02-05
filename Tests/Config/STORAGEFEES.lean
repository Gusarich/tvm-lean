-- Auto-generated stub for TVM instruction STORAGEFEES (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigStorageFees : IO Unit := do
  testC7AliasInstr (.tonEnvOp .storageFees) 12 (.int (.num 1234))

initialize
  Tests.registerTest "config/storagefees" testConfigStorageFees
  Tests.registerRoundtrip (.tonEnvOp .storageFees)
