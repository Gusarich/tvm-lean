-- Auto-generated stub for TVM instruction BLOCKLT (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigBlockLt : IO Unit := do
  testC7AliasInstr (.tonEnvOp .blockLt) 4 (.int (.num 424242))

initialize
  Tests.registerTest "config/blocklt" testConfigBlockLt
  Tests.registerRoundtrip (.tonEnvOp .blockLt)
