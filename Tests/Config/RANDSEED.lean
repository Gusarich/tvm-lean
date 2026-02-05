-- Auto-generated stub for TVM instruction RANDSEED (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigRandSeed : IO Unit := do
  testC7AliasInstr (.tonEnvOp .randSeed) 6 (.int (.num 0x123456))

initialize
  Tests.registerTest "config/randseed" testConfigRandSeed
  Tests.registerRoundtrip (.tonEnvOp .randSeed)
