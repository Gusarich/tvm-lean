-- Auto-generated stub for TVM instruction PREVBLOCKSINFOTUPLE (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigPrevBlocksInfoTuple : IO Unit := do
  let info : Array Value := #[.int (.num 1), .int (.num 2)]
  testC7AliasInstr (.tonEnvOp .prevBlocksInfoTuple) 13 (.tuple info)

initialize
  Tests.registerTest "config/prevblocksinfotuple" testConfigPrevBlocksInfoTuple
  Tests.registerRoundtrip (.tonEnvOp .prevBlocksInfoTuple)
