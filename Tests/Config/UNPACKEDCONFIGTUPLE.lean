-- Auto-generated stub for TVM instruction UNPACKEDCONFIGTUPLE (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigUnpackedConfigTuple : IO Unit := do
  let unpacked : Array Value := #[.int (.num 42)]
  testC7AliasInstr (.tonEnvOp .unpackedConfigTuple) 14 (.tuple unpacked)

initialize
  Tests.registerTest "config/unpackedconfigtuple" testConfigUnpackedConfigTuple
  Tests.registerRoundtrip (.tonEnvOp .unpackedConfigTuple)
