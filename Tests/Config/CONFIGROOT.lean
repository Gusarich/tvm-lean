-- Auto-generated stub for TVM instruction CONFIGROOT (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigConfigRoot : IO Unit := do
  let config : Cell := cellOfBytes #[0xaa]
  testC7AliasInstr (.tonEnvOp .configRoot) 9 (.cell config)

initialize
  Tests.registerTest "config/configroot" testConfigConfigRoot
  Tests.registerRoundtrip (.tonEnvOp .configRoot)
