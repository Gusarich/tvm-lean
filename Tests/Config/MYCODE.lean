-- Auto-generated stub for TVM instruction MYCODE (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigMyCode : IO Unit := do
  let code : Cell := cellOfBytes #[0xbb, 0xcc]
  testC7AliasInstr (.tonEnvOp .myCode) 10 (.cell code)

initialize
  Tests.registerTest "config/mycode" testConfigMyCode
  Tests.registerRoundtrip (.tonEnvOp .myCode)
