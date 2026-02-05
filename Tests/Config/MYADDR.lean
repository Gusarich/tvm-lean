-- Auto-generated stub for TVM instruction MYADDR (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigMyAddr : IO Unit := do
  let addr : Slice := Slice.ofCell (cellOfBytes #[0x01, 0x02, 0x03])
  testC7AliasInstr (.tonEnvOp .myAddr) 8 (.slice addr)

initialize
  Tests.registerTest "config/myaddr" testConfigMyAddr
  Tests.registerRoundtrip (.tonEnvOp .myAddr)
