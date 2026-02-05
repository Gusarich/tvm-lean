-- Auto-generated stub for TVM instruction GETGLOB (category: globals).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testGlobalsGetGlob : IO Unit := do
  let c7 : Array Value := #[.int (.num 0), .int (.num 11), .int (.num 22), .int (.num 33)]

  let (code0, st0) ← runInstrWithC7 (.tonEnvOp (.getGlob 3)) c7
  assert (code0 == -1) s!"GETGLOB: unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"GETGLOB: unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == .int (.num 33)) s!"GETGLOB: unexpected value {st0.stack[0]!.pretty}"

  let (code1, st1) ← runInstrWithC7 (.tonEnvOp (.getGlob 31)) c7
  assert (code1 == -1) s!"GETGLOB(oob): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"GETGLOB(oob): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == .null) s!"GETGLOB(oob): expected null, got {st1.stack[0]!.pretty}"

initialize
  Tests.registerTest "globals/getglob" testGlobalsGetGlob
  Tests.registerRoundtrip (.tonEnvOp (.getGlob 1))
  Tests.registerRoundtrip (.tonEnvOp (.getGlob 31))
