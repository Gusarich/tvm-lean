-- Auto-generated stub for TVM instruction GETGLOBVAR (category: globals).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testGlobalsGetGlobVar : IO Unit := do
  let c7 : Array Value := #[.int (.num 10), .int (.num 20), .int (.num 30)]

  -- In-range.
  let (code0, st0) ← runInstrWithC7 (.tonEnvOp .getGlobVar) c7 (stack := #[.int (.num 1)])
  assert (code0 == -1) s!"GETGLOBVAR: unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"GETGLOBVAR: unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == .int (.num 20)) s!"GETGLOBVAR: unexpected value {st0.stack[0]!.pretty}"

  -- Out of range => null.
  let (code1, st1) ← runInstrWithC7 (.tonEnvOp .getGlobVar) c7 (stack := #[.int (.num 10)])
  assert (code1 == -1) s!"GETGLOBVAR(oob): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"GETGLOBVAR(oob): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == .null) s!"GETGLOBVAR(oob): expected null, got {st1.stack[0]!.pretty}"

  -- Bad index => rangeChk.
  let (code2, _st2) ← runInstrWithC7 (.tonEnvOp .getGlobVar) c7 (stack := #[.int (.num (-1))])
  assert (code2 == (~~~ Excno.rangeChk.toInt)) s!"GETGLOBVAR(neg): expected rangeChk, got exitCode={code2}"

initialize
  Tests.registerTest "globals/getglobvar" testGlobalsGetGlobVar
  Tests.registerRoundtrip (.tonEnvOp .getGlobVar)
