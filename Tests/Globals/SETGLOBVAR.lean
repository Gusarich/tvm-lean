-- Auto-generated stub for TVM instruction SETGLOBVAR (category: globals).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testGlobalsSetGlobVar : IO Unit := do
  let base : Array Value := #[.int (.num 0), .int (.num 1)]

  -- Set existing index.
  let (code0, st0) ←
    runInstrWithC7 (.tonEnvOp .setGlobVar) base (stack := #[.int (.num 999), .int (.num 1)])
  assert (code0 == -1) s!"SETGLOBVAR: unexpected exitCode={code0}"
  assert (st0.stack.isEmpty) s!"SETGLOBVAR: expected empty stack, got size={st0.stack.size}"
  assert (st0.regs.c7.size == 2) s!"SETGLOBVAR: unexpected c7 size={st0.regs.c7.size}"
  assert (st0.regs.c7[1]! == .int (.num 999)) s!"SETGLOBVAR: unexpected c7[1]={st0.regs.c7[1]!.pretty}"

  -- Extend c7.
  let (code1, st1) ←
    runInstrWithC7 (.tonEnvOp .setGlobVar) base (stack := #[.int (.num 42), .int (.num 5)])
  assert (code1 == -1) s!"SETGLOBVAR(extend): unexpected exitCode={code1}"
  assert (st1.stack.isEmpty) s!"SETGLOBVAR(extend): expected empty stack, got size={st1.stack.size}"
  assert (st1.regs.c7.size == 6) s!"SETGLOBVAR(extend): expected c7 size 6, got {st1.regs.c7.size}"
  assert (st1.regs.c7[5]! == .int (.num 42)) s!"SETGLOBVAR(extend): unexpected c7[5]={st1.regs.c7[5]!.pretty}"

  -- Bad index => rangeChk.
  let (code2, _st2) ←
    runInstrWithC7 (.tonEnvOp .setGlobVar) base (stack := #[.int (.num 0), .int (.num (-1))])
  assert (code2 == (~~~ Excno.rangeChk.toInt)) s!"SETGLOBVAR(neg): expected rangeChk, got exitCode={code2}"

initialize
  Tests.registerTest "globals/setglobvar" testGlobalsSetGlobVar
  Tests.registerRoundtrip (.tonEnvOp .setGlobVar)
