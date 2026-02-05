-- Auto-generated stub for TVM instruction PREVMCBLOCKS_100 (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigPrevMcBlocks100 : IO Unit := do
  let prevInfo : Array Value := #[.int (.num 111), .int (.num 222), .int (.num 333)]
  let params := mkParamsWith 13 (.tuple prevInfo)

  let (code0, st0) ← runInstrWithC7 (.tonEnvOp .prevMcBlocks100) (mkC7Params params)
  assert (code0 == -1) s!"PREVMCBLOCKS_100: unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"PREVMCBLOCKS_100: unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == (.int (.num 333))) s!"PREVMCBLOCKS_100: expected 333, got {st0.stack[0]!.pretty}"

  -- Missing `c7`: rangeChk.
  let (code1, _st1) ← runInstrWithC7 (.tonEnvOp .prevMcBlocks100) #[]
  assert (code1 == (~~~ Excno.rangeChk.toInt)) s!"PREVMCBLOCKS_100(no c7): expected rangeChk, got exitCode={code1}"

  -- `c7[0]` not a tuple: typeChk.
  let (code2, _st2) ← runInstrWithC7 (.tonEnvOp .prevMcBlocks100) #[.int (.num 0)]
  assert (code2 == (~~~ Excno.typeChk.toInt)) s!"PREVMCBLOCKS_100(bad c7): expected typeChk, got exitCode={code2}"

  -- Params tuple too short: rangeChk.
  let shortParams : Array Value := Array.replicate 13 (.int (.num 0))
  let (code3, _st3) ← runInstrWithC7 (.tonEnvOp .prevMcBlocks100) (mkC7Params shortParams)
  assert (code3 == (~~~ Excno.rangeChk.toInt)) s!"PREVMCBLOCKS_100(short params): expected rangeChk, got exitCode={code3}"

  -- Param[13] not a tuple: typeChk.
  let paramsBad := mkParamsWith 13 (.int (.num 0))
  let (code4, _st4) ← runInstrWithC7 (.tonEnvOp .prevMcBlocks100) (mkC7Params paramsBad)
  assert (code4 == (~~~ Excno.typeChk.toInt)) s!"PREVMCBLOCKS_100(bad param): expected typeChk, got exitCode={code4}"

  -- Prev blocks tuple too short: rangeChk (idx=2).
  let paramsShort := mkParamsWith 13 (.tuple #[.int (.num 111), .int (.num 222)])
  let (code5, _st5) ← runInstrWithC7 (.tonEnvOp .prevMcBlocks100) (mkC7Params paramsShort)
  assert (code5 == (~~~ Excno.rangeChk.toInt)) s!"PREVMCBLOCKS_100(short tuple): expected rangeChk, got exitCode={code5}"

initialize
  Tests.registerTest "config/prevmcblocks_100" testConfigPrevMcBlocks100
  Tests.registerRoundtrip (.tonEnvOp .prevMcBlocks100)
