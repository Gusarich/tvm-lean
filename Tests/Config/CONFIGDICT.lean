-- Auto-generated stub for TVM instruction CONFIGDICT (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigConfigDict : IO Unit := do
  let configRootCell : Cell := Cell.mkOrdinary (natToBits 0xBEEF 16) #[]
  let params := mkParamsWith 9 (.cell configRootCell)

  let (code0, st0) ← runInstrWithC7 (.tonEnvOp .configDict) (mkC7Params params)
  assert (code0 == -1) s!"CONFIGDICT: unexpected exitCode={code0}"
  assert (st0.stack.size == 2) s!"CONFIGDICT: unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == (.cell configRootCell)) s!"CONFIGDICT: expected config root cell"
  assert (st0.stack[1]! == (.int (.num 32))) s!"CONFIGDICT: expected 32, got {st0.stack[1]!.pretty}"

  -- Missing `c7`: rangeChk.
  let (code1, _st1) ← runInstrWithC7 (.tonEnvOp .configDict) #[]
  assert (code1 == (~~~ Excno.rangeChk.toInt)) s!"CONFIGDICT(no c7): expected rangeChk, got exitCode={code1}"

  -- `c7[0]` not a tuple: typeChk.
  let (code2, _st2) ← runInstrWithC7 (.tonEnvOp .configDict) #[.int (.num 0)]
  assert (code2 == (~~~ Excno.typeChk.toInt)) s!"CONFIGDICT(bad c7): expected typeChk, got exitCode={code2}"

  -- Params tuple too short: rangeChk.
  let shortParams : Array Value := Array.replicate 9 (.int (.num 0))
  let (code3, _st3) ← runInstrWithC7 (.tonEnvOp .configDict) (mkC7Params shortParams)
  assert (code3 == (~~~ Excno.rangeChk.toInt)) s!"CONFIGDICT(short params): expected rangeChk, got exitCode={code3}"

initialize
  Tests.registerTest "config/configdict" testConfigConfigDict
  Tests.registerRoundtrip (.tonEnvOp .configDict)
