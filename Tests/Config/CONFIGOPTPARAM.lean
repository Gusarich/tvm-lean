-- Auto-generated stub for TVM instruction CONFIGOPTPARAM (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigConfigOptParam : IO Unit := do
  let cfgCell : Cell := Cell.mkOrdinary (natToBits 0xAB 8) #[]
  let keyBits : BitString := natToBits 19 32
  let dictRoot ←
    match dictSetRefWithCells none keyBits cfgCell .set with
    | .ok (some root, _, _, _) => pure root
    | .ok (none, _, _, _) => throw (IO.userError "CONFIGOPTPARAM: expected dict root")
    | .error e => throw (IO.userError s!"CONFIGOPTPARAM: dictSetRefWithCells failed: {reprStr e}")
  let params := mkParamsWith 9 (.cell dictRoot)

  -- Found: pushes just the cell.
  let (code0, st0) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params params) #[.int (.num 19)]
  assert (code0 == -1) s!"CONFIGOPTPARAM(found): unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"CONFIGOPTPARAM(found): unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == (.cell cfgCell)) s!"CONFIGOPTPARAM(found): expected cell"

  -- Not found: pushes null.
  let (code1, st1) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params params) #[.int (.num 20)]
  assert (code1 == -1) s!"CONFIGOPTPARAM(not found): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"CONFIGOPTPARAM(not found): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == .null) s!"CONFIGOPTPARAM(not found): expected null, got {st1.stack[0]!.pretty}"

  -- Invalid indices: treat as not found (no exception).
  let (code2, st2) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params params) #[.int (.num (-1))]
  assert (code2 == -1) s!"CONFIGOPTPARAM(neg idx): unexpected exitCode={code2}"
  assert (st2.stack.size == 1) s!"CONFIGOPTPARAM(neg idx): unexpected stack size={st2.stack.size}"
  assert (st2.stack[0]! == .null) s!"CONFIGOPTPARAM(neg idx): expected null, got {st2.stack[0]!.pretty}"

  let (code3, st3) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params params) #[.int (.num 4_294_967_296)]
  assert (code3 == -1) s!"CONFIGOPTPARAM(too large): unexpected exitCode={code3}"
  assert (st3.stack.size == 1) s!"CONFIGOPTPARAM(too large): unexpected stack size={st3.stack.size}"
  assert (st3.stack[0]! == .null) s!"CONFIGOPTPARAM(too large): expected null, got {st3.stack[0]!.pretty}"

  let (code4, st4) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params params) #[.int .nan]
  assert (code4 == -1) s!"CONFIGOPTPARAM(nan idx): unexpected exitCode={code4}"
  assert (st4.stack.size == 1) s!"CONFIGOPTPARAM(nan idx): unexpected stack size={st4.stack.size}"
  assert (st4.stack[0]! == .null) s!"CONFIGOPTPARAM(nan idx): expected null, got {st4.stack[0]!.pretty}"

  -- Null config dict: not found.
  let paramsNull := mkParamsWith 9 .null
  let (code5, st5) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params paramsNull) #[.int (.num 19)]
  assert (code5 == -1) s!"CONFIGOPTPARAM(null root): unexpected exitCode={code5}"
  assert (st5.stack.size == 1) s!"CONFIGOPTPARAM(null root): unexpected stack size={st5.stack.size}"
  assert (st5.stack[0]! == .null) s!"CONFIGOPTPARAM(null root): expected null, got {st5.stack[0]!.pretty}"

  -- Missing c7 / bad c7: propagate pushC7Param checks (rangeChk/typeChk).
  let (code6, _st6) ← runInstrWithC7 (.tonEnvOp (.configParam true)) #[] #[.int (.num 0)]
  assert (code6 == (~~~ Excno.rangeChk.toInt)) s!"CONFIGOPTPARAM(no c7): expected rangeChk, got exitCode={code6}"

  let (code7, _st7) ← runInstrWithC7 (.tonEnvOp (.configParam true)) #[.int (.num 0)] #[.int (.num 0)]
  assert (code7 == (~~~ Excno.typeChk.toInt)) s!"CONFIGOPTPARAM(bad c7): expected typeChk, got exitCode={code7}"

  let shortParams : Array Value := Array.replicate 9 (.int (.num 0))
  let (code8, _st8) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params shortParams) #[.int (.num 0)]
  assert (code8 == (~~~ Excno.rangeChk.toInt)) s!"CONFIGOPTPARAM(short params): expected rangeChk, got exitCode={code8}"

  -- Corrupt dict value (no single ref): dictErr.
  let badValCell : Cell := Cell.mkOrdinary (natToBits 0xFF 8) #[]
  let badValSlice : Slice := Slice.ofCell badValCell
  let dictRootBad ←
    match dictSetSliceWithCells none keyBits badValSlice .set with
    | .ok (some root, _, _, _) => pure root
    | .ok (none, _, _, _) => throw (IO.userError "CONFIGOPTPARAM: expected dict root (bad value)")
    | .error e => throw (IO.userError s!"CONFIGOPTPARAM: dictSetSliceWithCells failed: {reprStr e}")
  let paramsBad := mkParamsWith 9 (.cell dictRootBad)
  let (code9, _st9) ← runInstrWithC7 (.tonEnvOp (.configParam true)) (mkC7Params paramsBad) #[.int (.num 19)]
  assert (code9 == (~~~ Excno.dictErr.toInt)) s!"CONFIGOPTPARAM(bad value): expected dictErr, got exitCode={code9}"

initialize
  Tests.registerTest "config/configoptparam" testConfigConfigOptParam
  Tests.registerRoundtrip (.tonEnvOp (.configParam true))
