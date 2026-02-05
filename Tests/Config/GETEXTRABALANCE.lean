-- Tests for TVM instruction GETEXTRABALANCE (category: config).
import Tests.Config.Util

open TvmLean Tests
open Tests.Config

def testConfigGetExtraBalance : IO Unit := do
  let id : Nat := 17
  let valueNat : Nat := 0x1234
  let valueBits : BitString := natToBits 2 5 ++ natToBits valueNat 16
  let valueSlice : Slice := Slice.ofCell (Cell.mkOrdinary valueBits #[])

  let keyBits : BitString := natToBits id 32
  let dictRoot ←
    match dictSetSliceWithCells none keyBits valueSlice .set with
    | .ok (some root, _, _, _) => pure root
    | .ok (none, _, _, _) => throw (IO.userError "GETEXTRABALANCE: expected dict root")
    | .error e => throw (IO.userError s!"GETEXTRABALANCE: dictSetSliceWithCells failed: {reprStr e}")

  let balanceTuple : Array Value := #[.int (.num 0), .cell dictRoot]
  let params := mkParamsWith 7 (.tuple balanceTuple)

  -- Found.
  let (code0, st0) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params params) #[.int (.num (Int.ofNat id))]
  assert (code0 == -1) s!"GETEXTRABALANCE(found): unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"GETEXTRABALANCE(found): unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == (.int (.num (Int.ofNat valueNat)))) s!"GETEXTRABALANCE(found): unexpected value {st0.stack[0]!.pretty}"

  -- Not found -> 0.
  let (code1, st1) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params params) #[.int (.num 18)]
  assert (code1 == -1) s!"GETEXTRABALANCE(not found): unexpected exitCode={code1}"
  assert (st1.stack.size == 1) s!"GETEXTRABALANCE(not found): unexpected stack size={st1.stack.size}"
  assert (st1.stack[0]! == (.int (.num 0))) s!"GETEXTRABALANCE(not found): expected 0, got {st1.stack[0]!.pretty}"

  -- Null dict root -> 0.
  let balanceNull : Array Value := #[.int (.num 0), .null]
  let paramsNull := mkParamsWith 7 (.tuple balanceNull)
  let (code2, st2) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params paramsNull) #[.int (.num (Int.ofNat id))]
  assert (code2 == -1) s!"GETEXTRABALANCE(null dict): unexpected exitCode={code2}"
  assert (st2.stack.size == 1) s!"GETEXTRABALANCE(null dict): unexpected stack size={st2.stack.size}"
  assert (st2.stack[0]! == (.int (.num 0))) s!"GETEXTRABALANCE(null dict): expected 0, got {st2.stack[0]!.pretty}"

  -- Bad dict root type -> typeChk.
  let balanceBadRoot : Array Value := #[.int (.num 0), .int (.num 0)]
  let paramsBadRoot := mkParamsWith 7 (.tuple balanceBadRoot)
  let (code3, _st3) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params paramsBadRoot) #[.int (.num (Int.ofNat id))]
  assert (code3 == (~~~ Excno.typeChk.toInt)) s!"GETEXTRABALANCE(bad dict root): expected typeChk, got exitCode={code3}"

  -- Bad param[7] type -> typeChk.
  let paramsBadBal := mkParamsWith 7 (.int (.num 0))
  let (code4, _st4) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params paramsBadBal) #[.int (.num (Int.ofNat id))]
  assert (code4 == (~~~ Excno.typeChk.toInt)) s!"GETEXTRABALANCE(bad balance): expected typeChk, got exitCode={code4}"

  -- Range checks on id.
  let (code5, _st5) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params params) #[.int (.num (-1))]
  assert (code5 == (~~~ Excno.rangeChk.toInt)) s!"GETEXTRABALANCE(neg id): expected rangeChk, got exitCode={code5}"

  let (code6, _st6) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params params) #[.int (.num 4_294_967_296)]
  assert (code6 == (~~~ Excno.rangeChk.toInt)) s!"GETEXTRABALANCE(too large): expected rangeChk, got exitCode={code6}"

  -- Missing c7 / bad c7: pushC7Param checks.
  let (code7, _st7) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) #[] #[.int (.num 0)]
  assert (code7 == (~~~ Excno.rangeChk.toInt)) s!"GETEXTRABALANCE(no c7): expected rangeChk, got exitCode={code7}"

  let (code8, _st8) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) #[.int (.num 0)] #[.int (.num 0)]
  assert (code8 == (~~~ Excno.typeChk.toInt)) s!"GETEXTRABALANCE(bad c7): expected typeChk, got exitCode={code8}"

  -- Malformed value: cellUnd.
  let badValueBits : BitString := natToBits 1 5 -- lenBytes=1, but no payload bits
  let badValueSlice : Slice := Slice.ofCell (Cell.mkOrdinary badValueBits #[])
  let dictBad ←
    match dictSetSliceWithCells none keyBits badValueSlice .set with
    | .ok (some root, _, _, _) => pure root
    | .ok (none, _, _, _) => throw (IO.userError "GETEXTRABALANCE: expected dict root (bad)")
    | .error e => throw (IO.userError s!"GETEXTRABALANCE: dictSetSliceWithCells failed (bad): {reprStr e}")
  let balanceBadVal : Array Value := #[.int (.num 0), .cell dictBad]
  let paramsBadVal := mkParamsWith 7 (.tuple balanceBadVal)
  let (code9, _st9) ← runInstrWithC7 (.tonEnvOp .getExtraBalance) (mkC7Params paramsBadVal) #[.int (.num (Int.ofNat id))]
  assert (code9 == (~~~ Excno.cellUnd.toInt)) s!"GETEXTRABALANCE(malformed value): expected cellUnd, got exitCode={code9}"

initialize
  Tests.registerTest "config/getextrabalance" testConfigGetExtraBalance
  Tests.registerRoundtrip (.tonEnvOp .getExtraBalance)

