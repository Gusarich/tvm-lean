import Tests.Registry

open TvmLean Tests

namespace Tests.Config

def runInstrWithC7 (i : Instr) (c7 : Array Value) (stack : Stack := #[]) (fuel : Nat := 50) :
    IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack, regs := { base.regs with c7 := c7 } }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def mkC7Params (params : Array Value) : Array Value :=
  #[.tuple params]

def mkParamsWith (idx : Nat) (v : Value) : Array Value :=
  Id.run do
    let size : Nat := Nat.max 16 (idx + 1)
    let mut ps : Array Value := Array.replicate size (.int (.num 0))
    ps := ps.set! idx v
    return ps

def testC7AliasInstr (i : Instr) (idx : Nat) (v : Value) : IO Unit := do
  -- Success: `c7[0]` is the params tuple, and `params[idx]=v`.
  let params := mkParamsWith idx v
  let (code0, st0) ← runInstrWithC7 i (mkC7Params params)
  assert (code0 == -1) s!"{i.pretty}: unexpected exitCode={code0}"
  assert (st0.stack.size == 1) s!"{i.pretty}: unexpected stack size={st0.stack.size}"
  assert (st0.stack[0]! == v) s!"{i.pretty}: unexpected value {st0.stack[0]!.pretty}"

  -- Missing `c7`: rangeChk.
  let (code1, _st1) ← runInstrWithC7 i #[]
  assert (code1 == (~~~ Excno.rangeChk.toInt)) s!"{i.pretty}(no c7): expected rangeChk, got exitCode={code1}"

  -- `c7[0]` not a tuple: typeChk.
  let (code2, _st2) ← runInstrWithC7 i #[.int (.num 0)]
  assert (code2 == (~~~ Excno.typeChk.toInt)) s!"{i.pretty}(bad c7): expected typeChk, got exitCode={code2}"

  -- Params tuple too short: rangeChk.
  let shortParams : Array Value := Array.replicate idx (.int (.num 0))
  let (code3, _st3) ← runInstrWithC7 i (mkC7Params shortParams)
  assert (code3 == (~~~ Excno.rangeChk.toInt)) s!"{i.pretty}(short params): expected rangeChk, got exitCode={code3}"

end Tests.Config
