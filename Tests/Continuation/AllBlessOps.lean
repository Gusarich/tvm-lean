import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.Bless

def runInstrWithStack (i : Instr) (stack : Stack) (fuel : Nat := 80) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 [i] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"{i.pretty}: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def assertExitOk (ctx : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{ctx}: unexpected exitCode={code}"

def testBlessOps : IO Unit := do
  let code99 ←
    match assembleCp0 [.pushInt (.num 99)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let cs99 : Slice := Slice.ofCell code99

  -- BLESS: pop slice, push ordinary continuation with empty cdata.
  let (codeB, stB) ← runInstrWithStack .bless #[vInt 1, .slice cs99]
  assertExitOk "cont/bless" codeB
  assert (stB.stack.size == 2) s!"cont/bless: expected stack size 2"
  assert (stB.stack[0]! == vInt 1) s!"cont/bless: value changed"
  match stB.stack[1]! with
  | .cont (.ordinary code _ _ cdata) =>
      assert (code == cs99) s!"cont/bless: code slice mismatch"
      assert (cdata.stack.isEmpty) s!"cont/bless: expected empty closure stack"
      assert (cdata.nargs == -1) s!"cont/bless: expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/bless: expected cont, got {v.pretty}")

  -- BLESSARGS: capture top `copy` elements into closure stack, store `more` as nargs.
  let (codeBA, stBA) ← runInstrWithStack (.blessArgs 2 (-1)) #[vInt 1, vInt 2, vInt 3, .slice cs99]
  assertExitOk "cont/blessargs(2,-1)" codeBA
  assert (stBA.stack.size == 2) s!"cont/blessargs: expected stack size 2"
  assert (stBA.stack[0]! == vInt 1) s!"cont/blessargs: expected remaining [1]"
  match stBA.stack[1]! with
  | .cont (.ordinary code _ _ cdata) =>
      assert (code == cs99) s!"cont/blessargs: code slice mismatch"
      assert (cdata.stack == #[vInt 2, vInt 3]) s!"cont/blessargs: expected captured [2,3], got {cdata.stack}"
      assert (cdata.nargs == -1) s!"cont/blessargs: expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/blessargs: expected cont, got {v.pretty}")

  -- BLESSVARARGS: copy/more from stack (copy in 0..255, more in -1..255).
  let (codeBV, stBV) ← runInstrWithStack .blessVarArgs #[vInt 1, vInt 2, vInt 3, .slice cs99, vInt 2, vInt 7]
  assertExitOk "cont/blessvarargs(copy=2,more=7)" codeBV
  assert (stBV.stack.size == 2) s!"cont/blessvarargs: expected stack size 2"
  assert (stBV.stack[0]! == vInt 1) s!"cont/blessvarargs: expected remaining [1]"
  match stBV.stack[1]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.stack == #[vInt 2, vInt 3]) s!"cont/blessvarargs: expected captured [2,3], got {cdata.stack}"
      assert (cdata.nargs == 7) s!"cont/blessvarargs: expected nargs=7, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/blessvarargs: expected cont, got {v.pretty}")

initialize
  Tests.registerTest "continuation/bless" testBlessOps
  Tests.registerRoundtrip .bless
  Tests.registerRoundtrip .blessVarArgs
  Tests.registerRoundtrip (.blessArgs 0 (-1))
  Tests.registerRoundtrip (.blessArgs 15 14)

end Tests.Continuation.Bless

