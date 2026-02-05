import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation

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

def testSetContArgs : IO Unit := do
  -- Base continuation with no cdata.
  let code0 ←
    match assembleCp0 [] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(empty) failed: {reprStr e}")
  let cont0 : Continuation := .ordinary (Slice.ofCell code0) (.quit 0) OrdCregs.empty OrdCdata.empty

  -- copy=0, more=-1: should leave continuation unchanged and not touch the stack (besides popping/pushing cont).
  let (codeA, stA) ← runInstrWithStack (.setContArgs 0 (-1)) #[vInt 1, .cont cont0]
  assert (codeA == -1) s!"setcontargs(0,-1): unexpected exitCode={codeA}"
  assert (stA.stack.size == 2) s!"setcontargs(0,-1): unexpected stack size={stA.stack.size}"
  assert (stA.stack[0]! == vInt 1) s!"setcontargs(0,-1): value changed"
  match stA.stack[1]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.stack.isEmpty) s!"setcontargs(0,-1): expected empty cdata.stack"
      assert (cdata.nargs == -1) s!"setcontargs(0,-1): expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"setcontargs(0,-1): expected cont, got {v.pretty}")

  -- copy=2, more=-1: capture top 2 values into closure stack; nargs remains -1.
  let (codeB, stB) ← runInstrWithStack (.setContArgs 2 (-1)) #[vInt 1, vInt 2, vInt 3, .cont cont0]
  assert (codeB == -1) s!"setcontargs(2,-1): unexpected exitCode={codeB}"
  assert (stB.stack.size == 2) s!"setcontargs(2,-1): unexpected stack size={stB.stack.size}"
  assert (stB.stack[0]! == vInt 1) s!"setcontargs(2,-1): expected remaining [1]"
  match stB.stack[1]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.stack == #[vInt 2, vInt 3]) s!"setcontargs(2,-1): unexpected captured stack={cdata.stack}"
      assert (cdata.nargs == -1) s!"setcontargs(2,-1): expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"setcontargs(2,-1): expected cont, got {v.pretty}")

  -- copy=0, more=3: sets nargs=3 when nargs was -1.
  let (codeC, stC) ← runInstrWithStack (.setContArgs 0 3) #[.cont cont0]
  assert (codeC == -1) s!"setcontargs(0,3): unexpected exitCode={codeC}"
  match stC.stack[0]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.nargs == 3) s!"setcontargs(0,3): expected nargs=3, got {cdata.nargs}"
  | v => throw (IO.userError s!"setcontargs(0,3): expected cont, got {v.pretty}")

initialize
  Tests.registerTest "continuation/setcontargs" testSetContArgs
  Tests.registerRoundtrip (.setContArgs 0 (-1))
  Tests.registerRoundtrip (.setContArgs 15 14)
  Tests.registerRoundtrip (.setContArgs 15 (-1))

end Tests.Continuation

