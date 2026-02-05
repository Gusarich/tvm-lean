import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.VarargsReturn

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

def runProgWithStack (prog : List Instr) (stack : Stack) (fuel : Nat := 120) : IO (Int × VmState) := do
  let codeCell ←
    match assembleCp0 prog with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0 failed: {reprStr e}")
  let base : VmState := VmState.initial codeCell
  let st0 : VmState := { base with stack := stack }
  match VmState.run fuel st0 with
  | .continue _ => throw (IO.userError s!"prog: did not halt")
  | .halt exitCode st => pure (exitCode, st)

def vInt (n : Int) : Value := .int (.num n)

def assertExitOk (ctx : String) (code : Int) : IO Unit := do
  assert (code == -1) s!"{ctx}: unexpected exitCode={code}"

def testVarargsReturnOps : IO Unit := do
  -- A minimal continuation to use in tests.
  let code0 ←
    match assembleCp0 [] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(empty) failed: {reprStr e}")
  let cont0 : Continuation := .ordinary (Slice.ofCell code0) (.quit 0) OrdCregs.empty OrdCdata.empty

  -- SETNUMVARARGS: pop `more`, pop `cont`, push updated cont.
  let (codeS0, stS0) ← runInstrWithStack .setNumVarArgs #[vInt 1, .cont cont0, vInt (-1)]
  assertExitOk "cont/setnumvarargs(-1)" codeS0
  assert (stS0.stack.size == 2) s!"cont/setnumvarargs(-1): expected stack size 2"
  assert (stS0.stack[0]! == vInt 1) s!"cont/setnumvarargs(-1): value changed"
  match stS0.stack[1]! with
  | .cont k => assert (k == cont0) s!"cont/setnumvarargs(-1): continuation changed"
  | v => throw (IO.userError s!"cont/setnumvarargs(-1): expected cont, got {v.pretty}")

  let (codeS1, stS1) ← runInstrWithStack .setNumVarArgs #[.cont cont0, vInt 3]
  assertExitOk "cont/setnumvarargs(3)" codeS1
  match stS1.stack[0]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.nargs == 3) s!"cont/setnumvarargs(3): expected nargs=3, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/setnumvarargs(3): expected ordinary cont, got {v.pretty}")

  let contNargs5 : Continuation :=
    .ordinary (Slice.ofCell code0) (.quit 0) OrdCregs.empty { OrdCdata.empty with nargs := 5 }
  let (codeS2, stS2) ← runInstrWithStack .setNumVarArgs #[.cont contNargs5, vInt 3]
  assertExitOk "cont/setnumvarargs(nargs=5,more=3)" codeS2
  match stS2.stack[0]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.nargs == 0x40000000) s!"cont/setnumvarargs(nargs=5,more=3): expected nargs=0x40000000, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/setnumvarargs(nargs=5,more=3): expected ordinary cont, got {v.pretty}")

  let contNargs2 : Continuation :=
    .ordinary (Slice.ofCell code0) (.quit 0) OrdCregs.empty { OrdCdata.empty with nargs := 2 }
  let (codeS3, stS3) ← runInstrWithStack .setNumVarArgs #[.cont contNargs2, vInt 3]
  assertExitOk "cont/setnumvarargs(nargs=2,more=3)" codeS3
  match stS3.stack[0]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.nargs == 2) s!"cont/setnumvarargs(nargs=2,more=3): expected nargs=2, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/setnumvarargs(nargs=2,more=3): expected ordinary cont, got {v.pretty}")

  -- RETURNARGS: copy `(depth-count)` bottom items into c0 closure stack, leaving top `count` on stack.
  let progReturnArgs : List Instr := [ .pushCtr 0, .returnArgs 2, .pushCtr 0, .xchg0 1, .popCtr 0 ]
  let (codeR0, stR0) ← runProgWithStack progReturnArgs #[vInt 1, vInt 2, vInt 3]
  assertExitOk "cont/returnargs" codeR0
  assert (stR0.stack.size == 2) s!"cont/returnargs: expected stack size 2, got {stR0.stack.size}"
  assert (stR0.stack[0]! == vInt 3) s!"cont/returnargs: expected top value 3"
  match stR0.stack[1]! with
  | .cont (.envelope ext _ cdata) =>
      assert (ext == .quit 0) s!"cont/returnargs: expected ext=quit0"
      assert (cdata.stack == #[vInt 1, vInt 2]) s!"cont/returnargs: unexpected captured stack={cdata.stack}"
      assert (cdata.nargs == -1) s!"cont/returnargs: expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/returnargs: expected envelope cont, got {v.pretty}")

  -- RETURNVARARGS: pop count from stack first (0..255), then behave like RETURNARGS.
  let progReturnVarArgs : List Instr := [ .pushCtr 0, .pushInt (.num 2), .returnVarArgs, .pushCtr 0, .xchg0 1, .popCtr 0 ]
  let (codeRV, stRV) ← runProgWithStack progReturnVarArgs #[vInt 1, vInt 2, vInt 3]
  assertExitOk "cont/returnvarargs" codeRV
  assert (stRV.stack.size == 2) s!"cont/returnvarargs: expected stack size 2, got {stRV.stack.size}"
  assert (stRV.stack[0]! == vInt 3) s!"cont/returnvarargs: expected top value 3"
  match stRV.stack[1]! with
  | .cont (.envelope ext _ cdata) =>
      assert (ext == .quit 0) s!"cont/returnvarargs: expected ext=quit0"
      assert (cdata.stack == #[vInt 1, vInt 2]) s!"cont/returnvarargs: unexpected captured stack={cdata.stack}"
      assert (cdata.nargs == -1) s!"cont/returnvarargs: expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/returnvarargs: expected envelope cont, got {v.pretty}")

  -- RETVARARGS: pop `retvals` then return.
  let (codeV0, stV0) ← runInstrWithStack .retVarArgs #[vInt 10, vInt 20, vInt 1]
  assertExitOk "flow/retvarargs" codeV0
  assert (stV0.stack == #[vInt 20]) s!"flow/retvarargs: expected passing only 1 value"

  -- RETDATA: push remaining code slice, then return.
  let progRetData : List Instr := [ .retData, .pushInt (.num 99) ]
  let (codeD0, stD0) ← runProgWithStack progRetData #[]
  assertExitOk "flow/retdata" codeD0
  assert (stD0.stack.size == 1) s!"flow/retdata: expected stack size 1"
  match stD0.stack[0]! with
  | .slice s =>
      assert (s.bitsRemaining > 0) s!"flow/retdata: expected non-empty slice"
      match decodeCp0WithBits s with
      | .ok (instr, _, _) =>
          assert (instr == .pushInt (.num 99)) s!"flow/retdata: expected pushed code to start with PUSHINT 99, got {instr.pretty}"
      | .error e =>
          throw (IO.userError s!"flow/retdata: decode failed: {reprStr e}")
  | v =>
      throw (IO.userError s!"flow/retdata: expected slice, got {v.pretty}")

initialize
  Tests.registerTest "continuation/varargs-return" testVarargsReturnOps
  Tests.registerRoundtrip .setNumVarArgs
  Tests.registerRoundtrip (.returnArgs 0)
  Tests.registerRoundtrip (.returnArgs 15)
  Tests.registerRoundtrip .returnVarArgs
  Tests.registerRoundtrip .retVarArgs
  Tests.registerRoundtrip .retData

end Tests.Continuation.VarargsReturn
