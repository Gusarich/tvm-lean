import Tests.Registry

open TvmLean Tests

namespace Tests.Continuation.CallccJump

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

def testCallccJumpOps : IO Unit := do
  -- CALLCC: push current continuation and jump to provided cont.
  let progCallcc : List Instr := [ .pushCtr 0, .callcc ]
  let (codeC, stC) ← runProgWithStack progCallcc #[vInt 111]
  assertExitOk "cont/callcc" codeC
  assert (stC.stack.size == 2) s!"cont/callcc: expected stack size 2"
  assert (stC.stack[0]! == vInt 111) s!"cont/callcc: value changed"
  match stC.stack[1]! with
  | .cont (.ordinary code _ cregs cdata) =>
      assert (code.bitsRemaining == 0) s!"cont/callcc: expected empty remainder code"
      assert (cdata.stack.isEmpty) s!"cont/callcc: expected empty closure stack"
      assert (cdata.nargs == -1) s!"cont/callcc: expected nargs=-1, got {cdata.nargs}"
      assert (cregs.c0 == some (.quit 0)) s!"cont/callcc: expected saved c0=quit0"
      assert (cregs.c1 == some (.quit 1)) s!"cont/callcc: expected saved c1=quit1"
  | v => throw (IO.userError s!"cont/callcc: expected cont, got {v.pretty}")

  -- CALLCCARGS: keep top `params` on stack, store the rest in cc closure stack.
  let progCallccArgs : List Instr :=
    [ .pushInt (.num 1)
    , .pushInt (.num 2)
    , .pushInt (.num 3)
    , .pushCtr 0
    , .callccArgs 2 (-1)
    ]
  let (codeCA, stCA) ← runProgWithStack progCallccArgs #[]
  assertExitOk "cont/callccargs" codeCA
  assert (stCA.stack.size == 3) s!"cont/callccargs: expected stack size 3, got {stCA.stack.size}"
  assert (stCA.stack[0]! == vInt 2) s!"cont/callccargs: expected 2 kept"
  assert (stCA.stack[1]! == vInt 3) s!"cont/callccargs: expected 3 kept"
  match stCA.stack[2]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.stack == #[vInt 1]) s!"cont/callccargs: expected captured [1], got {cdata.stack}"
      assert (cdata.nargs == -1) s!"cont/callccargs: expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/callccargs: expected cont, got {v.pretty}")

  -- CALLCCVARARGS: params/retvals from stack.
  let progCallccVar : List Instr :=
    [ .pushInt (.num 1)
    , .pushInt (.num 2)
    , .pushInt (.num 3)
    , .pushCtr 0
    , .pushInt (.num 2)    -- params
    , .pushInt (.num (-1)) -- retvals
    , .callccVarArgs
    ]
  let (codeCV, stCV) ← runProgWithStack progCallccVar #[]
  assertExitOk "cont/callccvarargs" codeCV
  assert (stCV.stack.size == 3) s!"cont/callccvarargs: expected stack size 3"
  assert (stCV.stack[0]! == vInt 2) s!"cont/callccvarargs: expected 2 kept"
  assert (stCV.stack[1]! == vInt 3) s!"cont/callccvarargs: expected 3 kept"
  match stCV.stack[2]! with
  | .cont (.ordinary _ _ _ cdata) =>
      assert (cdata.stack == #[vInt 1]) s!"cont/callccvarargs: expected captured [1], got {cdata.stack}"
      assert (cdata.nargs == -1) s!"cont/callccvarargs: expected nargs=-1, got {cdata.nargs}"
  | v => throw (IO.userError s!"cont/callccvarargs: expected cont, got {v.pretty}")

  -- JMPXDATA: push remaining code slice and jump.
  let progJmpxData : List Instr := [ .pushCtr 0, .jmpxData, .pushInt (.num 99) ]
  let (codeJD, stJD) ← runProgWithStack progJmpxData #[]
  assertExitOk "flow/jmpxdata" codeJD
  assert (stJD.stack.size == 1) s!"flow/jmpxdata: expected stack size 1"
  match stJD.stack[0]! with
  | .slice s =>
      match decodeCp0WithBits s with
      | .ok (instr, _, _) =>
          assert (instr == .pushInt (.num 99)) s!"flow/jmpxdata: expected pushed code to start with PUSHINT 99, got {instr.pretty}"
      | .error e =>
          throw (IO.userError s!"flow/jmpxdata: decode failed: {reprStr e}")
  | v => throw (IO.userError s!"flow/jmpxdata: expected slice, got {v.pretty}")

  -- JMPXVARARGS: params from stack controls how many args are passed.
  let progJmpxVar : List Instr :=
    [ .pushInt (.num 1)
    , .pushInt (.num 2)
    , .pushInt (.num 3)
    , .pushCtr 0
    , .pushInt (.num 2)
    , .jmpxVarArgs
    ]
  let (codeJV, stJV) ← runProgWithStack progJmpxVar #[]
  assertExitOk "flow/jmpxvarargs" codeJV
  assert (stJV.stack == #[vInt 2, vInt 3]) s!"flow/jmpxvarargs: expected [2,3], got {stJV.stack}"

  -- CALLXVARARGS: params/retvals from stack, then call.
  let progCallxVar : List Instr :=
    [ .pushInt (.num 1)
    , .pushInt (.num 2)
    , .pushInt (.num 3)
    , .pushCtr 0
    , .pushInt (.num 2)    -- params
    , .pushInt (.num (-1)) -- retvals
    , .callxVarArgs
    ]
  let (codeXV, stXV) ← runProgWithStack progCallxVar #[]
  assertExitOk "flow/callxvarargs" codeXV
  assert (stXV.stack == #[vInt 2, vInt 3]) s!"flow/callxvarargs: expected [2,3], got {stXV.stack}"

initialize
  Tests.registerTest "continuation/callcc-jumps" testCallccJumpOps
  Tests.registerRoundtrip .callcc
  Tests.registerRoundtrip .jmpxData
  Tests.registerRoundtrip (.callccArgs 0 (-1))
  Tests.registerRoundtrip (.callccArgs 15 14)
  Tests.registerRoundtrip .callxVarArgs
  Tests.registerRoundtrip .jmpxVarArgs
  Tests.registerRoundtrip .callccVarArgs

end Tests.Continuation.CallccJump

