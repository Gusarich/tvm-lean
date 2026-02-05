import Tests.Registry

open TvmLean Tests

namespace Tests.Exception

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

def assertExitIsThrow (ctx : String) (code : Int) (exc : Int) : IO Unit := do
  assert (code == (~~~ exc)) s!"{ctx}: expected throw exitCode=~~~{exc}, got {code}"

def testAllExceptionOps : IO Unit := do
  -- THROW: sets stack=[0,exc] and jumps to c2(excQuit) => halts with ~~~exc, leaving [0] on stack.
  let (codeT, stT) ← runInstrWithStack (.throw 7) #[]
  assertExitIsThrow "exc/throw" codeT 7
  assert (stT.stack == #[vInt 0]) s!"exc/throw: expected stack [0], got {stT.stack}"

  -- THROWIF / THROWIFNOT: consumes condition only when not thrown.
  let (codeIf0, stIf0) ← runInstrWithStack (.throwIf 9) #[vInt 0]
  assertExitOk "exc/throwif(false)" codeIf0
  assert (stIf0.stack.isEmpty) s!"exc/throwif(false): expected empty stack"
  let (codeIf1, stIf1) ← runInstrWithStack (.throwIf 9) #[vInt (-1)]
  assertExitIsThrow "exc/throwif(true)" codeIf1 9
  assert (stIf1.stack == #[vInt 0]) s!"exc/throwif(true): expected stack [0]"

  let (codeIfN0, stIfN0) ← runInstrWithStack (.throwIfNot 11) #[vInt 0]
  assertExitIsThrow "exc/throwifnot(false)" codeIfN0 11
  assert (stIfN0.stack == #[vInt 0]) s!"exc/throwifnot(false): expected stack [0]"
  let (codeIfN1, stIfN1) ← runInstrWithStack (.throwIfNot 11) #[vInt 1]
  assertExitOk "exc/throwifnot(true)" codeIfN1
  assert (stIfN1.stack.isEmpty) s!"exc/throwifnot(true): expected empty stack"

  -- THROWARG: stack=[arg,exc] => halts ~~~exc leaving [arg].
  let (codeA, stA) ← runInstrWithStack (.throwArg 13) #[vInt 123]
  assertExitIsThrow "exc/throwarg" codeA 13
  assert (stA.stack == #[vInt 123]) s!"exc/throwarg: expected arg preserved"

  -- THROWARGIF / THROWARGIFNOT: always consumes arg; throws only depending on condition.
  let (codeAI0, stAI0) ← runInstrWithStack (.throwArgIf 17) #[vInt 555, vInt 0]
  assertExitOk "exc/throwargif(false)" codeAI0
  assert (stAI0.stack.isEmpty) s!"exc/throwargif(false): expected empty stack"
  let (codeAI1, stAI1) ← runInstrWithStack (.throwArgIf 17) #[vInt 555, vInt 1]
  assertExitIsThrow "exc/throwargif(true)" codeAI1 17
  assert (stAI1.stack == #[vInt 555]) s!"exc/throwargif(true): expected arg preserved"

  let (codeAIN0, stAIN0) ← runInstrWithStack (.throwArgIfNot 19) #[vInt 777, vInt 0]
  assertExitIsThrow "exc/throwargifnot(false)" codeAIN0 19
  assert (stAIN0.stack == #[vInt 777]) s!"exc/throwargifnot(false): expected arg preserved"
  let (codeAIN1, stAIN1) ← runInstrWithStack (.throwArgIfNot 19) #[vInt 777, vInt 1]
  assertExitOk "exc/throwargifnot(true)" codeAIN1
  assert (stAIN1.stack.isEmpty) s!"exc/throwargifnot(true): expected empty stack"

  -- THROW{ARG}ANY{IF,IFNOT}: excno from stack, plus optional arg + optional condition.
  -- hasParam=false, hasCond=false: always throw (represent as throwCond=false for cp0 encoding).
  let (codeTA0, stTA0) ← runInstrWithStack (.throwAny false false false) #[vInt 42]
  assertExitIsThrow "exc/throwany" codeTA0 42
  assert (stTA0.stack == #[vInt 0]) s!"exc/throwany: expected stack [0]"

  -- hasParam=true, hasCond=true, throwCond=true (THROWARGANYIF): if cond is true => throw, else drop arg.
  let (codeTA1, stTA1) ← runInstrWithStack (.throwAny true true true) #[vInt 999, vInt 77, vInt 1]
  assertExitIsThrow "exc/throwarganyif(true)" codeTA1 77
  assert (stTA1.stack == #[vInt 999]) s!"exc/throwarganyif(true): expected arg preserved"
  let (codeTA2, stTA2) ← runInstrWithStack (.throwAny true true true) #[vInt 999, vInt 77, vInt 0]
  assertExitOk "exc/throwarganyif(false)" codeTA2
  assert (stTA2.stack.isEmpty) s!"exc/throwarganyif(false): expected empty stack"

  -- hasParam=true, hasCond=true, throwCond=false (THROWARGANYIFNOT): if cond is false => throw.
  let (codeTA3, stTA3) ← runInstrWithStack (.throwAny true true false) #[vInt 111, vInt 88, vInt 0]
  assertExitIsThrow "exc/throwarganyifnot(false)" codeTA3 88
  assert (stTA3.stack == #[vInt 111]) s!"exc/throwarganyifnot(false): expected arg preserved"
  let (codeTA4, stTA4) ← runInstrWithStack (.throwAny true true false) #[vInt 111, vInt 88, vInt 1]
  assertExitOk "exc/throwarganyifnot(true)" codeTA4
  assert (stTA4.stack.isEmpty) s!"exc/throwarganyifnot(true): expected empty stack"

  -- TRY: install handler and execute cont; on exception resume after TRY.
  let bodyThrow : Cell ←
    match assembleCp0 [.throw 77] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(bodyThrow) failed: {reprStr e}")
  let handlerDrop : Cell ←
    match assembleCp0 [.drop2] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(handlerDrop) failed: {reprStr e}")
  let contBody : Continuation := .ordinary (Slice.ofCell bodyThrow) (.quit 0) OrdCregs.empty OrdCdata.empty
  let contHandler : Continuation := .ordinary (Slice.ofCell handlerDrop) (.quit 0) OrdCregs.empty OrdCdata.empty
  let (codeTry0, stTry0) ← runProgWithStack [.try_, .pushInt (.num 5)] #[.cont contBody, .cont contHandler]
  assertExitOk "exc/try(throws)" codeTry0
  assert (stTry0.stack == #[vInt 5]) s!"exc/try(throws): expected stack [5], got {stTry0.stack}"

  let bodyOk : Cell ←
    match assembleCp0 [.pushInt (.num 3)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(bodyOk) failed: {reprStr e}")
  let contOk : Continuation := .ordinary (Slice.ofCell bodyOk) (.quit 0) OrdCregs.empty OrdCdata.empty
  let (codeTry1, stTry1) ← runProgWithStack [.try_, .pushInt (.num 5)] #[.cont contOk, .cont contHandler]
  assertExitOk "exc/try(ok)" codeTry1
  assert (stTry1.stack == #[vInt 3, vInt 5]) s!"exc/try(ok): expected stack [3,5], got {stTry1.stack}"

  -- TRYARGS p,r: body sees top p params; on return, keep top r results and restore saved stack.
  let bodyRetMany : Cell ←
    match assembleCp0 [.pushInt (.num 10), .pushInt (.num 20)] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(bodyRetMany) failed: {reprStr e}")
  let contMany : Continuation := .ordinary (Slice.ofCell bodyRetMany) (.quit 0) OrdCregs.empty OrdCdata.empty
  let (codeTA5, stTA5) ←
    runProgWithStack [.tryArgs 2 1] #[vInt 1, vInt 2, vInt 3, .cont contMany, .cont contHandler]
  assertExitOk "exc/tryargs(ret1)" codeTA5
  -- Saved stack was [1]; params were [2,3]; body pushed 10,20 on top => top1 is 20; result stack [1,20].
  assert (stTA5.stack == #[vInt 1, vInt 20]) s!"exc/tryargs(ret1): got {stTA5.stack}"

  let bodyThrowArg : Cell ←
    match assembleCp0 [.throwArg 99] with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"assembleCp0(bodyThrowArg) failed: {reprStr e}")
  let contThrowArg : Continuation := .ordinary (Slice.ofCell bodyThrowArg) (.quit 0) OrdCregs.empty OrdCdata.empty
  let (codeTA6, stTA6) ←
    runProgWithStack [.tryArgs 1 0, .pushInt (.num 7)] #[vInt 123, vInt 456, .cont contThrowArg, .cont contHandler]
  assertExitOk "exc/tryargs(throws)" codeTA6
  -- Body throws; handler drops 2; TRYARGS resumes after it, with saved stack preserved and retVals=0 (keeps none).
  assert (stTA6.stack == #[vInt 123, vInt 7]) s!"exc/tryargs(throws): got {stTA6.stack}"

initialize
  Tests.registerTest "exception/all" testAllExceptionOps
  Tests.registerRoundtrip (.throw 0)
  Tests.registerRoundtrip (.throw 63)
  Tests.registerRoundtrip (.throw 1000)
  Tests.registerRoundtrip (.throwIf 0)
  Tests.registerRoundtrip (.throwIf 63)
  Tests.registerRoundtrip (.throwIf 1000)
  Tests.registerRoundtrip (.throwArg 0)
  Tests.registerRoundtrip (.throwArg 1000)
  Tests.registerRoundtrip (.throwArgIf 1000)
  Tests.registerRoundtrip (.throwArgIfNot 1000)
  Tests.registerRoundtrip (.throwAny false false false)
  Tests.registerRoundtrip (.throwAny true true true)
  Tests.registerRoundtrip (.throwAny true true false)
  Tests.registerRoundtrip (.tryArgs 0 0)
  Tests.registerRoundtrip (.tryArgs 15 15)

end Tests.Exception
