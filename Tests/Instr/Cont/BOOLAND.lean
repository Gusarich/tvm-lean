import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.BOOLAND

/-
BOOLAND (`exec_compos(mask=1)`) branch map:
- dispatch: `.boolAnd` vs fallback to `next`;
- upfront `check_underflow(2)` before any `pop_cont`;
- pop order: top value-cont first, then target-cont;
- define branch: `define_c0` sets only when `c0` is missing
  (ordinary/envelope/forced-envelope paths).
-/

private def boolAndId : InstrId := { name := "BOOLAND" }

private def boolAndInstr : Instr := .boolAnd

private def dispatchSentinel : Int := 51723

private def refCellA : Cell :=
  Cell.mkOrdinary (natToBits 0x11 6) #[]

private def refCellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[refCellA]

private def sliceA : Slice :=
  Slice.ofCell refCellA

private def sliceB : Slice :=
  Slice.ofCell refCellB

private def mkOrdCont
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary (Slice.ofCell Cell.empty) saved cregs cdata

private def mkEnvCont
    (ext : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .envelope ext cregs cdata

private def mkBoolAndStack
    (below : Array Value)
    (cont : Continuation)
    (val : Continuation) : Array Value :=
  below ++ #[.cont cont, .cont val]

private def mkTopTypeStack
    (below : Array Value)
    (cont : Continuation)
    (badTop : Value) : Array Value :=
  below ++ #[.cont cont, badTop]

private def mkSecondTypeStack
    (below : Array Value)
    (badSecond : Value)
    (val : Continuation) : Array Value :=
  below ++ #[badSecond, .cont val]

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[boolAndInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := boolAndId
    program := program
    initStack := stack
    fuel := fuel }

private def runBoolAndDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContBoolAnd boolAndInstr stack

private def runBoolAndDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContBoolAnd instr (VM.push (intV dispatchSentinel)) stack

private def runBoolAndRaw
    (stack : Array Value)
    (cc : Continuation := .quit 0) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack, cc := cc }
  (execInstrContBoolAnd boolAndInstr (pure ())).run st0

private def expectTopCont
    (label : String)
    (stack : Array Value)
    (k : Continuation → IO Unit) : IO Unit := do
  match stack.back? with
  | some (.cont cont) =>
      k cont
  | some v =>
      throw (IO.userError s!"{label}: expected top continuation, got {reprStr v}")
  | none =>
      throw (IO.userError s!"{label}: expected non-empty stack")

private def valQuitA : Continuation := .quit 101
private def valQuitB : Continuation := .quit 202
private def valOrd : Continuation := mkOrdCont (.quit 303)
private def valEnv : Continuation := mkEnvCont (.quit 404)
private def valWhile : Continuation := .whileCond (.quit 5) (.quit 6) (.quit 7)

private def targetQuit : Continuation := .quit 11
private def targetOrdNoC0 : Continuation := mkOrdCont (.quit 12)
private def targetOrdWithC0 : Continuation :=
  mkOrdCont (.quit 13) { OrdCregs.empty with c0 := some (.quit 900) }
private def targetOrdWithC1 : Continuation :=
  mkOrdCont (.quit 14) { OrdCregs.empty with c1 := some (.quit 901) }
private def targetOrdWithBoth : Continuation :=
  mkOrdCont (.quit 15) { OrdCregs.empty with c0 := some (.quit 902), c1 := some (.quit 903) }
private def targetEnvNoC0 : Continuation := mkEnvCont (.quit 16)
private def targetEnvWithC0 : Continuation :=
  mkEnvCont (.quit 17) { OrdCregs.empty with c0 := some (.quit 904) }
private def targetEnvWithC1 : Continuation :=
  mkEnvCont (.quit 18) { OrdCregs.empty with c1 := some (.quit 905) }
private def targetWhile : Continuation := .whileBody (.quit 19) (.quit 20) (.quit 21)
private def targetRepeat : Continuation := .repeatBody (.quit 22) (.quit 23) 2
private def targetAgain : Continuation := .againBody (.quit 24)

private def noiseA : Array Value :=
  #[.null, intV 7]

private def noiseB : Array Value :=
  #[.cell refCellA, .slice sliceA]

private def noiseC : Array Value :=
  #[.builder Builder.empty, .tuple #[]]

private def noiseD : Array Value :=
  #[intV maxInt257, intV minInt257, .cell refCellB]

private def k0 : Continuation := .quit 0

private def mkK0Stack (below : Array Value := #[]) : Array Value :=
  mkBoolAndStack below k0 k0

private def boolAndFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/success/",
      "ok/program-tail/",
      "ok/order/",
      "ok/branch/",
      "ok/noise/",
      "err/underflow/",
      "err/type/",
      "err/order/"
    ]
    mutationModes := #[
      0, 0, 0, 0,
      1, 1, 1,
      3, 3, 3,
      2,
      4
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := boolAndId
  unit := #[
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback"
          (runBoolAndDispatchFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/match"
          (runBoolAndDirect (mkBoolAndStack #[intV 9] targetQuit valQuitA))
          #[intV 9, .cont (targetQuit.defineC0 valQuitA)] }
    ,
    { name := "unit/error/underflow-precedes-type-on-singleton"
      run := do
        expectErr "underflow/empty" (runBoolAndDirect #[]) .stkUnd
        expectErr "underflow/one-cont" (runBoolAndDirect #[.cont (.quit 0)]) .stkUnd
        expectErr "underflow/one-null" (runBoolAndDirect #[.null]) .stkUnd
        let singleton : Array Value := #[.null]
        let (res, st) := runBoolAndRaw singleton (.quit 99)
        match res with
        | .error .stkUnd =>
            if st.stack == singleton then
              pure ()
            else
              throw (IO.userError s!"singleton-underflow mutated stack: {reprStr st.stack}")
        | .error e =>
            throw (IO.userError s!"singleton-underflow: expected stkUnd, got {e}")
        | .ok _ =>
            throw (IO.userError "singleton-underflow: expected stkUnd, got success") }
    ,
    { name := "unit/error/top-type-pop-consumes-top-only"
      run := do
        let st0 : Array Value := #[intV 55, .cont targetQuit, .null]
        let (res, st) := runBoolAndRaw st0 (.quit 71)
        match res with
        | .error .typeChk =>
            if st.stack == #[intV 55, .cont targetQuit] then
              pure ()
            else
              throw (IO.userError s!"top-type stack mismatch: {reprStr st.stack}")
        | .error e =>
            throw (IO.userError s!"top-type: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "top-type: expected typeChk, got success") }
    ,
    { name := "unit/error/second-type-after-val-pop-consumes-both"
      run := do
        let st0 : Array Value := #[intV 66, .null, .cont valQuitA]
        let (res, st) := runBoolAndRaw st0 (.quit 72)
        match res with
        | .error .typeChk =>
            if st.stack == #[intV 66] then
              pure ()
            else
              throw (IO.userError s!"second-type stack mismatch: {reprStr st.stack}")
        | .error e =>
            throw (IO.userError s!"second-type: expected typeChk, got {e}")
        | .ok _ =>
            throw (IO.userError "second-type: expected typeChk, got success") }
    ,
    { name := "unit/success/quit-target-forces-envelope-and-sets-c0"
      run := do
        let ccInit : Continuation := .quit 333
        let (res, st) := runBoolAndRaw (mkBoolAndStack #[intV 3] targetQuit valQuitA) ccInit
        match res with
        | .error e =>
            throw (IO.userError s!"quit-target: expected success, got {e}")
        | .ok _ =>
            if st.cc != ccInit then
              throw (IO.userError s!"quit-target: cc changed unexpectedly to {reprStr st.cc}")
            expectTopCont "quit-target/top" st.stack fun out => do
              match out with
              | .envelope ext cregs _ =>
                  if ext != targetQuit then
                    throw (IO.userError s!"quit-target/ext mismatch: got {reprStr ext}")
                  else if cregs.c0 != some valQuitA then
                    throw (IO.userError s!"quit-target/c0 mismatch: got {reprStr cregs.c0}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"quit-target: expected envelope, got {reprStr out}") }
    ,
    { name := "unit/success/ordinary-preserves-existing-c0"
      run := do
        let (res, st) := runBoolAndRaw (mkBoolAndStack #[] targetOrdWithC0 valQuitB)
        match res with
        | .error e =>
            throw (IO.userError s!"ordinary-existing-c0: expected success, got {e}")
        | .ok _ =>
            expectTopCont "ordinary-existing-c0/top" st.stack fun out => do
              match out with
              | .ordinary _ _ cregs _ =>
                  if cregs.c0 != some (.quit 900) then
                    throw (IO.userError s!"ordinary-existing-c0/c0 mismatch: got {reprStr cregs.c0}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"ordinary-existing-c0: expected ordinary, got {reprStr out}") }
    ,
    { name := "unit/success/ordinary-sets-c0-and-preserves-c1"
      run := do
        let (res, st) := runBoolAndRaw (mkBoolAndStack #[] targetOrdWithC1 valQuitA)
        match res with
        | .error e =>
            throw (IO.userError s!"ordinary-set-c0: expected success, got {e}")
        | .ok _ =>
            expectTopCont "ordinary-set-c0/top" st.stack fun out => do
              match out with
              | .ordinary _ _ cregs _ =>
                  if cregs.c0 != some valQuitA then
                    throw (IO.userError s!"ordinary-set-c0/c0 mismatch: got {reprStr cregs.c0}")
                  else if cregs.c1 != some (.quit 901) then
                    throw (IO.userError s!"ordinary-set-c0/c1 mismatch: got {reprStr cregs.c1}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"ordinary-set-c0: expected ordinary, got {reprStr out}") }
    ,
    { name := "unit/success/envelope-set-vs-preserve-c0"
      run := do
        let (resSet, stSet) := runBoolAndRaw (mkBoolAndStack #[] targetEnvNoC0 valQuitA)
        match resSet with
        | .error e =>
            throw (IO.userError s!"envelope-set: expected success, got {e}")
        | .ok _ =>
            expectTopCont "envelope-set/top" stSet.stack fun out => do
              match out with
              | .envelope _ cregs _ =>
                  if cregs.c0 != some valQuitA then
                    throw (IO.userError s!"envelope-set/c0 mismatch: got {reprStr cregs.c0}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"envelope-set: expected envelope, got {reprStr out}")
        let (resKeep, stKeep) := runBoolAndRaw (mkBoolAndStack #[] targetEnvWithC0 valQuitB)
        match resKeep with
        | .error e =>
            throw (IO.userError s!"envelope-preserve: expected success, got {e}")
        | .ok _ =>
            expectTopCont "envelope-preserve/top" stKeep.stack fun out => do
              match out with
              | .envelope _ cregs _ =>
                  if cregs.c0 != some (.quit 904) then
                    throw (IO.userError s!"envelope-preserve/c0 mismatch: got {reprStr cregs.c0}")
                  else
                    pure ()
              | _ =>
                  throw (IO.userError s!"envelope-preserve: expected envelope, got {reprStr out}") }
  ]
  oracle := #[
    -- Success coverage with token-safe init stacks (only `.cont (.quit 0)` continuations).
    mkCase "ok/success/basic-k0"
      (mkK0Stack #[]),
    mkCase "ok/success/noise-null-int"
      (mkK0Stack noiseA),
    mkCase "ok/success/noise-cell"
      (mkK0Stack #[.cell refCellA]),
    mkCase "ok/success/noise-slice"
      (mkK0Stack #[.slice sliceA]),
    mkCase "ok/success/noise-builder"
      (mkK0Stack #[.builder Builder.empty]),
    mkCase "ok/success/noise-empty-tuple"
      (mkK0Stack #[.tuple #[]]),
    mkCase "ok/success/noise-mixed-a"
      (mkK0Stack #[.cell refCellA, .slice sliceB, .null]),
    mkCase "ok/success/noise-mixed-b"
      (mkK0Stack #[intV maxInt257, intV minInt257, .builder Builder.empty]),
    mkCase "ok/program-tail/push-exec"
      (mkK0Stack noiseA)
      #[boolAndInstr, .pushInt (.num 77)],
    mkCase "ok/program-tail/pop-exec"
      (mkK0Stack noiseB)
      #[boolAndInstr, .pop 0],
    mkCase "ok/program-tail/nop-chain"
      (mkK0Stack noiseC)
      #[boolAndInstr, .nop, .nop],
    mkCase "ok/order/two-successive-booland"
      #[.cont k0, .cont k0, .cont k0]
      #[boolAndInstr, boolAndInstr],

    -- Explicit branch outcomes beyond trivial quit-target path.
    mkCase "ok/branch/ordinary-target-via-bless"
      #[.cont k0, .slice sliceA]
      #[.bless, .xchg0 1, boolAndInstr],
    mkCase "ok/branch/ordinary-existing-c0-via-bless-chain"
      #[.slice sliceB, .cont k0, .slice sliceA]
      #[.bless, .xchg0 1, boolAndInstr, .xchg0 1, .bless, boolAndInstr],
    mkCase "ok/branch/envelope-existing-c0-via-two-stage"
      #[.cont k0, .cont k0, .cont k0]
      #[boolAndInstr, .xchg0 1, boolAndInstr],
    mkCase "ok/branch/value-from-bless"
      #[.cont k0, .slice sliceA]
      #[.bless, boolAndInstr],
    mkCase "ok/branch/value-from-bless-with-noise"
      #[intV 7, .null, .cont k0, .slice sliceB]
      #[.bless, boolAndInstr],
    mkCase "ok/branch/value-and-target-from-bless"
      #[.cont k0, .slice sliceA, .slice sliceB]
      #[.bless, .xchg0 1, .bless, boolAndInstr],

    -- Underflow/error-order coverage (`check_underflow(2)` before any pop/type checks).
    mkCase "err/underflow/empty" #[],
    mkCase "err/underflow/one-int" #[intV 1],
    mkCase "err/underflow/one-null" #[.null],
    mkCase "err/underflow/one-cell" #[.cell refCellA],
    mkCase "err/underflow/one-slice" #[.slice sliceA],
    mkCase "err/underflow/one-builder" #[.builder Builder.empty],
    mkCase "err/underflow/one-cont-k0" #[.cont k0],
    mkCase "err/order/one-builder-prefers-underflow-with-tail"
      #[.builder Builder.empty]
      #[boolAndInstr, .pushInt (.num 999)],

    -- Type errors at first pop (`val` expected on top).
    mkCase "err/type/top-null-not-cont"
      (mkTopTypeStack #[] k0 .null),
    mkCase "err/type/top-int-not-cont"
      (mkTopTypeStack noiseA k0 (intV 5)),
    mkCase "err/type/top-cell-not-cont"
      (mkTopTypeStack noiseB k0 (.cell refCellA)),
    mkCase "err/type/top-slice-not-cont"
      (mkTopTypeStack noiseC k0 (.slice sliceA)),
    mkCase "err/type/top-builder-not-cont"
      (mkTopTypeStack noiseD k0 (.builder Builder.empty)),
    mkCase "err/type/top-tuple-not-cont"
      (mkTopTypeStack #[] k0 (.tuple #[])),

    -- Type errors at second pop (`cont` expected under a valid top continuation).
    mkCase "err/type/second-null"
      (mkSecondTypeStack #[] .null k0),
    mkCase "err/type/second-int"
      (mkSecondTypeStack noiseA (intV (-9)) k0),
    mkCase "err/type/second-cell"
      (mkSecondTypeStack noiseB (.cell refCellB) k0),
    mkCase "err/type/second-slice"
      (mkSecondTypeStack noiseC (.slice sliceB) k0),
    mkCase "err/type/second-builder"
      (mkSecondTypeStack noiseD (.builder Builder.empty) k0),
    mkCase "err/type/second-tuple"
      (mkSecondTypeStack #[] (.tuple #[]) k0),

    -- Explicit tail-skipping and pop-order/type-order behavior.
    mkCase "err/type/top-with-tail-skipped"
      (mkTopTypeStack noiseA k0 (.cell refCellA))
      #[boolAndInstr, .pushInt (.num 999)],
    mkCase "err/type/second-with-tail-skipped"
      (mkSecondTypeStack noiseB (.slice sliceA) k0)
      #[boolAndInstr, .pushInt (.num 999)],
    mkCase "err/order/top-type-before-second-type"
      #[.cell refCellA, .null]
      #[boolAndInstr],
    mkCase "ok/noise/max-min-int-preserved"
      (mkK0Stack #[intV maxInt257, intV minInt257, .null])
  ]
  fuzz := #[ mkContMutationFuzzSpecWithProfile boolAndId boolAndFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.BOOLAND
