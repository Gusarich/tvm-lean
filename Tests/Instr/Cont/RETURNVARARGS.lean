import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.RETURNVARARGS

private def returnVarArgsId : InstrId := { name := "RETURNVARARGS" }

private def returnVarArgsInstr : Instr := .returnVarArgs

private def dispatchSentinel : Int := 49080

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def q0 : Value := .cont (.quit 0)

private def mkOrdCont
    (code : Slice := Slice.ofCell Cell.empty)
    (saved : Continuation := .quit 0)
    (cregs : OrdCregs := OrdCregs.empty)
    (cdata : OrdCdata := OrdCdata.empty) : Continuation :=
  .ordinary code saved cregs cdata

private def c0NeedArgs (n : Int) : Continuation :=
  .envelope (.quit 1) OrdCregs.empty { stack := #[], nargs := n }

private def withCount (below : Array Value) (count : Int) : Array Value :=
  below ++ #[intV count]

private def intStackAsc (n : Nat) : Array Value :=
  Id.run do
    let mut out : Array Value := #[]
    for i in [0:n] do
      out := out.push (intV (Int.ofNat (i + 1)))
    out

private def range254 : Array Value := intStackAsc 254
private def range255 : Array Value := intStackAsc 255
private def range256 : Array Value := intStackAsc 256

private def runReturnVarArgsDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContReturnArgs returnVarArgsInstr stack

private def runReturnVarArgsFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContReturnArgs instr (VM.push (intV dispatchSentinel)) stack

private def runReturnVarArgsRaw
    (stack : Array Value)
    (cc : Continuation := mkOrdCont)
    (c0 : Continuation := .quit 0)
    (c1 : Continuation := .quit 1)
    (instr : Instr := returnVarArgsInstr) : Except Excno Unit × VmState :=
  let regs0 := Regs.initial
  let st0 : VmState :=
    { (VmState.initial Cell.empty) with
      stack := stack
      cc := cc
      regs := { regs0 with c0 := c0, c1 := c1 } }
  (execInstrContReturnArgs instr (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e => throw (IO.userError s!"{label}: expected success, got {e}")

private def expectRawErr
    (label : String)
    (out : Except Excno Unit × VmState)
    (expected : Excno) : IO VmState := do
  let (res, st) := out
  match res with
  | .error e =>
      if e = expected then
        pure st
      else
        throw (IO.userError s!"{label}: expected {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected error {expected}, got success")

private def expectDecodeErr
    (label : String)
    (code : Cell)
    (expected : Excno) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected decode error {expected}, got {e}")
  | .ok (instr, bits, _) =>
      throw (IO.userError s!"{label}: expected decode error, got {reprStr instr} ({bits} bits)")

private def expectDecodeReturnVarArgs
    (label : String)
    (code : Cell)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != .returnVarArgs then
        throw (IO.userError s!"{label}: expected .returnVarArgs, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected successful decode, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[returnVarArgsInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := returnVarArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := returnVarArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progSetC0FromC1 (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .popCtr 0, .returnVarArgs] ++ tail

private def progSetC0Nargs (n : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushCtr 1, .pushInt (.num n), .setNumVarArgs, .popCtr 0, .returnVarArgs] ++ tail

private def progSetC0Captured (capture : Int) (more : Int) (tail : Array Instr := #[]) : Array Instr :=
  #[.pushInt (.num capture), .pushCtr 1, .pushInt (.num 1), .pushInt (.num more), .setContVarArgs, .popCtr 0,
    .returnVarArgs] ++ tail

private def returnVarArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def returnVarArgsTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed10 >>> 1) 15) #[]

private def returnVarArgsOracleFamilies : Array String :=
  #[
    "ok/basic/",
    "ok/order/",
    "ok/c0-from-c1/",
    "ok/c0-nargs",
    "err/c0-nargs",
    "ok/captured/",
    "err/captured/",
    "err/underflow-",
    "err/type-",
    "err/range-",
    "err/decode-"
  ]

private def returnVarArgsFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := returnVarArgsOracleFamilies
    mutationModes := #[0, 0, 0, 0, 2, 2, 2, 4, 4, 1, 1, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Basic stack reshape behavior.
  mkCase "ok/basic/pass0-empty" (withCount #[] 0),
  mkCase "ok/basic/pass0-drop-one" (withCount #[intV 7] 0),
  mkCase "ok/basic/pass0-drop-mixed"
    (withCount #[.null, .cell cellA, .slice sliceB] 0),
  mkCase "ok/basic/pass1-exact-one" (withCount #[intV 7] 1),
  mkCase "ok/basic/pass1-keep-top-of-two" (withCount #[intV 7, intV 8] 1),
  mkCase "ok/basic/pass2-exact-two" (withCount #[intV 7, intV 8] 2),
  mkCase "ok/basic/pass2-drop-bottom-of-three" (withCount #[intV 7, intV 8, intV 9] 2),
  mkCase "ok/basic/pass3-keep-top-three-mixed"
    (withCount #[intV 1, .null, .cell cellA, .slice sliceA] 3),
  mkCase "ok/basic/pass254-exact-depth" (withCount range254 254),
  mkCase "ok/basic/pass254-drop-bottom" (withCount range255 254),
  mkCase "ok/basic/pass255-exact-depth" (withCount range255 255),
  mkCase "ok/basic/pass255-drop-bottom" (withCount range256 255),

  -- Ordering: count can be produced by prior instructions; tail executes (no jump).
  mkCase "ok/order/program-push-count0"
    #[intV 5]
    #[.pushInt (.num 0), returnVarArgsInstr],
  mkCase "ok/order/program-push-count2"
    #[intV 1, intV 2, intV 3]
    #[.pushInt (.num 2), returnVarArgsInstr],
  mkCase "ok/order/tail-exec-push"
    (withCount #[intV 9] 0)
    #[returnVarArgsInstr, .pushInt (.num 77)],
  mkCase "ok/order/tail-exec-add"
    (withCount #[intV 2, intV 3, intV 4] 2)
    #[returnVarArgsInstr, .add],
  mkCase "ok/order/pass2-preserves-top-order"
    (withCount #[intV 1, intV 2, intV 3, intV 4] 2),
  mkCase "ok/order/pass2-mixed-types"
    (withCount #[.cell cellA, .slice sliceA, .builder Builder.empty] 2),

  -- c0 retarget to c1 (quit1), then RETURNVARARGS wraps/updates c0 cdata.
  mkCase "ok/c0-from-c1/pass0" (withCount #[intV 11] 0) (progSetC0FromC1),
  mkCase "ok/c0-from-c1/pass1" (withCount #[intV 11] 1) (progSetC0FromC1),
  mkCase "ok/c0-from-c1/pass2-drop" (withCount #[intV 1, intV 2, intV 3] 2) (progSetC0FromC1),
  mkCase "ok/c0-from-c1/tail-exec"
    (withCount #[intV 9] 0)
    (progSetC0FromC1 #[.pushInt (.num 5)]),

  -- c0 nargs branch coverage (stkOv vs success).
  mkCase "ok/c0-nargs1/pass0-one-copied" (withCount #[intV 11] 0) (progSetC0Nargs 1),
  mkCase "err/c0-nargs1/pass0-two-copied" (withCount #[intV 11, intV 12] 0) (progSetC0Nargs 1),
  mkCase "ok/c0-nargs2/pass1-one-copied" (withCount #[intV 11, intV 12] 1) (progSetC0Nargs 2),
  mkCase "err/c0-nargs0/pass0-one-copied" (withCount #[intV 11] 0) (progSetC0Nargs 0),
  mkCase "ok/c0-nargs3/pass0-three-copied" (withCount #[intV 1, intV 2, intV 3] 0) (progSetC0Nargs 3),
  mkCase "err/c0-nargs2/pass0-three-copied" (withCount #[intV 1, intV 2, intV 3] 0) (progSetC0Nargs 2),

  -- c0 already has captured stack via SETCONTVARARGS.
  mkCase "ok/captured/more-minus1-pass0-onecopy" (withCount #[intV 9] 0) (progSetC0Captured 70 (-1)),
  mkCase "ok/captured/more1-pass0-onecopy" (withCount #[intV 9] 0) (progSetC0Captured 71 1),
  mkCase "err/captured/more0-pass0-onecopy" (withCount #[intV 9] 0) (progSetC0Captured 72 0),
  mkCase "ok/captured/more2-pass1-onecopy" (withCount #[intV 9, intV 10] 1) (progSetC0Captured 73 2),
  mkCase "err/captured/more1-pass0-twocopy" (withCount #[intV 9, intV 10] 0) (progSetC0Captured 74 1),
  mkCase "ok/captured/more2-pass0-twocopy" (withCount #[intV 9, intV 10] 0) (progSetC0Captured 75 2),

  -- Error mapping from pop_smallint_range(255) and post-pop underflow.
  mkCase "err/underflow-empty" #[],
  mkCase "err/underflow-need-after-pop-1" #[intV 1],
  mkCase "err/underflow-need-after-pop-255" #[intV 255],
  mkCase "err/type-top-null" #[.null],
  mkCase "err/type-top-cell" #[.cell cellA],
  mkCase "err/type-top-slice" #[.slice sliceA],
  mkCase "err/type-top-builder" #[.builder Builder.empty],
  mkCase "err/type-top-tuple-empty" #[.tuple #[]],
  mkCase "err/type-top-cont-quit0" #[q0],
  mkCase "err/range-top-nan-via-program" #[] #[.pushInt .nan, returnVarArgsInstr],
  mkCase "err/range-top-minus1" #[intV (-1)],
  mkCase "err/range-top-256" #[intV 256],
  mkCase "err/range-top-max-int257" #[intV maxInt257],
  mkCase "err/range-top-min-int257" #[intV minInt257],
  mkCase "err/range-nan-via-program" #[] #[.pushInt .nan, returnVarArgsInstr],

  -- Decode boundaries around 16-bit RETURNVARARGS opcode.
  mkCaseCode "err/decode-truncated-8-prefix" #[] returnVarArgsTruncated8Code,
  mkCaseCode "err/decode-truncated-15-prefix" #[intV 1] returnVarArgsTruncated15Code
]

def suite : InstrSuite where
  id := returnVarArgsId
  unit := #[
    { name := "unit/dispatch/returnvarargs-vs-fallback"
      run := do
        expectOkStack "dispatch/fallback-next-only"
          (runReturnVarArgsFallback .add #[intV 2, intV 3])
          #[intV 2, intV 3, intV dispatchSentinel]
        expectOkStack "dispatch/matched-returnvarargs"
          (runReturnVarArgsFallback returnVarArgsInstr (withCount #[intV 7] 1))
          #[intV 7] }
    ,
    { name := "unit/errors/underflow-type-range"
      run := do
        expectErr "underflow/empty" (runReturnVarArgsDirect #[]) .stkUnd
        expectErr "underflow/need-after-pop-1" (runReturnVarArgsDirect #[intV 1]) .stkUnd
        expectErr "type/top-null" (runReturnVarArgsDirect #[.null]) .typeChk
        expectErr "type/top-cell" (runReturnVarArgsDirect #[.cell cellA]) .typeChk
        expectErr "type/top-slice" (runReturnVarArgsDirect #[.slice sliceA]) .typeChk
        expectErr "type/top-builder" (runReturnVarArgsDirect #[.builder Builder.empty]) .typeChk
        expectErr "type/top-tuple" (runReturnVarArgsDirect #[.tuple #[]]) .typeChk
        expectErr "type/top-cont" (runReturnVarArgsDirect #[q0]) .typeChk
        expectErr "range/top-nan" (runReturnVarArgsDirect #[.int .nan]) .rangeChk
        expectErr "range/top-minus1" (runReturnVarArgsDirect #[intV (-1)]) .rangeChk
        expectErr "range/top-256" (runReturnVarArgsDirect #[intV 256]) .rangeChk }
    ,
    { name := "unit/order/pop-before-underflow-check"
      run := do
        let st ← expectRawErr "order/pop-before-underflow"
          (runReturnVarArgsRaw #[intV 88, intV 2]) .stkUnd
        if st.stack != #[intV 88] then
          throw (IO.userError s!"order/pop-before-underflow: expected stack #[88], got {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"order/pop-before-underflow: expected unchanged c0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/returnargs-common/c0-capture-bottom-preserve-top"
      run := do
        let st ← expectRawOk "c0-capture-bottom" (runReturnVarArgsRaw (withCount #[intV 1, intV 2, intV 3] 1))
        if st.stack != #[intV 3] then
          throw (IO.userError s!"c0-capture-bottom: expected stack #[3], got {reprStr st.stack}")
        else
          match st.regs.c0 with
          | .envelope ext _ cdata =>
              if ext != .quit 0 then
                throw (IO.userError s!"c0-capture-bottom: expected ext quit0, got {reprStr ext}")
              else if cdata.stack != #[intV 1, intV 2] then
                throw (IO.userError
                  s!"c0-capture-bottom: expected captured #[1,2], got {reprStr cdata.stack}")
              else if cdata.nargs != (-1) then
                throw (IO.userError s!"c0-capture-bottom: expected nargs=-1, got {cdata.nargs}")
              else
                pure ()
          | other =>
              throw (IO.userError s!"c0-capture-bottom: expected envelope c0, got {reprStr other}") }
    ,
    { name := "unit/returnargs-common/depth-equals-count-no-c0-wrap"
      run := do
        let st ← expectRawOk "depth-equals-count" (runReturnVarArgsRaw (withCount #[intV 7, intV 8] 2))
        if st.stack != #[intV 7, intV 8] then
          throw (IO.userError s!"depth-equals-count: stack mismatch {reprStr st.stack}")
        else if st.regs.c0 != .quit 0 then
          throw (IO.userError s!"depth-equals-count: expected c0=quit0, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/order/stkov-after-stack-shape-and-before-c0-writeback"
      run := do
        let c0Need1 := c0NeedArgs 1
        let st ← expectRawErr "stkov-order"
          (runReturnVarArgsRaw (withCount #[intV 11, intV 12] 0) (mkOrdCont) c0Need1) .stkOv
        if !st.stack.isEmpty then
          throw (IO.userError s!"stkov-order: expected emptied stack after keep=0, got {reprStr st.stack}")
        else if st.regs.c0 != c0Need1 then
          throw (IO.userError s!"stkov-order: expected c0 unchanged on error, got {reprStr st.regs.c0}")
        else
          pure () }
    ,
    { name := "unit/decode-assemble/returnvarargs-opcode"
      run := do
        match assembleCp0 [.returnVarArgs] with
        | .ok assembled =>
            if assembled.bits != natToBits 0xed10 16 then
              throw (IO.userError s!"opcode/returnvarargs: expected 0xed10, got {reprStr assembled.bits}")
        | .error e =>
            throw (IO.userError s!"opcode/returnvarargs: unexpected assembly error {reprStr e}")
        expectDecodeReturnVarArgs "decode/ok" (Cell.mkOrdinary (natToBits 0xed10 16) #[])
        expectDecodeErr "decode/truncated-8" returnVarArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated-15" returnVarArgsTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile returnVarArgsId returnVarArgsFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.RETURNVARARGS
