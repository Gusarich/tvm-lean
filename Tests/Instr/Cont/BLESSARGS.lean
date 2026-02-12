import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.BLESSARGS

private def blessArgsId : InstrId := { name := "BLESSARGS" }
private def blessArgsOpcode : Nat := 0xee
private def dispatchSentinel : Int := 61027

private def q0 : Value := .cont (.quit 0)

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB

private def intStackAsc (n : Nat) : Array Value :=
  (Array.range n).map (fun i => intV (Int.ofNat (i + 1)))

private def runDirect (copy : Nat) (more : Int) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContBless (.blessArgs copy more) stack

private def runFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContBless instr (VM.push (intV dispatchSentinel)) stack

private def runRaw (copy : Nat) (more : Int) (stack : Array Value) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContBless (.blessArgs copy more) (pure ())).run st0

private def expectRawOk (label : String) (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

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

private def expectTopBlessedCont
    (label : String)
    (stack : Array Value)
    (expectedCode : Slice)
    (expectedCaptured : Array Value)
    (expectedNargs : Int) : IO Unit := do
  match stack.back? with
  | some (.cont (.ordinary code saved _ cdata)) =>
      if code != expectedCode then
        throw (IO.userError s!"{label}: code mismatch expected={reprStr expectedCode} got={reprStr code}")
      else if saved != .quit 0 then
        throw (IO.userError s!"{label}: expected savedC0=.quit 0, got {reprStr saved}")
      else if cdata.stack != expectedCaptured then
        throw (IO.userError
          s!"{label}: captured stack mismatch expected={reprStr expectedCaptured} got={reprStr cdata.stack}")
      else if cdata.nargs != expectedNargs then
        throw (IO.userError s!"{label}: nargs mismatch expected={expectedNargs} got={cdata.nargs}")
      else
        pure ()
  | some (.cont k) =>
      throw (IO.userError s!"{label}: expected ordinary continuation, got {reprStr k}")
  | some v =>
      throw (IO.userError s!"{label}: expected top continuation, got {reprStr v}")
  | none =>
      throw (IO.userError s!"{label}: expected non-empty stack")

private def assembleNoRefCell! (label : String) (program : Array Instr) : Cell :=
  match assembleCp0 program.toList with
  | .ok c =>
      if c.refs.isEmpty then
        c
      else
        panic! s!"{label}: assembled with unexpected refs={c.refs.size}"
  | .error e =>
      panic! s!"{label}: assembleCp0 failed: {reprStr e}"

private def rawArgsByte (copy : Nat) (more : Int) : Nat :=
  let moreNib : Nat := if more = -1 then 15 else more.toNat
  (copy <<< 4) + moreNib

private def rawBlessArgsCode (copy : Nat) (more : Int) : Cell :=
  Cell.mkOrdinary
    (natToBits blessArgsOpcode 8 ++ natToBits (rawArgsByte copy more) 8)
    #[]

private def blessArgsThenRetCode : Cell :=
  assembleNoRefCell! "blessargs/code/seq" #[.blessArgs 2 (-1), .ret]

private def blessArgsTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits blessArgsOpcode 8) #[]

private def blessArgsTruncated15Code : Cell :=
  Cell.mkOrdinary ((natToBits (blessArgsOpcode <<< 8) 16).take 15) #[]

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
      throw (IO.userError
        s!"{label}: expected decode error {expected}, got instr={reprStr instr}, bits={bits}")

private def expectDecodeStep
    (label : String)
    (s : Slice)
    (expectedInstr : Instr)
    (expectedBits : Nat) : IO Slice := do
  match decodeCp0WithBits s with
  | .ok (instr, bits, rest) =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected instr {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
      else
        pure rest
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got error {e}")

private def expectAssembleErr
    (label : String)
    (program : Array Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 program.toList with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")
  | .ok c =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got code {reprStr c}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (copy : Nat)
    (more : Int)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blessArgsId
    program := #[.blessArgs copy more]
    initStack := stack
    fuel := fuel }

private def mkCaseProg
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blessArgsId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blessArgsId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progBlessArgsCallxVarArgs (copy : Nat) (more params retVals : Int) : Array Instr :=
  #[.blessArgs copy more, .pushInt (.num params), .pushInt (.num retVals), .callxVarArgs]

private def progBlessArgsJmpxVarArgs (copy : Nat) (more params : Int) : Array Instr :=
  #[.blessArgs copy more, .pushInt (.num params), .jmpxVarArgs]

private def blessArgsFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/basic/",
      "order/program-",
      "err/underflow-",
      "err/type-",
      "err/order-",
      "ok/decode/",
      "err/decode/",
      "ok/interaction/",
      "err/interaction/"
    ]
    -- Bias toward argument-shape, underflow/order, and boundary/range-adjacent stress.
    mutationModes := #[0, 0, 0, 0, 2, 2, 2, 4, 4, 1, 1, 3]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

private def oracleCases : Array OracleCase := #[
  -- Success boundaries for copy/more and stack splitting.
  mkCase "ok/basic/c0-more-neg1-empty" #[.slice sliceA] 0 (-1),
  mkCase "ok/basic/c0-more0-prefix-int" #[intV 5, .slice sliceA] 0 0,
  mkCase "ok/basic/c0-more14-prefix-mixed"
    #[.null, .cell cellA, .builder Builder.empty, .slice sliceB] 0 14,
  mkCase "ok/basic/c1-more-neg1-exact" #[intV 11, .slice sliceA] 1 (-1),
  mkCase "ok/basic/c1-more0-drop-bottom" #[intV 11, intV 22, .slice sliceA] 1 0,
  mkCase "ok/basic/c1-more14-mixed" #[.null, intV 7, .cell cellA, .slice sliceB] 1 14,
  mkCase "ok/basic/c2-more0-exact-two" #[intV 1, intV 2, .slice sliceA] 2 0,
  mkCase "ok/basic/c2-more1-depth3" #[intV 1, intV 2, intV 3, .slice sliceA] 2 1,
  mkCase "ok/basic/c2-more14-mixed" #[.cell cellA, intV 9, .tuple #[], .slice sliceB] 2 14,
  mkCase "ok/basic/c3-more2-mixed"
    #[.null, intV 1, .cell cellA, .tuple #[], .slice sliceA] 3 2,
  mkCase "ok/basic/c4-more0-five-values"
    #[intV 1, intV 2, intV 3, intV 4, intV 5, .slice sliceA] 4 0,
  mkCase "ok/basic/c15-more14-exact-depth" (intStackAsc 15 ++ #[.slice sliceA]) 15 14,
  mkCase "ok/basic/c15-more-neg1-depth16" (intStackAsc 16 ++ #[.slice sliceB]) 15 (-1),
  mkCase "ok/basic/c15-more0-depth16-drop-bottom" (intStackAsc 16 ++ #[.slice sliceA]) 15 0,

  -- Program-order coverage (BLESSARGS itself does not alter control flow).
  mkCaseProg "order/program-prelude-push-swap-capture"
    #[.slice sliceA]
    #[.pushInt (.num 99), .xchg0 1, .blessArgs 1 0],
  mkCaseProg "order/program-tail-continues-after-blessargs"
    #[intV 7, .slice sliceA]
    #[.blessArgs 1 0, .pushInt (.num 777)],
  mkCaseProg "order/program-large-copy15-tail-push"
    (intStackAsc 15 ++ #[.slice sliceB])
    #[.blessArgs 15 14, .pushInt (.num 88)],
  -- Underflow/type paths and ordering.
  mkCase "err/underflow-empty" #[] 0 0,
  mkCase "err/underflow-copy1-only-slice" #[.slice sliceA] 1 0,
  mkCase "err/underflow-copy2-one-arg" #[intV 1, .slice sliceA] 2 0,
  mkCase "err/underflow-copy15-short" (intStackAsc 14 ++ #[.slice sliceA]) 15 0,
  mkCase "err/type-top-int" #[intV 1] 0 0,
  mkCase "err/type-top-null" #[.null] 0 0,
  mkCase "err/type-top-cell" #[.cell cellA] 0 0,
  mkCase "err/type-top-builder" #[.builder Builder.empty] 0 0,
  mkCase "err/type-top-tuple" #[.tuple #[]] 0 0,
  mkCase "err/type-top-cont" #[q0] 0 0,
  mkCase "err/order-underflow-before-slice-type" #[intV 1, .null] 2 0,
  mkCase "err/order-type-after-underflow-check-copy1" #[intV 1, .null] 1 0,
  mkCase "err/order-underflow-before-slice-type-largecopy" #[q0, intV 1, .null] 3 0,
  mkCase "err/order-type-after-underflow-check-copy2" #[intV 1, intV 2, .cell cellA] 2 0,

  -- Decode/raw opcode coverage for the 0xee prefix family.
  mkCaseCode "ok/decode/raw-c0-more-neg1" #[.slice sliceA] (rawBlessArgsCode 0 (-1)),
  mkCaseCode "ok/decode/raw-c7-more3" (intStackAsc 7 ++ #[.slice sliceA]) (rawBlessArgsCode 7 3),
  mkCaseCode "ok/decode/raw-c15-more14" (intStackAsc 15 ++ #[.slice sliceB]) (rawBlessArgsCode 15 14),
  mkCaseCode "err/decode/truncated8" #[] blessArgsTruncated8Code,
  mkCaseCode "err/decode/truncated15" #[intV 1] blessArgsTruncated15Code,

  -- cdata interactions through CALLXVARARGS/JMPXVARARGS.
  mkCaseProg "ok/interaction/c1-more1-callx-pass1-ret0"
    #[intV 9, .slice sliceA] (progBlessArgsCallxVarArgs 1 1 1 0),
  mkCaseProg "err/interaction/c1-more1-callx-pass0-ret0"
    #[intV 9, .slice sliceA] (progBlessArgsCallxVarArgs 1 1 0 0),
  mkCaseProg "ok/interaction/c1-more-neg1-callx-pass0-ret0"
    #[intV 9, .slice sliceA] (progBlessArgsCallxVarArgs 1 (-1) 0 0),
  mkCaseProg "ok/interaction/c2-more2-callx-pass2-ret0"
    #[intV 1, intV 2, .slice sliceA] (progBlessArgsCallxVarArgs 2 2 2 0),
  mkCaseProg "err/interaction/c2-more2-callx-pass1-ret0"
    #[intV 1, intV 2, .slice sliceA] (progBlessArgsCallxVarArgs 2 2 1 0),
  mkCaseProg "ok/interaction/c1-more0-jmpx-pass0"
    #[intV 9, .slice sliceA] (progBlessArgsJmpxVarArgs 1 0 0),
  mkCaseProg "err/interaction/c1-more1-jmpx-pass0"
    #[intV 9, .slice sliceA] (progBlessArgsJmpxVarArgs 1 1 0)
]

def suite : InstrSuite where
  id := blessArgsId
  unit := #[
    { name := "unit/direct/dispatch-fallback-vs-match"
      run := do
        expectOkStack "fallback/non-match"
          (runFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "fallback/matched-blessargs"
          (runFallback (.blessArgs 0 (-1)) #[.slice sliceA])
          #[.cont (.ordinary sliceA (.quit 0) OrdCregs.empty OrdCdata.empty)] }
    ,
    { name := "unit/direct/range-copy-and-more"
      run := do
        expectErr "range/copy>15"
          (runDirect 16 0 #[.slice sliceA])
          .rangeChk
        expectErr "range/more<-1"
          (runDirect 0 (-2) #[.slice sliceA])
          .rangeChk
        expectErr "range/more>14"
          (runDirect 0 15 #[.slice sliceA])
          .rangeChk }
    ,
    { name := "unit/order/underflow-before-slice-type"
      run := do
        let st ← expectRawErr "order/underflow-before-type"
          (runRaw 2 0 #[intV 1, .null])
          .stkUnd
        if st.stack != #[intV 1, .null] then
          throw (IO.userError
            s!"order/underflow-before-type: expected stack unchanged, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/typechk-pops-top-slice-candidate"
      run := do
        let st ← expectRawErr "raw/typechk-pop"
          (runRaw 0 0 #[intV 7, .null])
          .typeChk
        if st.stack != #[intV 7] then
          throw (IO.userError s!"raw/typechk-pop: expected stack #[7], got {reprStr st.stack}") }
    ,
    { name := "unit/raw/success-captures-copy-order"
      run := do
        let st ← expectRawOk "raw/capture-order"
          (runRaw 2 1 #[intV 7, intV 8, .slice sliceB])
        if st.stack.size != 1 then
          throw (IO.userError s!"raw/capture-order: expected depth=1, got {st.stack.size}")
        else
          expectTopBlessedCont "raw/capture-order/top" st.stack sliceB #[intV 7, intV 8] 1 }
    ,
    { name := "unit/raw/success-copy0-more-neg1-empty-cdata"
      run := do
        let st ← expectRawOk "raw/copy0-more-neg1"
          (runRaw 0 (-1) #[intV 9, .slice sliceA])
        if st.stack[0]? != some (intV 9) then
          throw (IO.userError s!"raw/copy0-more-neg1: expected preserved bottom int, got {reprStr st.stack}")
        else
          expectTopBlessedCont "raw/copy0-more-neg1/top" st.stack sliceA #[] (-1) }
    ,
    { name := "unit/opcode/decode-and-assembly-boundaries"
      run := do
        let s0 := Slice.ofCell blessArgsThenRetCode
        let s1 ← expectDecodeStep "decode/blessargs" s0 (.blessArgs 2 (-1)) 16
        let s2 ← expectDecodeStep "decode/ret" s1 .ret 16
        if s2.bitsRemaining != 0 ∨ s2.refsRemaining != 0 then
          throw (IO.userError
            s!"decode/end: expected bits=0 refs=0, got bits={s2.bitsRemaining} refs={s2.refsRemaining}")
        expectDecodeErr "decode/truncated8" blessArgsTruncated8Code .invOpcode
        expectDecodeErr "decode/truncated15" blessArgsTruncated15Code .invOpcode
        expectAssembleErr "asm/copy-overflow" #[.blessArgs 16 0] .rangeChk
        expectAssembleErr "asm/more-overflow" #[.blessArgs 0 15] .rangeChk
        expectAssembleErr "asm/more-underflow" #[.blessArgs 0 (-2)] .rangeChk }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile blessArgsId blessArgsFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.BLESSARGS
