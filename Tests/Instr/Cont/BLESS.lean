import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Cont.BLESS

/-
BLESS branch map (Lean vs C++):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/Cont/Bless.lean`
  - `TvmLean/Semantics/VM/Ops/Stack.lean` (`popInt`, `popNatUpTo`)
  - `TvmLean/Semantics/VM/Ops/Cont.lean` (`VM.jump`, `VM.call`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/contops.cpp`
    (`exec_bless`, `exec_bless_args_common`, `exec_bless_varargs`)
  - `/Users/daniil/Coding/ton/crypto/vm/stack.cpp`
    (`pop_smallint_range`, `pop_cellslice`)

Coverage focus:
- continuation conversion (`slice -> ordinary continuation`);
- `copy` / `more` capture interactions for `BLESSARGS` and `BLESSVARARGS`;
- operand/error-order mapping (`stkUnd`, `typeChk`, `rangeChk`);
- NaN range mapping parity for `BLESSVARARGS` (`pop_smallint_range(255, -1) -> range_chk`);
- deterministic oracle compatibility (token-encodable stacks, handcrafted cases).
-/

private def blessId : InstrId := { name := "BLESS" }
private def blessInstr : Instr := .bless
private def blessVarArgsInstr : Instr := .blessVarArgs

private def dispatchSentinel : Int := 61342

private def cellA : Cell :=
  Cell.mkOrdinary (natToBits 0x15 6) #[]

private def cellB : Cell :=
  Cell.mkOrdinary (natToBits 0x2a 6) #[cellA]

private def sliceA : Slice := Slice.ofCell cellA
private def sliceB : Slice := Slice.ofCell cellB
private def sliceEmpty : Slice := Slice.ofCell Cell.empty

private def q0 : Value := .cont (.quit 0)

private def intStackAsc (n : Nat) : Array Value :=
  (Array.range n).map (fun i => intV (Int.ofNat (i + 1)))

private def runBlessDirect
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrContBless instr stack

private def runBlessDispatchFallback
    (instr : Instr)
    (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrContBless instr (VM.push (intV dispatchSentinel)) stack

private def runBlessRaw
    (instr : Instr)
    (stack : Array Value) : Except Excno Unit × VmState :=
  let st0 : VmState := { (VmState.initial Cell.empty) with stack := stack }
  (execInstrContBless instr (pure ())).run st0

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

private def expectRawOk
    (label : String)
    (out : Except Excno Unit × VmState) : IO VmState := do
  let (res, st) := out
  match res with
  | .ok _ => pure st
  | .error e =>
      throw (IO.userError s!"{label}: expected success, got {e}")

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

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expectedInstr : Instr)
    (expectedBits : Nat := 16) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) =>
      if instr != expectedInstr then
        throw (IO.userError s!"{label}: expected {reprStr expectedInstr}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected bits={expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[blessInstr])
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blessId
    program := program
    initStack := stack
    fuel := fuel }

private def mkCodeCase
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := blessId
    codeCell? := some code
    initStack := stack
    fuel := fuel }

private def progBlessArgsCallxVarArgs (copy : Nat) (more params retVals : Int) : Array Instr :=
  #[.blessArgs copy more, .pushInt (.num params), .pushInt (.num retVals), .callxVarArgs]

private def progBlessVarArgsCallxVarArgs (params retVals : Int) : Array Instr :=
  #[.blessVarArgs, .pushInt (.num params), .pushInt (.num retVals), .callxVarArgs]

private def progBlessArgsJmpxVarArgs (copy : Nat) (more params : Int) : Array Instr :=
  #[.blessArgs copy more, .pushInt (.num params), .jmpxVarArgs]

private def progBlessVarArgsJmpxVarArgs (params : Int) : Array Instr :=
  #[.blessVarArgs, .pushInt (.num params), .jmpxVarArgs]

private def blessCode : Cell :=
  Cell.mkOrdinary (natToBits 0xed1e 16) #[]

private def blessVarArgsCode : Cell :=
  Cell.mkOrdinary (natToBits 0xed1f 16) #[]

private def blessArgs2Neg1Code : Cell :=
  Cell.mkOrdinary (natToBits 0xee2f 16) #[]

private def blessTruncated8Code : Cell :=
  Cell.mkOrdinary (natToBits 0xed 8) #[]

private def blessTruncated15Code : Cell :=
  Cell.mkOrdinary (natToBits (0xed1e >>> 1) 15) #[]

private def oracleCases : Array OracleCase := #[
  -- BLESS conversion and simple ordering.
  mkCase "ok/bless/basic-empty-slice" #[.slice sliceEmpty],
  mkCase "ok/bless/basic-slice-a" #[.slice sliceA],
  mkCase "ok/bless/basic-slice-b-with-below-int" #[intV 7, .slice sliceB],
  mkCase "ok/bless/basic-mixed-below"
    #[.null, .cell cellA, .builder Builder.empty, .tuple #[], .slice sliceA],
  mkCase "ok/bless/basic-k-below" #[q0, intV (-3), .slice sliceB],
  mkCase "order/bless/tail-push-skipped" #[.slice sliceA] #[.bless, .pushInt (.num 999)],
  mkCase "order/bless/prelude-push-swap" #[.slice sliceA] #[.pushInt (.num 11), .xchg0 1, .bless],
  mkCase "err/bless/underflow-empty" #[],
  mkCase "err/bless/type-top-int" #[intV 1],
  mkCase "err/bless/type-top-null" #[.null],
  mkCase "err/bless/type-top-cell" #[.cell cellA],
  mkCase "err/bless/type-top-builder" #[.builder Builder.empty],
  mkCase "err/bless/type-top-tuple" #[.tuple #[]],
  mkCase "err/bless/type-top-cont" #[q0],

  -- BLESSARGS capture semantics and error order.
  mkCase "ok/blessargs/copy0-more-neg1-empty" #[.slice sliceA] #[.blessArgs 0 (-1)],
  mkCase "ok/blessargs/copy0-more0-empty" #[.slice sliceA] #[.blessArgs 0 0],
  mkCase "ok/blessargs/copy1-more0-one-arg" #[intV 7, .slice sliceA] #[.blessArgs 1 0],
  mkCase "ok/blessargs/copy1-more1-one-arg" #[intV 7, .slice sliceB] #[.blessArgs 1 1],
  mkCase "ok/blessargs/copy2-more1-two-args" #[intV 7, intV 8, .slice sliceA] #[.blessArgs 2 1],
  mkCase "ok/blessargs/copy2-more14-two-args" #[intV 7, intV 8, .slice sliceB] #[.blessArgs 2 14],
  mkCase "ok/blessargs/copy15-more14-depth15" (intStackAsc 15 ++ #[.slice sliceA]) #[.blessArgs 15 14],
  mkCase "err/blessargs/underflow-empty" #[] #[.blessArgs 0 0],
  mkCase "err/blessargs/underflow-copy1-only-slice" #[.slice sliceA] #[.blessArgs 1 0],
  mkCase "err/blessargs/underflow-copy2-one-arg" #[intV 1, .slice sliceA] #[.blessArgs 2 0],
  mkCase "err/blessargs/type-top-not-slice" #[intV 1, intV 2] #[.blessArgs 1 0],
  mkCase "err/blessargs/type-top-null" #[intV 1, .null] #[.blessArgs 1 0],
  mkCase "err/blessargs/order-underflow-before-slice-type" #[intV 1, .null] #[.blessArgs 2 0],

  -- BLESSVARARGS copy/more bounds, type mapping, and ordering.
  mkCase "ok/blessvarargs/copy0-more-neg1" #[.slice sliceA, intV 0, intV (-1)] #[.blessVarArgs],
  mkCase "ok/blessvarargs/copy0-more0" #[.slice sliceA, intV 0, intV 0] #[.blessVarArgs],
  mkCase "ok/blessvarargs/copy1-more0" #[intV 7, .slice sliceA, intV 1, intV 0] #[.blessVarArgs],
  mkCase "ok/blessvarargs/copy1-more1" #[intV 7, .slice sliceB, intV 1, intV 1] #[.blessVarArgs],
  mkCase "ok/blessvarargs/copy2-more1" #[intV 7, intV 8, .slice sliceA, intV 2, intV 1] #[.blessVarArgs],
  mkCase "ok/blessvarargs/copy2-more255" #[intV 7, intV 8, .slice sliceB, intV 2, intV 255] #[.blessVarArgs],
  mkCase "err/blessvarargs/underflow-empty" #[] #[.blessVarArgs],
  mkCase "err/blessvarargs/underflow-one-item" #[intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/type-more-null" #[.slice sliceA, intV 0, .null] #[.blessVarArgs],
  mkCase "err/blessvarargs/type-more-cell" #[.slice sliceA, intV 0, .cell cellA] #[.blessVarArgs],
  mkCase "err/blessvarargs/range-more-low" #[.slice sliceA, intV 0, intV (-2)] #[.blessVarArgs],
  mkCase "err/blessvarargs/range-more-high" #[.slice sliceA, intV 0, intV 256] #[.blessVarArgs],
  mkCase "err/blessvarargs/rangemap-more-nan-program" #[.slice sliceA, intV 0]
    #[.pushInt .nan, .blessVarArgs],
  mkCase "err/blessvarargs/type-copy-null" #[.slice sliceA, .null, intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/type-copy-cell" #[.slice sliceA, .cell cellA, intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/range-copy-neg" #[.slice sliceA, intV (-1), intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/range-copy-high" #[.slice sliceA, intV 256, intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/rangemap-copy-nan-program" #[.slice sliceA, intV 0]
    #[.pushInt .nan, .xchg0 1, .blessVarArgs],
  mkCase "err/blessvarargs/type-slice-after-params" #[intV 1, intV 0, intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/underflow-copy-after-pop" #[.slice sliceA, intV 2, intV 0] #[.blessVarArgs],
  mkCase "err/blessvarargs/order-more-before-copy-type" #[.slice sliceA, .cell cellA, .null] #[.blessVarArgs],
  mkCase "err/blessvarargs/order-copy-before-slice-type" #[intV 1, .null, intV 0] #[.blessVarArgs],

  -- Conversion/copy-more interactions through CALLXVARARGS and JMPXVARARGS.
  mkCase "ok/interaction/blessargs-copy1-more1-callx-pass1-ret0"
    #[intV 9, .slice sliceA] (progBlessArgsCallxVarArgs 1 1 1 0),
  mkCase "err/interaction/blessargs-copy1-more1-callx-pass0-ret0"
    #[intV 9, .slice sliceA] (progBlessArgsCallxVarArgs 1 1 0 0),
  mkCase "ok/interaction/blessargs-copy1-more-neg1-callx-pass0-ret0"
    #[intV 9, .slice sliceA] (progBlessArgsCallxVarArgs 1 (-1) 0 0),
  mkCase "ok/interaction/blessargs-copy2-more2-callx-pass2-ret0"
    #[intV 1, intV 2, .slice sliceA] (progBlessArgsCallxVarArgs 2 2 2 0),
  mkCase "err/interaction/blessargs-copy2-more2-callx-pass1-ret0"
    #[intV 1, intV 2, .slice sliceA] (progBlessArgsCallxVarArgs 2 2 1 0),
  mkCase "ok/interaction/blessvarargs-copy1-more1-callx-pass1-ret0"
    #[intV 9, .slice sliceB, intV 1, intV 1] (progBlessVarArgsCallxVarArgs 1 0),
  mkCase "err/interaction/blessvarargs-copy1-more1-callx-pass0-ret0"
    #[intV 9, .slice sliceB, intV 1, intV 1] (progBlessVarArgsCallxVarArgs 0 0),
  mkCase "ok/interaction/blessvarargs-copy2-more-neg1-callx-pass-all-ret0"
    #[intV 1, intV 2, .slice sliceA, intV 2, intV (-1)] (progBlessVarArgsCallxVarArgs (-1) 0),
  mkCase "ok/interaction/blessargs-copy1-more0-jmpx-pass0"
    #[intV 9, .slice sliceA] (progBlessArgsJmpxVarArgs 1 0 0),
  mkCase "err/interaction/blessargs-copy1-more1-jmpx-pass0"
    #[intV 9, .slice sliceA] (progBlessArgsJmpxVarArgs 1 1 0),
  mkCase "ok/interaction/blessvarargs-copy1-more0-jmpx-pass0"
    #[intV 9, .slice sliceA, intV 1, intV 0] (progBlessVarArgsJmpxVarArgs 0),

  -- Decode gates around BLESS prefix width.
  mkCodeCase "decode/bless-truncated8" #[] blessTruncated8Code,
  mkCodeCase "decode/bless-truncated15" #[intV 1] blessTruncated15Code
]

private def blessFuzzProfile : ContMutationProfile :=
  { oracleNamePrefixes := #[
      "ok/bless/",
      "order/bless/",
      "err/bless/underflow-",
      "err/bless/type-",
      "ok/blessargs/",
      "err/blessargs/underflow-",
      "err/blessargs/type-",
      "err/blessargs/order-",
      "ok/blessvarargs/",
      "err/blessvarargs/underflow-",
      "err/blessvarargs/type-",
      "err/blessvarargs/range-",
      "err/blessvarargs/rangemap-",
      "err/blessvarargs/order-",
      "ok/interaction/",
      "err/interaction/",
      "decode/"
    ]
    -- Weight toward stack-shape/order/range perturbations for BLESS copy/more families.
    mutationModes := #[
      0, 0, 0, 0,
      2, 2, 2, 2,
      4, 4, 4,
      1, 1,
      3
    ]
    minMutations := 1
    maxMutations := 5
    includeErrOracleSeeds := true }

def suite : InstrSuite where
  id := blessId
  unit := #[
    { name := "unit/dispatch/fallback-vs-match"
      run := do
        expectOkStack "dispatch/fallback-add"
          (runBlessDispatchFallback .add #[intV 5])
          #[intV 5, intV dispatchSentinel]
        expectOkStack "dispatch/matched-bless"
          (runBlessDispatchFallback .bless #[.slice sliceA])
          #[.cont (.ordinary sliceA (.quit 0) OrdCregs.empty OrdCdata.empty)] }
    ,
    { name := "unit/raw/bless-converts-slice-to-ordinary"
      run := do
        let st ← expectRawOk "raw/bless-converts"
          (runBlessRaw .bless #[intV 1, .slice sliceA])
        if st.stack.size != 2 then
          throw (IO.userError s!"raw/bless-converts: expected depth=2, got {st.stack.size}")
        else if st.stack[0]! != intV 1 then
          throw (IO.userError s!"raw/bless-converts: expected lower item preserved")
        else
          expectTopBlessedCont "raw/bless-converts/top" st.stack sliceA #[] (-1) }
    ,
    { name := "unit/raw/blessargs-captures-copy-and-more"
      run := do
        let st ← expectRawOk "raw/blessargs-captures"
          (runBlessRaw (.blessArgs 2 1) #[intV 7, intV 8, .slice sliceB])
        if st.stack.size != 1 then
          throw (IO.userError s!"raw/blessargs-captures: expected depth=1, got {st.stack.size}")
        else
          expectTopBlessedCont "raw/blessargs-captures/top" st.stack sliceB #[intV 7, intV 8] 1 }
    ,
    { name := "unit/order/blessargs-underflow-before-slice-type"
      run := do
        expectErr "order/blessargs-underflow-before-slice-type"
          (runBlessDirect (.blessArgs 2 0) #[intV 1, .null])
          .stkUnd }
    ,
    { name := "unit/rangemap/blessvarargs-more-nan-to-rangechk"
      run := do
        let st ← expectRawErr "rangemap/blessvarargs-more-nan"
          (runBlessRaw blessVarArgsInstr #[.slice sliceA, intV 0, .int .nan])
          .rangeChk
        if st.stack != #[.slice sliceA, intV 0] then
          throw (IO.userError s!"rangemap/blessvarargs-more-nan: expected top popped, got {reprStr st.stack}") }
    ,
    { name := "unit/rangemap/blessvarargs-copy-nan-to-rangechk"
      run := do
        let st ← expectRawErr "rangemap/blessvarargs-copy-nan"
          (runBlessRaw blessVarArgsInstr #[.slice sliceA, .int .nan, intV 0])
          .rangeChk
        if st.stack != #[.slice sliceA] then
          throw (IO.userError s!"rangemap/blessvarargs-copy-nan: expected params popped, got {reprStr st.stack}") }
    ,
    { name := "unit/raw/blessvarargs-captures-copy-and-more"
      run := do
        let st ← expectRawOk "raw/blessvarargs-captures"
          (runBlessRaw blessVarArgsInstr #[intV 7, intV 8, .slice sliceA, intV 2, intV 1])
        if st.stack.size != 1 then
          throw (IO.userError s!"raw/blessvarargs-captures: expected depth=1, got {st.stack.size}")
        else
          expectTopBlessedCont "raw/blessvarargs-captures/top" st.stack sliceA #[intV 7, intV 8] 1 }
    ,
    { name := "unit/decode/bless-family-and-truncated-prefix"
      run := do
        expectDecodeOk "decode/bless" blessCode .bless
        expectDecodeOk "decode/blessvarargs" blessVarArgsCode .blessVarArgs
        expectDecodeOk "decode/blessargs-2-neg1" blessArgs2Neg1Code (.blessArgs 2 (-1))
        expectDecodeErr "decode/bless-truncated8" blessTruncated8Code .invOpcode
        expectDecodeErr "decode/bless-truncated15" blessTruncated15Code .invOpcode }
    ,
    { name := "unit/oracle/handcrafted-count-at-least-30"
      run := do
        if oracleCases.size < 30 then
          throw (IO.userError s!"oracle count too small: expected >=30, got {oracleCases.size}") }
  ]
  oracle := oracleCases
  fuzz := #[ mkContMutationFuzzSpecWithProfile blessId blessFuzzProfile 500 ]

initialize registerSuite suite

end Tests.Instr.Cont.BLESS
