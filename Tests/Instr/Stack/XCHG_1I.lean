import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.XCHG_1I

/-
INSTRUCTION: XCHG_1I

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Dispatch path:
   - `execInstrStackXchg1` must match `.xchg1 idx`; any non-matching opcode passes to `next`.
2. [B2] Runtime success:
   - For valid argument `2 ≤ idx ≤ 15` and `idx < st.stack.size`, `VM.swap 1 idx` is applied.
   - Swap is pure local reorder and keeps stack size unchanged.
3. [B3] Runtime stack-shape/path branch:
   - Deep stacks preserve elements below the swapped positions.
4. [B4] Runtime underflow branch:
   - When `idx ≥ st.stack.size`, execution fails with `.stkUnd`.
5. [B5] Assembler range branch:
   - `.xchg1 idx` assembles only for `2 ≤ idx ≤ 15`; otherwise `.rangeChk`.
   - Valid indices encode to one-byte opcodes `0x12`..`0x1f`.
6. [B6] Decoder boundary/alias branches:
   - `0x12`..`0x1f` decode to `.xchg1 2`..`.xchg1 15`.
   - Neighbor prefixes `0x10` (16-bit `XCHG`) and `0x11` (long `XCHG s0`) do not decode to `.xchg1`.
   - Truncated 4/8-bit prefixes and unrelated bytes produce decode errors.
7. [B7] Gas edge:
   - No variable gas penalty branch was observed; gas check uses base-cost only.
   - Exact budget succeeds; exact-minus-one budget fails before execution.

TOTAL BRANCHES: 7
Each oracle test below is tagged with the branch(es) it covers.
-/

private def xchg1Id : InstrId := { name := "XCHG_1I" }

private def xchg1Instr : Instr := .xchg1 2

private def dispatchSentinel : Int := 55112

private def sampleCell : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
private def sampleSlice : Slice := Slice.ofCell sampleCell
private def sampleBuilder : Builder := Builder.empty

private def raw8 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 8) #[]
private def raw16 (w : Nat) : Cell := Cell.mkOrdinary (natToBits w 16) #[]
private def xchg1Code (idx : Nat) : Cell := raw8 (0x10 + idx)
private def truncated4Code : Cell := Cell.mkOrdinary (natToBits 0x1 4) #[]
private def truncated8Code : Cell := raw8 0x10
private def invalidFFCode : Cell := raw8 0xff
private def xchg0LongNeighborCode : Cell := raw16 0x1110

private def depth16Base : Array Value := Array.range 16 |>.map (fun i => intV (Int.ofNat i))
private def depth15Base : Array Value := Array.range 15 |>.map (fun i => intV (Int.ofNat i))
private def depth17Base : Array Value := Array.range 17 |>.map (fun i => intV (Int.ofNat i))

private def runXchg1DispatchFallback (instr : Instr) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrStackXchg1 instr (VM.push (intV dispatchSentinel)) stack

private def runXchg1Direct (idx : Nat) (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXchg1 (.xchg1 idx) stack

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[xchg1Instr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg1Id
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkCaseCode
    (name : String)
    (stack : Array Value)
    (code : Cell)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := xchg1Id
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def expectDecodeOk
    (label : String)
    (code : Cell)
    (expected : Instr)
    (expectedBits : Nat := 8) : IO Unit := do
  match decodeCp0WithBits (Slice.ofCell code) with
  | .ok (instr, bits, rest) => do
      if instr != expected then
        throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr instr}")
      else if bits != expectedBits then
        throw (IO.userError s!"{label}: expected decoded bits {expectedBits}, got {bits}")
      else if rest.bitsRemaining + rest.refsRemaining != 0 then
        throw (IO.userError s!"{label}: expected empty decode tail, got {reprStr rest}")
      else
        pure ()
  | .error e =>
      throw (IO.userError s!"{label}: expected decode success, got {e}")

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

private def expectAssembleErr
    (label : String)
    (instr : Instr)
    (expected : Excno) : IO Unit := do
  match assembleCp0 [instr] with
  | .error e =>
      if e = expected then
        pure ()
      else
        throw (IO.userError s!"{label}: expected assemble error {expected}, got {e}")
  | .ok _ =>
      throw (IO.userError s!"{label}: expected assemble error {expected}, got success")

private def xchg1Gas : Int := computeExactGasBudget xchg1Instr
private def xchg1GasMinusOne : Int := computeExactGasBudgetMinusOne xchg1Instr

private def xchg1GasExact : OracleGasLimits :=
  oracleGasLimitsExact xchg1Gas

private def xchg1GasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne xchg1GasMinusOne

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def fuzzValuePool : Array Value :=
  #[
    .null,
    .cell sampleCell,
    .slice sampleSlice,
    .builder sampleBuilder,
    .tuple #[],
    .cont (.quit 0),
    intV (-1),
    intV 0,
    intV 1,
    intV 17,
    intV maxInt257,
    intV minInt257
  ]

private def randomValueStack (size : Nat) (rng0 : StdGen) : Array Value × StdGen :=
  Id.run do
    let mut out : Array Value := #[]
    let mut rng := rng0
    let mut i : Nat := 0
    while i < size do
      let (v, rng') := pickFromPool fuzzValuePool rng
      out := out.push v
      rng := rng'
      i := i + 1
    return (out, rng)

private def genXchg1FuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 9
  if shape = 0 then
    let (idx, rng2) := randNat rng1 2 15
    let (extra, rng3) := randNat rng2 0 3
    let size := idx + extra + 1
    let (stack, rng4) := randomValueStack size rng3
    let (tag, rng5) := randNat rng4 0 999_999
    (mkCase s!"fuzz/ok/depth/{idx}/{tag}" stack #[.xchg1 idx], rng5)
  else if shape = 1 then
    let (idx, rng2) := randNat rng1 2 15
    let (a, rng3) := pickSigned257ish rng2
    let (b, rng4) := pickSigned257ish rng3
    let (pre, rng5) := randomValueStack idx rng4
    let (extra, rng6) := randNat rng5 0 2
    let (suffix, rng7) := randomValueStack extra rng6
    let stack := pre ++ #[intV a, intV b] ++ suffix ++ #[.null, .cell sampleCell, .slice sampleSlice, .builder sampleBuilder]
    let (tag, rng8) := randNat rng7 0 999_999
    (mkCase s!"fuzz/ok/typed-prefix/{idx}/{tag}" stack #[.xchg1 idx], rng8)
  else if shape = 2 then
    let (idx, rng2) := randNat rng1 2 15
    let (depth, rng3) := randNat rng2 0 idx
    let (stack, rng4) := randomValueStack depth rng3
    let (tag, rng5) := randNat rng4 0 999_999
    (mkCase s!"fuzz/err/underflow/{idx}/{tag}" stack #[.xchg1 idx], rng5)
  else if shape = 3 then
    let (caseKind, rng2) := randNat rng1 0 3
    let invalidIdx : Nat :=
      if caseKind = 0 then 0 else if caseKind = 1 then 1 else if caseKind = 2 then 16 else 255
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"fuzz/err/asm/{invalidIdx}/{tag}" (depth16Base.take 1) #[.xchg1 invalidIdx], rng3)
  else if shape = 4 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCaseCode s!"fuzz/err/decode/truncated-8/{tag}" #[] truncated8Code, rng2)
  else if shape = 5 then
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCaseCode s!"fuzz/err/decode/truncated-4/{tag}" #[] truncated4Code, rng2)
  else if shape = 6 then
    let (idx, rng2) := randNat rng1 0 1
    let (tag, rng3) := randNat rng2 0 999_999
    let code : Cell := if idx = 0 then xchg1Code 2 else xchg1Code 15
    let stack := if idx = 0 then #[intV 1, intV 2, intV 3] else depth17Base
    (mkCaseCode s!"fuzz/ok/decode/{idx}/{tag}" stack code, rng3)
  else if shape = 7 then
    let (tightOrNot, rng2) := randNat rng1 0 1
    let budget : Int := if tightOrNot = 0 then xchg1Gas else xchg1GasMinusOne
    let limits : OracleGasLimits :=
      if tightOrNot = 0 then xchg1GasExact else xchg1GasExactMinusOne
    let caseName := if tightOrNot = 0 then s!"fuzz/gas/exact" else s!"fuzz/gas/exact-minus-one"
    let (tag, rng3) := randNat rng2 0 999_999
    (mkCase s!"{caseName}/{tag}" #[intV 1, intV 2, intV 3] #[.pushInt (.num budget), .tonEnvOp .setGasLimit, .xchg1 2] limits, rng3)
  else
    let (tag, rng2) := randNat rng1 0 999_999
    (mkCaseCode s!"fuzz/ok/decode/neighbor-xchg0/{tag}" depth17Base xchg0LongNeighborCode, rng2)

def suite : InstrSuite where
  id := xchg1Id
  unit := #[
    { name := "unit/dispatch/fallback-add"
      run := do
        expectOkStack "dispatch/fallback-add" (runXchg1DispatchFallback .add #[intV 10, intV 32]) #[intV 10, intV 32, intV dispatchSentinel]
    },
    { name := "unit/dispatch/matched-idx2"
      run := do
        expectOkStack "dispatch/idx2" (runXchg1Direct 2 #[intV 7, intV 11, intV 22]) #[intV 11, intV 7, intV 22]
    },
    { name := "unit/runtime/type-mix"
      run := do
        expectOkStack "type-mix"
          (runXchg1Direct 2 #[.null, intV 1, .cell sampleCell, .slice sampleSlice]) #[.null, .cell sampleCell, intV 1, .slice sampleSlice]
    },
    { name := "unit/runtime/underflow-empty"
      run := do
        expectErr "underflow-empty" (runXchg1Direct 2 #[]) .stkUnd
    },
    { name := "unit/runtime/underflow-two-items"
      run := do
        expectErr "underflow-two-items" (runXchg1Direct 2 #[intV 1, intV 2]) .stkUnd
    },
    { name := "unit/runtime/underflow-idx15"
      run := do
        expectErr "underflow-idx15" (runXchg1Direct 15 depth15Base) .stkUnd
    },
    { name := "unit/asmdecode/encode-decode-idx2"
      run := do
        expectDecodeOk "asmdecode-idx2" (xchg1Code 2) (.xchg1 2)
    },
    { name := "unit/asmdecode/encode-decode-idx15"
      run := do
        expectDecodeOk "asmdecode-idx15" (xchg1Code 15) (.xchg1 15)
    },
    { name := "unit/asmdecode/assemble-reject-idx0"
      run := do
        expectAssembleErr "assemble-idx0" (.xchg1 0) .rangeChk
    },
    { name := "unit/asmdecode/assemble-reject-idx1"
      run := do
        expectAssembleErr "assemble-idx1" (.xchg1 1) .rangeChk
    },
    { name := "unit/asmdecode/assemble-reject-idx16"
      run := do
        expectAssembleErr "assemble-idx16" (.xchg1 16) .rangeChk
    },
    { name := "unit/asmdecode/decode-truncated-8"
      run := do
        expectDecodeErr "decode-truncated-8" truncated8Code .invOpcode
    },
    { name := "unit/asmdecode/decode-truncated-4"
      run := do
        expectDecodeErr "decode-truncated-4" truncated4Code .invOpcode
    },
    { name := "unit/asmdecode/decode-truncated-11"
      run := do
        expectDecodeErr "decode-truncated-11" (raw8 0x11) .invOpcode
    },
    { name := "unit/asmdecode/decode-invalid-ff"
      run := do
        expectDecodeErr "decode-invalid-ff" invalidFFCode .invOpcode
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/ok/dispatch-match-idx2" #[intV 11, intV 22, intV 33],
    -- [B2]
    mkCase "oracle/ok/idx2/boundary-min" #[intV 0, intV 1, intV 2],
    -- [B2]
    mkCase "oracle/ok/idx2/negative" #[intV (-7), intV 9, intV 12],
    -- [B2]
    mkCase "oracle/ok/idx2/max-min" #[intV maxInt257, intV 0, intV minInt257],
    -- [B2]
    mkCase "oracle/ok/idx3" #[intV 1, intV 2, intV 3, intV 4] #[.xchg1 3],
    -- [B2]
    mkCase "oracle/ok/idx4-min" #[intV 4, intV 5, intV 6, intV 7, intV 8] #[.xchg1 4],
    -- [B2]
    mkCase "oracle/ok/idx15-max-depth" depth17Base #[.xchg1 15],
    -- [B3]
    mkCase "oracle/ok/deep-prefix-7" (#[.null, .cell sampleCell, .slice sampleSlice, .builder sampleBuilder, intV 1, intV 2, intV 3]) #[.xchg1 2],
    -- [B3]
    mkCase "oracle/ok/deep-prefix-12" (depth16Base ++ #[.tuple #[], .cont (.quit 0), intV 99]) #[.xchg1 5],
    -- [B3]
    mkCase "oracle/ok/deep-prefix-typed" (#[.tuple #[], .null, .cell sampleCell, .slice sampleSlice, .builder sampleBuilder, .cont (.quit 0), intV 0, intV 1]) #[.xchg1 6],
    -- [B3]
    mkCase "oracle/ok/deep-prefix-noise" (depth17Base ++ #[intV 1, intV 2, intV 3, intV 4]) #[.xchg1 7],
    -- [B2]
    mkCase "oracle/ok/type-no-check-int" #[intV 0, .null, .cell sampleCell, intV 9, .slice sampleSlice, .builder sampleBuilder] #[.xchg1 2],
    -- [B2]
    mkCase "oracle/ok/type-no-check-cont" #[.tuple #[], .cont (.quit 0), .cell sampleCell, .slice sampleSlice, .builder sampleBuilder, intV 7, .null] #[.xchg1 3],
    -- [B2]
    mkCase "oracle/ok/type-no-check-typed-mix" #[.null, .cont (.quit 0), .tuple #[], .builder sampleBuilder, .cell sampleCell, .slice sampleSlice, intV 1] #[.xchg1 4],
    -- [B4]
    mkCase "oracle/err/underflow/empty" #[] #[.xchg1 2],
    -- [B4]
    mkCase "oracle/err/underflow/one" #[intV 1] #[.xchg1 2],
    -- [B4]
    mkCase "oracle/err/underflow/two" #[intV 1, intV 2] #[.xchg1 2],
    -- [B4]
    mkCase "oracle/err/underflow/idx3-size2" #[intV 1, intV 2] #[.xchg1 3],
    -- [B4]
    mkCase "oracle/err/underflow/idx15-size15" (depth17Base.take 15) #[.xchg1 15],
    -- [B4]
    mkCase "oracle/err/underflow/idx15-size16" (depth16Base) #[.xchg1 15],
    -- [B5]
    mkCase "oracle/ok/asm/idx2-roundtrip" (#[intV 7, intV 8, intV 9]) #[.xchg1 2],
    -- [B5]
    mkCase "oracle/ok/asm/idx15-roundtrip" (depth17Base.take 16) #[.xchg1 15],
    -- [B6]
    mkCaseCode "oracle/ok/decode/0x12" (#[intV 1, intV 2, intV 3]) (xchg1Code 2),
    -- [B6]
    mkCaseCode "oracle/ok/decode/0x13" (#[intV 7, intV 8, intV 9, intV 10]) (xchg1Code 3),
    -- [B6]
    mkCaseCode "oracle/ok/decode/0x1f" (depth17Base) (xchg1Code 15),
    -- [B6]
    mkCaseCode "oracle/err/decode/0x10-truncated" (depth16Base) truncated8Code,
    -- [B6]
    mkCaseCode "oracle/err/decode-0x11-truncated" (depth16Base) (raw8 0x11),
    -- [B6]
    mkCaseCode "oracle/ok/decode/0x11xx-neighbor" (depth17Base) xchg0LongNeighborCode,
    -- [B6]
    mkCaseCode "oracle/err/decode/0x1-bittrunc" (depth16Base) truncated4Code,
    -- [B6]
    mkCaseCode "oracle/err/decode/0xff" (depth16Base) invalidFFCode,
    -- [B7]
    mkCase "oracle/gas/exact" #[intV 1, intV 2, intV 3] #[.pushInt (.num xchg1Gas), .tonEnvOp .setGasLimit, .xchg1 2] xchg1GasExact,
    -- [B7]
    mkCase "oracle/gas/exact-minus-one" #[intV 1, intV 2, intV 3] #[.pushInt (.num xchg1GasMinusOne), .tonEnvOp .setGasLimit, .xchg1 2] xchg1GasExactMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr xchg1Id
      count := 500
      gen := genXchg1FuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.XCHG_1I
