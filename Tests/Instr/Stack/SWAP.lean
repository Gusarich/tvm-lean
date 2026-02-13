import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith

namespace Tests.Instr.Stack.SWAP

/-
INSTRUCTION: SWAP

BRANCH ANALYSIS (derived from reading Lean + C++ source):

1. [B1] Runtime normal-path success:
   - `.xchg0 1` succeeds with at least two stack items.
   - It swaps top two entries without type checks.
2. [B2] Runtime stack-shape success:
   - On deeper stacks, only top two values are swapped and everything below remains unchanged.
3. [B3] Runtime underflow:
   - Stack size < 2 raises `stkUnd`; no mutation is expected before failure.
4. [B4] Dispatch-path branch:
   - `execInstrStackXchg0` executes `.xchg0` cases and delegates to `next` for all other instructions.
5. [B5] Assembler encoding / range branches:
   - `.xchg0 0` encodes as `0x00` (`.nop`).
   - `.xchg0 1` encodes as `0x01`.
   - `.xchg0 2..15` encodes as short one-byte opcodes.
   - `.xchg0 16..255` encodes as `0x11 xx`.
   - `.xchg0 >= 256` is rejected with `.rangeChk`.
6. [B6] Decoder boundaries and decode aliases:
   - `0x00` decodes as `.nop`, `0x01` decodes as `.xchg0 1`.
   - `0x02..0x0f` decodes as `.xchg0 idx`.
   - `0x10` needs a second byte and fails as `.invOpcode` when truncated.
   - `0x11 xx` decodes as `.xchg0 xx`.
7. [B7] Gas accounting:
   - Fixed decode-width gas model for this instruction; no argument-dependent penalty.
   - Exact budget should succeed; exact-1 budget should fail before completion.

TOTAL BRANCHES: 7

Each oracle test below is tagged with one or more [Bn] labels.
-/

private def swapId : InstrId := { name := "SWAP" }

private def swapInstr : Instr := .xchg0 1

private def dispatchSentinel : Int := 49321

private def swapExactGas : Int :=
  computeExactGasBudget swapInstr

private def swapExactGasMinusOne : Int :=
  computeExactGasBudgetMinusOne swapInstr

private def swapGasExact : OracleGasLimits :=
  oracleGasLimitsExact swapExactGas

private def swapGasExactMinusOne : OracleGasLimits :=
  oracleGasLimitsExactMinusOne swapExactGasMinusOne

private def mkCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[swapInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := swapId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkRawCase
    (name : String)
    (code : Cell)
    (stack : Array Value)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := swapId
    codeCell? := some code
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def raw8 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 8) #[]

private def raw16 (w : Nat) : Cell :=
  Cell.mkOrdinary (natToBits w 16) #[]

private def runSwapDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrStackXchg0 swapInstr stack

private def cellA : Cell := Cell.mkOrdinary (natToBits 0xa5 8) #[]
private def cellB : Cell := Cell.mkOrdinary (natToBits 0x5a 8) #[cellA]
private def fullSliceA : Slice := Slice.ofCell cellA
private def fullSliceB : Slice := Slice.ofCell cellB
private def builderA : Builder := Builder.empty
private def emptyTuple : Value := .tuple #[]
private def contQuit : Value := .cont (.quit 0)

private def noiseA : Array Value :=
  #[.null, .cell cellA, .slice fullSliceA, .builder builderA, intV 17]

private def noiseB : Array Value :=
  #[.cell cellB, .slice fullSliceB, intV 9, .null, .cont (.quit 0), intV (-5)]

private def depth17 : Array Value :=
  Array.range 17 |>.map (fun i => intV (Int.ofNat i))

private def depth17WithTail : Array Value :=
  (Array.range 16 |>.map (fun i => intV (-(Int.ofNat i + 1)))
    |>.push (intV 42)
    |>.push (intV 7))

private def xchg0Idx16Code : Cell := raw16 0x1110
private def xchg0Idx0LongCode : Cell := raw16 0x1100
private def swapCode : Cell := raw8 0x01
private def nopCode : Cell := raw8 0x00
private def xchg2Code : Cell := raw8 0x02
private def xchg3Code : Cell := raw8 0x03
private def xchg15Code : Cell := raw8 0x0f
private def truncated10Code : Cell := raw8 0x10
private def truncated15LongXchgCode : Cell := Cell.mkOrdinary (natToBits 0x11 15) #[]
private def invalidFFCode : Cell := raw8 0xff
private def truncated4Code : Cell := Cell.mkOrdinary (natToBits 0x1 4) #[]

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
        throw (IO.userError s!"{label}: expected bits {expectedBits}, got {bits}")
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
      throw (IO.userError s!"{label}: expected decode error, got instr={reprStr instr} bits={bits}")

private def expectAssembleOk
    (label : String)
    (instr : Instr)
    (decodeAs : Instr)
    (expectedBits : Nat) : IO Unit := do
  match assembleCp0 [instr] with
  | .ok c =>
      expectDecodeOk label c decodeAs expectedBits
  | .error e =>
      throw (IO.userError s!"{label}: expected assemble success, got {e}")

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

private def pickFromPool {α : Type} [Inhabited α] (pool : Array α) (rng : StdGen) : α × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def genSwapFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 12
  let (a, rng2) := pickInt257Boundary rng1
  let (b, rng3) := pickInt257Boundary rng2
  let (noise1, rng4) := pickFromPool noiseA rng3
  let (noise2, rng5) := pickFromPool noiseB rng4
  let shapeCase : OracleCase :=
    if shape = 0 then
      mkCase "fuzz/ok/pair-boundary-ascending" #[intV a, intV b]
    else if shape = 1 then
      mkCase "fuzz/ok/pair-boundary-descending" #[intV b, intV a]
    else if shape = 2 then
      mkCase "fuzz/ok/pair-hetero" #[intV a, noise1]
    else if shape = 3 then
      mkCase "fuzz/ok/size3" #[noise1, intV a, intV b]
    else if shape = 4 then
      mkCase "fuzz/ok/size6" #[noise1, intV a, intV b, noise2, .cell cellB, intV (-a)]
    else if shape = 5 then
      mkRawCase "fuzz/ok/raw-swap" swapCode depth17WithTail
    else if shape = 6 then
      mkCase "fuzz/ok/depth17-xchg0-16" depth17 #[.xchg0 16]
    else if shape = 7 then
      mkRawCase "fuzz/ok/raw-long-idx0" xchg0Idx0LongCode depth17
    else if shape = 8 then
      mkCase "fuzz/ok/xchg0-0-noop" #[intV 4, intV 9] #[.xchg0 0]
    else if shape = 9 then
      mkCase "fuzz/err/depth17-xchg0-255-underflow" depth17 #[.xchg0 255]
    else if shape = 10 then
      mkCase "fuzz/err/underflow-empty" #[]
    else if shape = 11 then
      mkCase "fuzz/err/underflow-single-int" #[intV a]
    else
      mkCase "fuzz/err/underflow-single-cell" #[.cell cellA]
  let (tag, rng6) := randNat rng5 0 999_999
  ({ shapeCase with name := s!"{shapeCase.name}-{tag}" }, rng6)

def suite : InstrSuite where
  id := swapId
  unit := #[
    { name := "unit/runtime/dispatch/swap-two-top-values"
      run := do
        expectOkStack "unit/runtime/swap-two-top-values" (runSwapDirect #[intV 9, intV 4]) #[intV 4, intV 9]
    },
    { name := "unit/runtime/dispatch-fallback-to-next"
      run := do
        let ok := runHandlerDirectWithNext execInstrStackXchg0 (.add) (VM.push (intV dispatchSentinel)) #[]
        expectOkStack "unit/runtime/dispatch-fallback-to-next" ok #[intV dispatchSentinel]
    },
    { name := "unit/asm/xchg0-0-encodes-as-nop"
      run := do
        expectAssembleOk "unit/asm/xchg0-0-encodes-as-nop" (.xchg0 0) .nop 8
    },
    { name := "unit/asm/xchg0-1-roundtrip"
      run := do
        expectAssembleOk "unit/asm/xchg0-1-roundtrip" swapInstr (.xchg0 1) 8
    },
    { name := "unit/asm/xchg0-2-roundtrip"
      run := do
        expectAssembleOk "unit/asm/xchg0-2-roundtrip" (.xchg0 2) (.xchg0 2) 8
    },
    { name := "unit/asm/xchg0-15-roundtrip"
      run := do
        expectAssembleOk "unit/asm/xchg0-15-roundtrip" (.xchg0 15) (.xchg0 15) 8
    },
    { name := "unit/asm/xchg0-16-long-roundtrip"
      run := do
        expectAssembleOk "unit/asm/xchg0-16-long-roundtrip" (.xchg0 16) (.xchg0 16) 16
    },
    { name := "unit/asm/xchg0-255-long-roundtrip"
      run := do
        expectAssembleOk "unit/asm/xchg0-255-long-roundtrip" (.xchg0 255) (.xchg0 255) 16
    },
    { name := "unit/asm/xchg0-256-range-error"
      run := do
        expectAssembleErr "unit/asm/xchg0-256-range-error" (.xchg0 256) .rangeChk
    },
    { name := "unit/decode/swap-short"
      run := do
        expectDecodeOk "unit/decode/swap-short" swapCode (.xchg0 1) 8
    },
    { name := "unit/decode/xchg0-0-nop"
      run := do
        expectDecodeOk "unit/decode/xchg0-0-nop" nopCode .nop 8
    },
    { name := "unit/decode/xchg0-2"
      run := do
        expectDecodeOk "unit/decode/xchg0-2" xchg2Code (.xchg0 2) 8
    },
    { name := "unit/decode/xchg0-3"
      run := do
        expectDecodeOk "unit/decode/xchg0-3" xchg3Code (.xchg0 3) 8
    },
    { name := "unit/decode/xchg0-15"
      run := do
        expectDecodeOk "unit/decode/xchg0-15" xchg15Code (.xchg0 15) 8
    },
    { name := "unit/decode/xchg0-16"
      run := do
        expectDecodeOk "unit/decode/xchg0-16" xchg0Idx16Code (.xchg0 16) 16
    },
    { name := "unit/decode/truncated-8bit-x10"
      run := do
        expectDecodeErr "unit/decode/truncated-8bit-x10" truncated10Code .invOpcode
    },
    { name := "unit/decode/truncated-15bit-11"
      run := do
        match decodeCp0WithBits (Slice.ofCell truncated15LongXchgCode) with
        | .ok (.nop, 8, _) => pure ()
        | .ok (instr, bits, _) =>
            throw (IO.userError s!"unit/decode/truncated-15bit-11: expected alias nop(8), got {reprStr instr} ({bits} bits)")
        | .error e =>
            throw (IO.userError s!"unit/decode/truncated-15bit-11: expected alias nop(8), got error {e}")
    },
    { name := "unit/decode/truncated-4bit-prefix"
      run := do
        expectDecodeErr "unit/decode/truncated-4bit-prefix" truncated4Code .invOpcode
    },
    { name := "unit/decode/invalid-ff"
      run := do
        expectDecodeErr "unit/decode/invalid-ff" invalidFFCode .invOpcode
    },
    { name := "unit/gas/exact-vs-minus-one"
      run := do
        if swapGasExact.gasLimit != swapExactGas then
          throw (IO.userError s!"unit/gas/exact-vs-minus-one: gasLimit {swapGasExact.gasLimit} != expected {swapExactGas}")
        if swapGasExactMinusOne.gasLimit >= swapGasExact.gasLimit then
          throw (IO.userError s!"unit/gas/exact-vs-minus-one: gasMinusOne {swapGasExactMinusOne.gasLimit} must be below exact {swapGasExact.gasLimit}")
    }
  ]
  oracle := #[
    -- [B1]
    mkCase "oracle/ok/basic/pos-pos" #[intV 17, intV 42],
    -- [B1]
    mkCase "oracle/ok/basic/neg-neg" #[intV (-3), intV (-11)],
    -- [B1]
    mkCase "oracle/ok/basic/zeros" #[intV 0, intV 0],
    -- [B1]
    mkCase "oracle/ok/basic/max-min" #[intV maxInt257, intV minInt257],
    -- [B1]
    mkCase "oracle/ok/basic/min-max" #[intV minInt257, intV maxInt257],
    -- [B1]
    mkCase "oracle/ok/basic/null-int" #[.null, intV 7],
    -- [B1]
    mkCase "oracle/ok/basic/int-null" #[intV 7, .null],
    -- [B1]
    mkCase "oracle/ok/basic/cell-cell" #[.cell cellA, .cell cellB],
    -- [B1]
    mkCase "oracle/ok/basic/slice-builder" #[.slice fullSliceA, .builder builderA],
    -- [B1]
    mkCase "oracle/ok/basic/tuple-cont" #[emptyTuple, contQuit],
    -- [B1]
    mkCase "oracle/ok/basic/builder-tuple" #[.builder builderA, emptyTuple],
    -- [B1]
    mkCase "oracle/ok/basic/non-int-hetero" #[.builder builderA, .slice fullSliceB],
    -- [B2]
    mkCase "oracle/ok/deep/prefix-3" #[.cell cellA, intV 11, intV 22],
    -- [B2]
    mkCase "oracle/ok/deep/prefix-6" #[.null, .builder builderA, .slice fullSliceA, intV 7, .cell cellB, intV (-5)],
    -- [B2]
    mkCase "oracle/ok/deep/hetero-5" #[.cell cellA, intV 1, emptyTuple, .slice fullSliceB, intV 9],
    -- [B2]
    mkCase "oracle/ok/deep/large-prefix-7" (depth17.take 7),
    -- [B2]
    mkCase "oracle/ok/deep/large-prefix-8" (depth17.take 8 |>.set! 7 (intV 999)),
    -- [B2]
    mkCase "oracle/ok/deep/large-prefix-16" depth17WithTail,
    -- [B2]
    mkCase "oracle/ok/deep/large-prefix-17-xchg1" (depth17.push (intV 42)) #[.xchg0 1],
    -- [B3]
    mkCase "oracle/err/underflow/empty-stack" #[],
    -- [B3]
    mkCase "oracle/err/underflow/single-int" #[intV 1],
    -- [B3]
    mkCase "oracle/err/underflow/single-null" #[.null],
    -- [B3]
    mkCase "oracle/err/underflow/single-cell" #[.cell cellA],
    -- [B3]
    mkCase "oracle/err/underflow/single-cont" #[contQuit],
    -- [B3]
    mkCase "oracle/err/underflow/xchg0-2-short" #[intV 1, intV 2] #[.xchg0 2],
    -- [B3]
    mkRawCase "oracle/err/underflow/raw-swap-with-rawx" xchg0Idx16Code #[intV 1],
    -- [B4]
    mkCase "oracle/ok/encode/xchg0-0-is-noop" #[intV 4, intV 8] #[.xchg0 0],
    -- [B4]
    mkCase "oracle/ok/encode/xchg0-2-neighbor" #[intV 1, intV 2, intV 3] #[.xchg0 2],
    -- [B4]
    mkCase "oracle/ok/encode/xchg0-3-neighbor" #[intV 9, intV 1, intV 7] #[.xchg0 3],
    -- [B4]
    mkCase "oracle/ok/encode/xchg0-15-neighbor" #[intV (-1), intV 20, intV 30] #[.xchg0 15],
    -- [B4]
    mkCase "oracle/ok/encode/xchg0-16-long" depth17 #[.xchg0 16],
    -- [B4]
    mkCase "oracle/ok/encode/xchg0-255-long-underflow" (depth17.take 17) #[.xchg0 255],
    -- [B5]
    mkRawCase "oracle/ok/raw/opcode-01-swap" swapCode #[intV 5, intV 6],
    -- [B5]
    mkRawCase "oracle/ok/raw/opcode-00-nop-neighbor" nopCode #[intV 5, intV 6],
    -- [B5]
    mkRawCase "oracle/ok/raw/opcode-02-neighbor" xchg2Code #[intV 9, intV 10, intV 11],
    -- [B5]
    mkRawCase "oracle/ok/raw/opcode-03-neighbor" xchg3Code #[intV 1, intV 2, intV 3],
    -- [B5]
    mkRawCase "oracle/ok/raw/opcode-0f-neighbor" xchg15Code #[intV 1, intV 2, intV 3],
    -- [B5]
    mkRawCase "oracle/ok/raw/long-xchg0-16" xchg0Idx16Code depth17,
    -- [B5]
    mkRawCase "oracle/ok/raw/long-xchg0-0" xchg0Idx0LongCode depth17,
    -- [B6]
    mkRawCase "oracle/err/raw/truncated-8bit-x10" truncated10Code #[intV 1, intV 2],
    -- [B6]
    mkRawCase "oracle/err/raw/truncated-15bit-0x11" truncated15LongXchgCode #[intV 1, intV 2],
    -- [B6]
    mkRawCase "oracle/err/raw/truncated-4bit-prefix" truncated4Code #[intV 1],
    -- [B6]
    mkRawCase "oracle/err/raw/invalid-ff" invalidFFCode #[intV 1],
    -- [B7]
    mkCase "oracle/gas/exact-budget-succeeds"
      #[intV 8, intV 9]
      (#[.pushInt (.num swapExactGas), .tonEnvOp .setGasLimit, swapInstr])
      swapGasExact,
    -- [B7]
    mkCase "oracle/gas/exact-minus-one-fails"
      #[intV 8, intV 9]
      (#[.pushInt (.num swapExactGasMinusOne), .tonEnvOp .setGasLimit, swapInstr])
      swapGasExactMinusOne
  ]
  fuzz := #[
    { seed := fuzzSeedForInstr swapId
      count := 500
      gen := genSwapFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Stack.SWAP
