import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STOPTSTDADDRQ

/-
STOPTSTDADDRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.tonEnvOp (.stOptStdAddr true)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STOPTSTDADDRQ` encode: `0xfa55`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa55` decode to `.tonEnvOp (.stOptStdAddr true)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (no STOPTSTDADDR{Q} implementation)
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_opt_std_address`, opcodes `0xfa54/0xfa55`).

Branch map used for this suite:
- Lean STOPTSTDADDRQ path: 9 branch sites / 14 terminal outcomes
  (`checkUnderflow 2`; builder pop/type gate; operand split `null|slice|other`;
   `null` capacity branch; std-address validity checks (tag/len/refs) + capacity branch;
   quiet failures restore operands and push status `-1`; success pushes status `0`).
- C++ STOPTSTDADDRQ path: aligned behavior in `exec_store_opt_std_address`
  (`check_underflow(2)`; `pop_builder`; null-vs-slice-vs-type path; quiet bool status).

Key risk areas:
- stack order is `... (slice|null|other) builder` (builder on top);
- quiet type mismatch must push `null` (not original non-slice value) then builder then `-1`;
- quiet invalid-std and quiet overflow both return `-1`, preserving original operand/builder order;
- `null` success stores exactly `addr_none$00` (`00`) and returns status `0`.
-/

private def stoptstdaddrqId : InstrId := { name := "STOPTSTDADDRQ" }

private def stoptstdaddrqInstr : Instr := .tonEnvOp (.stOptStdAddr true)

private def mkStoptstdaddrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stoptstdaddrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stoptstdaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStoptstdaddrqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stoptstdaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStoptstdaddrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr stoptstdaddrqInstr stack

private def runStoptstdaddrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 955)) stack

private def stoptstdaddrqSetGasExact : Int :=
  computeExactGasBudget stoptstdaddrqInstr

private def stoptstdaddrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stoptstdaddrqInstr

private def mkCellWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  { (Builder.empty.storeBits bits) with refs := refs }.finalize

private def mkStdAddrBits (wc : Nat) (addr : Nat) : BitString :=
  natToBits 0b100 3 ++ natToBits wc 8 ++ natToBits addr 256

private def mkStdAddrCell (wc : Nat) (addr : Nat) : Cell :=
  mkCellWithBitsAndRefs (mkStdAddrBits wc addr)

private def mkStdAddrSlice (wc : Nat) (addr : Nat) : Slice :=
  Slice.ofCell (mkStdAddrCell wc addr)

private def appendCellToBuilder (b : Builder) (c : Cell) : Builder :=
  { bits := b.bits ++ c.bits
    refs := b.refs ++ c.refs }

private def addrNoneBuilder : Builder :=
  Builder.empty.storeBits (Array.replicate 2 false)

private def stdCellZero : Cell :=
  mkStdAddrCell 0 0

private def stdCellAlt : Cell :=
  mkStdAddrCell 255 65535

private def stdSliceZero : Slice :=
  Slice.ofCell stdCellZero

private def stdSliceAlt : Slice :=
  Slice.ofCell stdCellAlt

private def invalidTagSlice : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs (natToBits 0b101 3 ++ natToBits 0 8 ++ natToBits 0 256))

private def invalidShortSlice : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs (natToBits 0b100 3 ++ natToBits 0 8 ++ natToBits 0 255))

private def invalidLongSlice : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs (natToBits 0b100 3 ++ natToBits 0 8 ++ natToBits 0 257))

private def invalidRefSlice : Slice :=
  Slice.ofCell ({ (Builder.empty.storeBits (mkStdAddrBits 1 1)) with refs := #[Cell.empty] }.finalize)

private def quietOverflowBuilderProgram : Array Instr :=
  build1023WithFixed (fun bits => .stu bits)

private def quietOverflowProgram : Array Instr :=
  quietOverflowBuilderProgram ++ #[stoptstdaddrqInstr]

private def newcThenStoptstdaddrqProgram : Array Instr :=
  #[.newc, stoptstdaddrqInstr]

private def wcBoundaryPool : Array Nat :=
  #[0, 1, 2, 127, 128, 254, 255]

private def addrBoundaryPool : Array Nat :=
  #[0, 1, 2, 255, 256, 257, 4095, 65535]

private def pickWcBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (wcBoundaryPool.size - 1)
  (wcBoundaryPool[idx]!, rng')

private def pickAddrBoundary (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (addrBoundaryPool.size - 1)
  (addrBoundaryPool[idx]!, rng')

private def pickWcMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickWcBoundary rng1
  else
    randNat rng1 0 255

private def pickAddrMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickAddrBoundary rng1
  else
    randNat rng1 0 65535

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else if pick = 2 then .cell Cell.empty
    else .tuple #[]
  (v, rng1)

private def pickTypeMismatchOperand (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 3
  let v : Value :=
    if pick = 0 then intV 9
    else if pick = 1 then .cell Cell.empty
    else if pick = 2 then .tuple #[]
    else .cont (.quit 0)
  (v, rng1)

private def pickInvalidStdSlice (rng0 : StdGen) : Slice × String × StdGen :=
  let (shape, rng1) := randNat rng0 0 3
  let (wc, rng2) := pickWcMixed rng1
  let (addr, rng3) := pickAddrMixed rng2
  if shape = 0 then
    (Slice.ofCell (mkCellWithBitsAndRefs (natToBits 0b101 3 ++ natToBits wc 8 ++ natToBits addr 256)),
      "tag-or-anycast", rng3)
  else if shape = 1 then
    (Slice.ofCell (mkCellWithBitsAndRefs (natToBits 0b100 3 ++ natToBits wc 8 ++ natToBits addr 255)),
      "short-266", rng3)
  else if shape = 2 then
    (Slice.ofCell (mkCellWithBitsAndRefs (natToBits 0b100 3 ++ natToBits wc 8 ++ natToBits addr 257)),
      "long-268", rng3)
  else
    (Slice.ofCell ({ (Builder.empty.storeBits (mkStdAddrBits wc addr)) with refs := #[Cell.empty] }.finalize),
      "has-refs", rng3)

private def genStoptstdaddrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  let (wc, rng2) := pickWcMixed rng1
  let (addr, rng3) := pickAddrMixed rng2
  let goodSlice := mkStdAddrSlice wc addr
  if shape = 0 then
    (mkStoptstdaddrqCase "fuzz/ok/null-empty-builder" #[.null, .builder Builder.empty], rng3)
  else if shape = 1 then
    (mkStoptstdaddrqCase s!"fuzz/ok/std/wc-{wc}/addr-{addr}"
      #[.slice goodSlice, .builder Builder.empty], rng3)
  else if shape = 2 then
    let (noise, rng4) := pickNoiseValue rng3
    (mkStoptstdaddrqCase s!"fuzz/ok/deep/wc-{wc}/addr-{addr}"
      #[noise, .slice goodSlice, .builder Builder.empty], rng4)
  else if shape = 3 then
    (mkStoptstdaddrqCase "fuzz/underflow/empty" #[], rng3)
  else if shape = 4 then
    let (pick, rng4) := randNat rng3 0 2
    let one : Value :=
      if pick = 0 then .null
      else if pick = 1 then intV 3
      else .slice goodSlice
    (mkStoptstdaddrqCase "fuzz/underflow/one-item" #[one], rng4)
  else if shape = 5 then
    let (pick, rng4) := randNat rng3 0 2
    let badTop : Value :=
      if pick = 0 then .null
      else if pick = 1 then intV 1
      else .cell Cell.empty
    (mkStoptstdaddrqCase "fuzz/type/top-not-builder" #[.slice goodSlice, badTop], rng4)
  else if shape = 6 then
    let (bad, rng4) := pickTypeMismatchOperand rng3
    (mkStoptstdaddrqCase "fuzz/quiet/type/operand-non-slice"
      #[bad, .builder Builder.empty], rng4)
  else if shape = 7 then
    let (badSlice, tag, rng4) := pickInvalidStdSlice rng3
    (mkStoptstdaddrqCase s!"fuzz/quiet/range/{tag}" #[.slice badSlice, .builder Builder.empty], rng4)
  else if shape = 8 then
    let (badSlice, tag, rng4) := pickInvalidStdSlice rng3
    let (noise, rng5) := pickNoiseValue rng4
    (mkStoptstdaddrqCase s!"fuzz/quiet/range/deep/{tag}"
      #[noise, .slice badSlice, .builder Builder.empty], rng5)
  else if shape = 9 then
    (mkStoptstdaddrqProgramCase "fuzz/quiet/overflow/null-full-builder"
      #[.null] quietOverflowProgram, rng3)
  else if shape = 10 then
    (mkStoptstdaddrqProgramCase s!"fuzz/quiet/overflow/std-full-builder/wc-{wc}/addr-{addr}"
      #[.slice goodSlice] quietOverflowProgram, rng3)
  else if shape = 11 then
    let (badSlice, tag, rng4) := pickInvalidStdSlice rng3
    (mkStoptstdaddrqProgramCase s!"fuzz/quiet/overflow/invalid-full-builder/{tag}"
      #[.slice badSlice] quietOverflowProgram, rng4)
  else if shape = 12 then
    (mkStoptstdaddrqCase "fuzz/gas/exact"
      #[.null, .builder Builder.empty]
      #[.pushInt (.num stoptstdaddrqSetGasExact), .tonEnvOp .setGasLimit, stoptstdaddrqInstr], rng3)
  else if shape = 13 then
    (mkStoptstdaddrqCase "fuzz/gas/exact-minus-one"
      #[.null, .builder Builder.empty]
      #[.pushInt (.num stoptstdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stoptstdaddrqInstr], rng3)
  else if shape = 14 then
    (mkStoptstdaddrqProgramCase s!"fuzz/ok/program/newc/wc-{wc}/addr-{addr}"
      #[.slice goodSlice] newcThenStoptstdaddrqProgram, rng3)
  else
    let (noise, rng4) := pickNoiseValue rng3
    (mkStoptstdaddrqProgramCase s!"fuzz/ok/program/newc/deep/wc-{wc}/addr-{addr}"
      #[noise, .slice goodSlice] newcThenStoptstdaddrqProgram, rng4)

def suite : InstrSuite where
  id := stoptstdaddrqId
  unit := #[
    { name := "unit/direct/success-status-and-stack-order"
      run := do
        expectOkStack "ok/null-stores-addr-none"
          (runStoptstdaddrqDirect #[.null, .builder Builder.empty])
          #[.builder addrNoneBuilder, intV 0]

        let expectedStdEmpty := appendCellToBuilder Builder.empty stdCellZero
        expectOkStack "ok/std-addr-stores-slice"
          (runStoptstdaddrqDirect #[.slice stdSliceZero, .builder Builder.empty])
          #[.builder expectedStdEmpty, intV 0]

        let baseBuilder : Builder :=
          { (Builder.empty.storeBits (natToBits 5 3)) with refs := #[Cell.empty] }
        let expectedBase := appendCellToBuilder baseBuilder stdCellAlt
        expectOkStack "ok/std-addr-preserve-existing-builder-content"
          (runStoptstdaddrqDirect #[.slice stdSliceAlt, .builder baseBuilder])
          #[.builder expectedBase, intV 0]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStoptstdaddrqDirect #[intV 17, .slice stdSliceZero, .builder Builder.empty])
          #[intV 17, .builder expectedStdEmpty, intV 0] }
    ,
    { name := "unit/direct/quiet-range-type-overflow-return-minus1"
      run := do
        expectOkStack "quiet/overflow-null-full-builder"
          (runStoptstdaddrqDirect #[.null, .builder fullBuilder1023])
          #[.null, .builder fullBuilder1023, intV (-1)]
        expectOkStack "quiet/overflow-std-full-builder"
          (runStoptstdaddrqDirect #[.slice stdSliceZero, .builder fullBuilder1023])
          #[.slice stdSliceZero, .builder fullBuilder1023, intV (-1)]

        expectOkStack "quiet/range-invalid-tag-or-anycast"
          (runStoptstdaddrqDirect #[.slice invalidTagSlice, .builder Builder.empty])
          #[.slice invalidTagSlice, .builder Builder.empty, intV (-1)]
        expectOkStack "quiet/range-invalid-short-len"
          (runStoptstdaddrqDirect #[.slice invalidShortSlice, .builder Builder.empty])
          #[.slice invalidShortSlice, .builder Builder.empty, intV (-1)]
        expectOkStack "quiet/range-invalid-has-refs"
          (runStoptstdaddrqDirect #[.slice invalidRefSlice, .builder Builder.empty])
          #[.slice invalidRefSlice, .builder Builder.empty, intV (-1)]

        expectOkStack "quiet/type-operand-int-pushes-null"
          (runStoptstdaddrqDirect #[intV 9, .builder Builder.empty])
          #[.null, .builder Builder.empty, intV (-1)]
        expectOkStack "quiet/type-operand-cell-pushes-null"
          (runStoptstdaddrqDirect #[.cell Cell.empty, .builder Builder.empty])
          #[.null, .builder Builder.empty, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-builder-type-fail"
      run := do
        expectErr "underflow/empty" (runStoptstdaddrqDirect #[]) .stkUnd
        expectErr "underflow/one-item-null" (runStoptstdaddrqDirect #[.null]) .stkUnd
        expectErr "underflow/one-item-builder" (runStoptstdaddrqDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder-null"
          (runStoptstdaddrqDirect #[.null, .null]) .typeChk
        expectErr "type/top-not-builder-int"
          (runStoptstdaddrqDirect #[.slice stdSliceZero, intV 1]) .typeChk
        expectErr "error-order/builder-type-before-range"
          (runStoptstdaddrqDirect #[.slice invalidTagSlice, intV 0]) .typeChk }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr :=
          #[stoptstdaddrqInstr, .tonEnvOp (.stOptStdAddr false), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stoptstdaddrq" s0 stoptstdaddrqInstr 16
        let s2 ← expectDecodeStep "decode/stoptstdaddr" s1 (.tonEnvOp (.stOptStdAddr false)) 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStoptstdaddrqDispatchFallback #[.null])
          #[.null, intV 955] }
  ]
  oracle := #[
    mkStoptstdaddrqCase "ok/null-empty-builder" #[.null, .builder Builder.empty],
    mkStoptstdaddrqCase "ok/null-deep-stack" #[intV 7, .null, .builder Builder.empty],
    mkStoptstdaddrqCase "ok/std-empty-builder-zero" #[.slice stdSliceZero, .builder Builder.empty],
    mkStoptstdaddrqCase "ok/std-empty-builder-alt" #[.slice stdSliceAlt, .builder Builder.empty],
    mkStoptstdaddrqCase "ok/std-deep-stack" #[.cell Cell.empty, .slice stdSliceAlt, .builder Builder.empty],
    mkStoptstdaddrqProgramCase "ok/program/newc-null" #[.null] newcThenStoptstdaddrqProgram,
    mkStoptstdaddrqProgramCase "ok/program/newc-std" #[.slice stdSliceZero] newcThenStoptstdaddrqProgram,

    mkStoptstdaddrqCase "underflow/empty" #[],
    mkStoptstdaddrqCase "underflow/one-item-null" #[.null],
    mkStoptstdaddrqCase "underflow/one-item-builder" #[.builder Builder.empty],
    mkStoptstdaddrqCase "type/top-not-builder-null" #[.null, .null],
    mkStoptstdaddrqCase "type/top-not-builder-int" #[.slice stdSliceZero, intV 1],

    mkStoptstdaddrqCase "quiet/type/operand-int" #[intV 9, .builder Builder.empty],
    mkStoptstdaddrqCase "quiet/type/operand-cell" #[.cell Cell.empty, .builder Builder.empty],
    mkStoptstdaddrqCase "quiet/type/operand-tuple" #[.tuple #[], .builder Builder.empty],
    mkStoptstdaddrqCase "quiet/range/bad-tag-or-anycast" #[.slice invalidTagSlice, .builder Builder.empty],
    mkStoptstdaddrqCase "quiet/range/short-266" #[.slice invalidShortSlice, .builder Builder.empty],
    mkStoptstdaddrqCase "quiet/range/long-268" #[.slice invalidLongSlice, .builder Builder.empty],
    mkStoptstdaddrqCase "quiet/range/has-refs" #[.slice invalidRefSlice, .builder Builder.empty],

    mkStoptstdaddrqProgramCase "quiet/overflow/null-full-builder" #[.null] quietOverflowProgram,
    mkStoptstdaddrqProgramCase "quiet/overflow/std-full-builder" #[.slice stdSliceZero] quietOverflowProgram,
    mkStoptstdaddrqProgramCase "quiet/overflow/invalid-full-builder" #[.slice invalidTagSlice] quietOverflowProgram,

    mkStoptstdaddrqCase "gas/exact-cost-succeeds" #[.null, .builder Builder.empty]
      #[.pushInt (.num stoptstdaddrqSetGasExact), .tonEnvOp .setGasLimit, stoptstdaddrqInstr],
    mkStoptstdaddrqCase "gas/exact-minus-one-out-of-gas" #[.null, .builder Builder.empty]
      #[.pushInt (.num stoptstdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, stoptstdaddrqInstr]
  ]
  fuzz := #[
    { seed := 2026021016
      count := 500
      gen := genStoptstdaddrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STOPTSTDADDRQ
