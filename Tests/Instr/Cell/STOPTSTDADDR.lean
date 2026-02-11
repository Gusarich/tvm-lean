import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STOPTSTDADDR

/-
STOPTSTDADDR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.tonEnvOp (.stOptStdAddr quiet)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STOPTSTDADDR`: `0xfa54`, `STOPTSTDADDRQ`: `0xfa55`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa54/0xfa55` decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (no `STOPTSTDADDR` handler/opcode)
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_opt_std_address`, non-quiet path used by `0xfa54`).

Branch map used for this suite (`quiet = false` only):
- Lean STOPTSTDADDR path: 8 branch sites / 10 terminal outcomes
  (`checkUnderflow 2`; top builder pop/type; second pop kind split: null/slice/other;
   null-capacity guard; slice validity/capacity conjunction; success append/store-00;
   failure to `cellOv`; non-slice to `typeChk`).
- C++ STOPTSTDADDR path: 7 branch sites / 9 aligned outcomes
  (`check_underflow(2)`; `pop_builder`; `pop`; null branch capacity;
   `as_slice()` type split; `is_valid_std_msg_addr` + capacity; success or `cell_ov`/`type_chk`).

Key risk areas:
- stack order is `... (slice|null) builder` (builder on top);
- non-quiet has no `rangeChk` branch; invalid std-address shapes map to `cellOv`;
- `null` stores exactly `addr_none$00` (2 zero bits);
- `slice` path requires exact modern std-address shape (`10 0 wc:int8 addr:256`, no refs);
- quiet opcode (`0xfa55`) must remain decode-distinct while this suite targets non-quiet semantics.
-/

private def stOptStdAddrId : InstrId := { name := "STOPTSTDADDR" }

private def stOptStdAddrInstr : Instr :=
  .tonEnvOp (.stOptStdAddr false)

private def stOptStdAddrQInstr : Instr :=
  .tonEnvOp (.stOptStdAddr true)

private def mkStOptStdAddrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[stOptStdAddrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stOptStdAddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStOptStdAddrProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := stOptStdAddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStOptStdAddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr stOptStdAddrInstr stack

private def runStOptStdAddrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 436)) stack

private def stdAddrBits (wc : Nat) (addr : Nat) : BitString :=
  natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits wc 8 ++ natToBits addr 256

private def mkStdAddrSlice (wc : Nat) (addr : Nat) : Slice :=
  mkSliceFromBits (stdAddrBits wc addr)

private def validStdWc0Addr0 : Slice := mkStdAddrSlice 0 0
private def validStdWc255Addr1 : Slice := mkStdAddrSlice 255 1
private def validStdWc42Addr4660 : Slice := mkStdAddrSlice 42 4660
private def validStdWc1Addr255 : Slice := mkStdAddrSlice 1 255
private def validStdWc127Addr65535 : Slice := mkStdAddrSlice 127 65535

private def wrongTagSlice : Slice :=
  mkSliceFromBits (natToBits 0b00 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def anycastOneSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 1 1 ++ natToBits 0 8 ++ natToBits 1 256)

private def shortStdSlice266 : Slice :=
  mkSliceFromBits ((stdAddrBits 0 0).extract 0 266)

private def longStdSlice268 : Slice :=
  mkSliceFromBits (stdAddrBits 0 0 ++ #[true])

private def shortZeroSlice : Slice :=
  mkSliceFromBits #[]

private def stdSliceWithRef : Slice :=
  Slice.ofCell (Cell.mkOrdinary (stdAddrBits 0 5) #[Cell.empty])

private def appendSliceToBuilder (b : Builder) (s : Slice) : Builder :=
  let c := s.toCellRemaining
  { bits := b.bits ++ c.bits
    refs := b.refs ++ c.refs }

private def stOptNullOverflowProgram : Array Instr :=
  build1023WithFixed .stu ++ #[.pushNull, .xchg0 1, stOptStdAddrInstr]

private def stOptNullOverflowProgramWithNoise : Array Instr :=
  #[.pushNull] ++ stOptNullOverflowProgram

private def stOptNullSuccessProgram : Array Instr :=
  #[.newc, .pushNull, .xchg0 1, stOptStdAddrInstr]

private def stOptStdAddrSetGasExact : Int :=
  computeExactGasBudget stOptStdAddrInstr

private def stOptStdAddrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne stOptStdAddrInstr

private def stOptWcPool : Array Nat := #[0, 1, 42, 127, 255]

private def stOptAddrPool : Array Nat := #[0, 1, 2, 17, 255, 256, 4095, 65535]

private def pickWc (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stOptWcPool.size - 1)
  (stOptWcPool[idx]!, rng')

private def pickAddr (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (stOptAddrPool.size - 1)
  (stOptAddrPool[idx]!, rng')

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 97
    else .cell Cell.empty
  (noise, rng')

private def genStOptStdAddrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  if shape = 0 then
    (mkStOptStdAddrCase "fuzz/ok/null-empty-builder" #[.null, .builder Builder.empty], rng1)
  else if shape = 1 then
    let (wc, rng2) := pickWc rng1
    let (addr, rng3) := pickAddr rng2
    (mkStOptStdAddrCase s!"fuzz/ok/slice/wc-{wc}-addr-{addr}"
      #[.slice (mkStdAddrSlice wc addr), .builder Builder.empty], rng3)
  else if shape = 2 then
    let (wc, rng2) := pickWc rng1
    let (addr, rng3) := pickAddr rng2
    let (noise, rng4) := pickNoise rng3
    (mkStOptStdAddrCase s!"fuzz/ok/deep-stack/wc-{wc}-addr-{addr}"
      #[noise, .slice (mkStdAddrSlice wc addr), .builder Builder.empty], rng4)
  else if shape = 3 then
    let (noise, rng2) := pickNoise rng1
    (mkStOptStdAddrCase "fuzz/ok/deep-stack/null"
      #[noise, .null, .builder Builder.empty], rng2)
  else if shape = 4 then
    (mkStOptStdAddrCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStOptStdAddrCase "fuzz/underflow/one-null" #[.null], rng1)
  else if shape = 6 then
    (mkStOptStdAddrCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng1)
  else if shape = 7 then
    (mkStOptStdAddrCase "fuzz/type/top-not-builder" #[.null, intV 1], rng1)
  else if shape = 8 then
    (mkStOptStdAddrCase "fuzz/type/value-not-slice-or-null" #[intV 3, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkStOptStdAddrCase "fuzz/invalid/wrong-tag" #[.slice wrongTagSlice, .builder Builder.empty], rng1)
  else if shape = 10 then
    (mkStOptStdAddrCase "fuzz/invalid/anycast-one" #[.slice anycastOneSlice, .builder Builder.empty], rng1)
  else if shape = 11 then
    (mkStOptStdAddrCase "fuzz/invalid/short-266" #[.slice shortStdSlice266, .builder Builder.empty], rng1)
  else if shape = 12 then
    (mkStOptStdAddrCase "fuzz/invalid/has-ref" #[.slice stdSliceWithRef, .builder Builder.empty], rng1)
  else if shape = 13 then
    (mkStOptStdAddrProgramCase "fuzz/cellov/full-builder-null" #[] stOptNullOverflowProgram, rng1)
  else if shape = 14 then
    (mkStOptStdAddrCase "fuzz/gas/exact" #[.null, .builder Builder.empty]
      #[.pushInt (.num stOptStdAddrSetGasExact), .tonEnvOp .setGasLimit, stOptStdAddrInstr], rng1)
  else if shape = 15 then
    (mkStOptStdAddrCase "fuzz/gas/exact-minus-one" #[.null, .builder Builder.empty]
      #[.pushInt (.num stOptStdAddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, stOptStdAddrInstr], rng1)
  else
    (mkStOptStdAddrCase "fuzz/invalid/long-268" #[.slice longStdSlice268, .builder Builder.empty], rng1)

def suite : InstrSuite where
  id := stOptStdAddrId
  unit := #[
    { name := "unit/direct/success-order-and-boundaries"
      run := do
        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let expectedNull := prefBuilder.storeBits (natToBits 0 2)
        expectOkStack "ok/null-appends-addr-none"
          (runStOptStdAddrDirect #[.null, .builder prefBuilder])
          #[.builder expectedNull]

        let expectedSlice := appendSliceToBuilder prefBuilder validStdWc42Addr4660
        expectOkStack "ok/slice-appends-std-address"
          (runStOptStdAddrDirect #[.slice validStdWc42Addr4660, .builder prefBuilder])
          #[.builder expectedSlice]

        let b756 := Builder.empty.storeBits (Array.replicate 756 false)
        let expectedBoundary := appendSliceToBuilder b756 validStdWc0Addr0
        expectOkStack "ok/slice-capacity-boundary-756-plus-267"
          (runStOptStdAddrDirect #[.slice validStdWc0Addr0, .builder b756])
          #[.builder expectedBoundary]

        expectOkStack "ok/deep-stack-preserve-below"
          (runStOptStdAddrDirect #[intV 7, .null, .builder Builder.empty])
          #[intV 7, .builder (Builder.empty.storeBits (natToBits 0 2))] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runStOptStdAddrDirect #[]) .stkUnd
        expectErr "underflow/one-null" (runStOptStdAddrDirect #[.null]) .stkUnd
        expectErr "underflow/one-builder" (runStOptStdAddrDirect #[.builder Builder.empty]) .stkUnd

        expectErr "type/top-not-builder"
          (runStOptStdAddrDirect #[.null, intV 1]) .typeChk
        expectErr "type/value-not-slice-or-null"
          (runStOptStdAddrDirect #[intV 3, .builder Builder.empty]) .typeChk
        expectErr "type/reversed-args"
          (runStOptStdAddrDirect #[.builder Builder.empty, .slice validStdWc0Addr0]) .typeChk
        expectErr "type/both-wrong"
          (runStOptStdAddrDirect #[intV 1, .null]) .typeChk }
    ,
    { name := "unit/direct/range-shape-and-overflow-as-cellov"
      run := do
        expectErr "invalid/wrong-tag"
          (runStOptStdAddrDirect #[.slice wrongTagSlice, .builder Builder.empty]) .cellOv
        expectErr "invalid/anycast-one"
          (runStOptStdAddrDirect #[.slice anycastOneSlice, .builder Builder.empty]) .cellOv
        expectErr "invalid/short-266-bits"
          (runStOptStdAddrDirect #[.slice shortStdSlice266, .builder Builder.empty]) .cellOv
        expectErr "invalid/long-268-bits"
          (runStOptStdAddrDirect #[.slice longStdSlice268, .builder Builder.empty]) .cellOv
        expectErr "invalid/zero-bits"
          (runStOptStdAddrDirect #[.slice shortZeroSlice, .builder Builder.empty]) .cellOv
        expectErr "invalid/has-ref"
          (runStOptStdAddrDirect #[.slice stdSliceWithRef, .builder Builder.empty]) .cellOv

        let b1021 := Builder.empty.storeBits (Array.replicate 1021 false)
        expectOkStack "ok/null-capacity-boundary-1021-plus-2"
          (runStOptStdAddrDirect #[.null, .builder b1021])
          #[.builder (b1021.storeBits (natToBits 0 2))]

        let b1022 := Builder.empty.storeBits (Array.replicate 1022 false)
        expectErr "cellov/null-1022-plus-2-overflow"
          (runStOptStdAddrDirect #[.null, .builder b1022]) .cellOv
        expectErr "cellov/full-builder-plus-valid-slice"
          (runStOptStdAddrDirect #[.slice validStdWc255Addr1, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let nonQuietCode ←
          match assembleCp0 [stOptStdAddrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble non-quiet failed: {e}")
        if nonQuietCode.bits = natToBits 0xfa54 16 then
          pure ()
        else
          throw (IO.userError s!"stoptstdaddr encode mismatch: got bits {nonQuietCode.bits}")

        let quietCode ←
          match assembleCp0 [stOptStdAddrQInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble quiet failed: {e}")
        if quietCode.bits = natToBits 0xfa55 16 then
          pure ()
        else
          throw (IO.userError s!"stoptstdaddrq encode mismatch: got bits {quietCode.bits}")

        let program : Array Instr := #[stOptStdAddrInstr, stOptStdAddrQInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/stoptstdaddr" s0 stOptStdAddrInstr 16
        let s2 ← expectDecodeStep "decode/stoptstdaddrq" s1 stOptStdAddrQInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStOptStdAddrDispatchFallback #[.null])
          #[.null, intV 436] }
  ]
  oracle := #[
    mkStOptStdAddrCase "ok/null-empty-builder" #[.null, .builder Builder.empty],
    mkStOptStdAddrCase "ok/null-deep-stack" #[.null, .null, .builder Builder.empty],
    mkStOptStdAddrCase "ok/slice-wc0-addr0" #[.slice validStdWc0Addr0, .builder Builder.empty],
    mkStOptStdAddrCase "ok/slice-wc255-addr1" #[.slice validStdWc255Addr1, .builder Builder.empty],
    mkStOptStdAddrCase "ok/slice-wc42-addr4660" #[.slice validStdWc42Addr4660, .builder Builder.empty],
    mkStOptStdAddrCase "ok/slice-wc1-addr255-deep" #[intV 7, .slice validStdWc1Addr255, .builder Builder.empty],
    mkStOptStdAddrCase "ok/slice-wc127-addr65535" #[.slice validStdWc127Addr65535, .builder Builder.empty],
    mkStOptStdAddrProgramCase "ok/program/newc-null-store" #[] stOptNullSuccessProgram,

    mkStOptStdAddrCase "underflow/empty" #[],
    mkStOptStdAddrCase "underflow/one-null" #[.null],
    mkStOptStdAddrCase "underflow/one-builder" #[.builder Builder.empty],
    mkStOptStdAddrCase "type/top-not-builder" #[.null, intV 1],
    mkStOptStdAddrCase "type/value-not-slice-or-null" #[intV 3, .builder Builder.empty],
    mkStOptStdAddrCase "type/reversed-args" #[.builder Builder.empty, .slice validStdWc0Addr0],

    mkStOptStdAddrCase "invalid/wrong-tag" #[.slice wrongTagSlice, .builder Builder.empty],
    mkStOptStdAddrCase "invalid/anycast-one" #[.slice anycastOneSlice, .builder Builder.empty],
    mkStOptStdAddrCase "invalid/short-266-bits" #[.slice shortStdSlice266, .builder Builder.empty],
    mkStOptStdAddrCase "invalid/long-268-bits" #[.slice longStdSlice268, .builder Builder.empty],
    mkStOptStdAddrCase "invalid/zero-bits" #[.slice shortZeroSlice, .builder Builder.empty],
    mkStOptStdAddrCase "invalid/has-ref" #[.slice stdSliceWithRef, .builder Builder.empty],

    mkStOptStdAddrCase "gas/exact-cost-succeeds" #[.null, .builder Builder.empty]
      #[.pushInt (.num stOptStdAddrSetGasExact), .tonEnvOp .setGasLimit, stOptStdAddrInstr],
    mkStOptStdAddrCase "gas/exact-minus-one-out-of-gas" #[.null, .builder Builder.empty]
      #[.pushInt (.num stOptStdAddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, stOptStdAddrInstr],

    mkStOptStdAddrProgramCase "cellov/full-builder-null-via-program" #[] stOptNullOverflowProgram,
    mkStOptStdAddrProgramCase "cellov/full-builder-null-via-program-with-noise" #[] stOptNullOverflowProgramWithNoise
  ]
  fuzz := #[
    { seed := 2026021010
      count := 500
      gen := genStOptStdAddrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STOPTSTDADDR
