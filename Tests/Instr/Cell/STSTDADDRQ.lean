import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.STSTDADDRQ

/-
STSTDADDRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.stStdAddr quiet`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`STSTDADDRQ` encode: `0xfa53`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa53` decode to `.tonEnvOp (.stStdAddr true)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_store_std_address`, `is_valid_std_msg_addr`, quiet path for `STSTDADDRQ`)
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (quiet status convention `push_bool(true => failure, false => success)` used across quiet stores).

Branch map used for this suite (quiet STSTDADDR path):
- handler-match (`.tonEnvOp (.stStdAddr _)` vs fallthrough to `next`);
- hard guards before quiet handling (`checkUnderflow 2`; top must be builder; next must be slice);
- std-address shape guard (`isValidStdMsgAddr`: exact `addr_std$10`, `anycast=0`, no refs, exact bits);
- capacity guard (`builder.canExtendBy` with remaining slice payload);
- quiet success pushes `[builder', 0]`;
- quiet failure (invalid shape or overflow) restores `[slice, builder, -1]`.

Key risk areas:
- stack order is `... slice builder` (builder on top);
- quiet mode does not soften underflow/type failures;
- invalid address shape and capacity overflow both map to status `-1` (no throw);
- opcode mapping must remain aligned with `0xfa53` in both decode and assembler.
-/

private def ststdaddrqId : InstrId := { name := "STSTDADDRQ" }

private def ststdaddrqInstr : Instr :=
  .tonEnvOp (.stStdAddr true)

private def ststdaddrInstr : Instr :=
  .tonEnvOp (.stStdAddr false)

private def mkStstdaddrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ststdaddrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ststdaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def mkStstdaddrqProgramCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr)
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ststdaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runStstdaddrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ststdaddrqInstr stack

private def runStstdaddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ststdaddrInstr stack

private def runStstdaddrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 453)) stack

private def ststdaddrqSetGasExact : Int :=
  computeExactGasBudget ststdaddrqInstr

private def ststdaddrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ststdaddrqInstr

private def mkStdAddrBits (workchainByte : Nat) (addr256 : Nat) : BitString :=
  natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits (workchainByte % 256) 8 ++ natToBits addr256 256

private def mkStdAddrSlice (workchainByte : Nat) (addr256 : Nat) : Slice :=
  mkSliceFromBits (mkStdAddrBits workchainByte addr256)

private def validStdSlice0 : Slice :=
  mkStdAddrSlice 0 0

private def validStdSlice1 : Slice :=
  mkStdAddrSlice 0 1

private def validStdSliceWc255 : Slice :=
  mkStdAddrSlice 255 42

private def validStdSliceWc17 : Slice :=
  mkStdAddrSlice 17 65535

private def invalidTagSlice : Slice :=
  mkSliceFromBits (natToBits 0b00 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def invalidAnycastSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 1 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def invalidShortSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 255)

private def invalidLongSlice : Slice :=
  mkSliceFromBits (mkStdAddrBits 0 0 ++ #[true])

private def invalidRefsSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkStdAddrBits 0 0) #[Cell.empty])

private def appendSliceRemainingToBuilder (b : Builder) (cs : Slice) : Builder :=
  let c := cs.toCellRemaining
  { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }

private def build1023Program : Array Instr :=
  build1023WithFixed .stu

private def quietOverflowProgram : Array Instr :=
  build1023Program ++ #[ststdaddrqInstr]

private def appendPrefixThenStoreProgram : Array Instr :=
  #[
    .newc,
    .pushInt (.num 5), .xchg0 1, .stu 3,
    ststdaddrqInstr
  ]

private def validSlicePool : Array (String × Slice) :=
  #[
    ("wc0-addr0", validStdSlice0),
    ("wc0-addr1", validStdSlice1),
    ("wc255-addr42", validStdSliceWc255),
    ("wc17-addr65535", validStdSliceWc17)
  ]

private def invalidSlicePool : Array (String × Slice) :=
  #[
    ("tag-not-std", invalidTagSlice),
    ("anycast-enabled", invalidAnycastSlice),
    ("short-bits", invalidShortSlice),
    ("long-bits", invalidLongSlice),
    ("nonzero-refs", invalidRefsSlice)
  ]

private def pickSliceFromPool
    (pool : Array (String × Slice))
    (fallback : String × Slice)
    (rng : StdGen) : (String × Slice) × StdGen :=
  if pool.isEmpty then
    (fallback, rng)
  else
    let (idx, rng') := randNat rng 0 (pool.size - 1)
    match pool[idx]? with
    | some entry => (entry, rng')
    | none => (fallback, rng')

private def pickValidSlice (rng : StdGen) : (String × Slice) × StdGen :=
  pickSliceFromPool validSlicePool ("wc0-addr0", validStdSlice0) rng

private def pickInvalidSlice (rng : StdGen) : (String × Slice) × StdGen :=
  pickSliceFromPool invalidSlicePool ("tag-not-std", invalidTagSlice) rng

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 3
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else if pick = 2 then .cell Cell.empty
    else .tuple #[]
  (noise, rng')

private def genStstdaddrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 14
  if shape = 0 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqCase s!"fuzz/ok/direct/{label}" #[.slice cs, .builder Builder.empty], rng2)
  else if shape = 1 then
    let ((label, cs), rng2) := pickValidSlice rng1
    let (noise, rng3) := pickNoise rng2
    (mkStstdaddrqCase s!"fuzz/ok/deep/{label}" #[noise, .slice cs, .builder Builder.empty], rng3)
  else if shape = 2 then
    let ((label, cs), rng2) := pickInvalidSlice rng1
    (mkStstdaddrqCase s!"fuzz/quiet-invalid/{label}" #[.slice cs, .builder Builder.empty], rng2)
  else if shape = 3 then
    let ((label, cs), rng2) := pickInvalidSlice rng1
    let (noise, rng3) := pickNoise rng2
    (mkStstdaddrqCase s!"fuzz/quiet-invalid/deep/{label}" #[noise, .slice cs, .builder Builder.empty], rng3)
  else if shape = 4 then
    (mkStstdaddrqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 5 then
    (mkStstdaddrqCase "fuzz/underflow/one-builder" #[.builder Builder.empty], rng1)
  else if shape = 6 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqCase s!"fuzz/underflow/one-slice/{label}" #[.slice cs], rng2)
  else if shape = 7 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqCase s!"fuzz/type/top-not-builder/{label}" #[.slice cs, .null], rng2)
  else if shape = 8 then
    (mkStstdaddrqCase "fuzz/type/second-not-slice" #[.null, .builder Builder.empty], rng1)
  else if shape = 9 then
    (mkStstdaddrqCase "fuzz/type/both-wrong" #[intV 2, intV 1], rng1)
  else if shape = 10 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqProgramCase s!"fuzz/quiet-cellov/program/{label}" #[.slice cs] quietOverflowProgram, rng2)
  else if shape = 11 then
    let ((label, cs), rng2) := pickValidSlice rng1
    let (noise, rng3) := pickNoise rng2
    (mkStstdaddrqProgramCase s!"fuzz/quiet-cellov/program-deep/{label}" #[noise, .slice cs] quietOverflowProgram, rng3)
  else if shape = 12 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqProgramCase s!"fuzz/ok/append-prefix-program/{label}" #[.slice cs] appendPrefixThenStoreProgram, rng2)
  else if shape = 13 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqCase s!"fuzz/gas/exact/{label}" #[.slice cs, .builder Builder.empty]
      #[.pushInt (.num ststdaddrqSetGasExact), .tonEnvOp .setGasLimit, ststdaddrqInstr], rng2)
  else
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkStstdaddrqCase s!"fuzz/gas/exact-minus-one/{label}" #[.slice cs, .builder Builder.empty]
      #[.pushInt (.num ststdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ststdaddrqInstr], rng2)

def suite : InstrSuite where
  id := ststdaddrqId
  unit := #[
    { name := "unit/direct/success-status-and-order"
      run := do
        let expected0 := appendSliceRemainingToBuilder Builder.empty validStdSlice0
        expectOkStack "ok/empty-builder-valid-slice"
          (runStstdaddrqDirect #[.slice validStdSlice0, .builder Builder.empty])
          #[.builder expected0, intV 0]

        let prefBuilder := Builder.empty.storeBits (natToBits 5 3)
        let expectedPref := appendSliceRemainingToBuilder prefBuilder validStdSlice1
        expectOkStack "ok/append-nonempty-builder"
          (runStstdaddrqDirect #[.slice validStdSlice1, .builder prefBuilder])
          #[.builder expectedPref, intV 0]

        let expectedDeep := appendSliceRemainingToBuilder Builder.empty validStdSliceWc255
        expectOkStack "ok/deep-stack-preserve-below"
          (runStstdaddrqDirect #[.null, .slice validStdSliceWc255, .builder Builder.empty])
          #[.null, .builder expectedDeep, intV 0] }
    ,
    { name := "unit/direct/underflow-and-type-guards"
      run := do
        expectErr "underflow/empty" (runStstdaddrqDirect #[]) .stkUnd
        expectErr "underflow/one-builder" (runStstdaddrqDirect #[.builder Builder.empty]) .stkUnd
        expectErr "underflow/one-slice" (runStstdaddrqDirect #[.slice validStdSlice0]) .stkUnd

        expectErr "type/top-not-builder"
          (runStstdaddrqDirect #[.slice validStdSlice0, .null]) .typeChk
        expectErr "type/second-not-slice"
          (runStstdaddrqDirect #[.null, .builder Builder.empty]) .typeChk
        expectErr "type/both-wrong"
          (runStstdaddrqDirect #[intV 2, intV 1]) .typeChk }
    ,
    { name := "unit/direct/quiet-invalid-shape-and-overflow-status"
      run := do
        for entry in invalidSlicePool do
          let label := entry.1
          let cs := entry.2
          expectOkStack s!"quiet-invalid/{label}"
            (runStstdaddrqDirect #[.slice cs, .builder Builder.empty])
            #[.slice cs, .builder Builder.empty, intV (-1)]

        expectOkStack "quiet-cellov/full-builder"
          (runStstdaddrqDirect #[.slice validStdSlice0, .builder fullBuilder1023])
          #[.slice validStdSlice0, .builder fullBuilder1023, intV (-1)]

        expectOkStack "quiet-cellov/deep-stack-preserve-below"
          (runStstdaddrqDirect #[intV 11, .slice validStdSlice1, .builder fullBuilder1023])
          #[intV 11, .slice validStdSlice1, .builder fullBuilder1023, intV (-1)] }
    ,
    { name := "unit/direct/nonquiet-baseline-cellov"
      run := do
        expectErr "nonquiet/invalid-shape"
          (runStstdaddrDirect #[.slice invalidTagSlice, .builder Builder.empty]) .cellOv
        expectErr "nonquiet/overflow"
          (runStstdaddrDirect #[.slice validStdSlice0, .builder fullBuilder1023]) .cellOv }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[ststdaddrqInstr, ststdaddrInstr, (.tonEnvOp (.stOptStdAddr true)), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ststdaddrq" s0 ststdaddrqInstr 16
        let s2 ← expectDecodeStep "decode/ststdaddr" s1 ststdaddrInstr 16
        let s3 ← expectDecodeStep "decode/stoptstdaddrq" s2 (.tonEnvOp (.stOptStdAddr true)) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runStstdaddrqDispatchFallback #[.null])
          #[.null, intV 453] }
  ]
  oracle := #[
    mkStstdaddrqCase "ok/valid-wc0-addr0" #[.slice validStdSlice0, .builder Builder.empty],
    mkStstdaddrqCase "ok/valid-wc0-addr1" #[.slice validStdSlice1, .builder Builder.empty],
    mkStstdaddrqCase "ok/valid-wc255-addr42" #[.slice validStdSliceWc255, .builder Builder.empty],
    mkStstdaddrqCase "ok/valid-wc17-addr65535" #[.slice validStdSliceWc17, .builder Builder.empty],
    mkStstdaddrqCase "ok/deep-stack-null" #[.null, .slice validStdSlice0, .builder Builder.empty],
    mkStstdaddrqCase "ok/deep-stack-int" #[intV 9, .slice validStdSlice1, .builder Builder.empty],
    mkStstdaddrqProgramCase "ok/program-append-existing-prefix" #[.slice validStdSlice0] appendPrefixThenStoreProgram,
    mkStstdaddrqProgramCase "ok/program-append-existing-prefix-alt" #[.slice validStdSliceWc255] appendPrefixThenStoreProgram,

    mkStstdaddrqCase "quiet-invalid/tag-not-std" #[.slice invalidTagSlice, .builder Builder.empty],
    mkStstdaddrqCase "quiet-invalid/anycast-enabled" #[.slice invalidAnycastSlice, .builder Builder.empty],
    mkStstdaddrqCase "quiet-invalid/short-bits" #[.slice invalidShortSlice, .builder Builder.empty],
    mkStstdaddrqCase "quiet-invalid/long-bits" #[.slice invalidLongSlice, .builder Builder.empty],
    mkStstdaddrqCase "quiet-invalid/nonzero-refs" #[.slice invalidRefsSlice, .builder Builder.empty],
    mkStstdaddrqCase "quiet-invalid/deep-stack" #[intV 77, .slice invalidAnycastSlice, .builder Builder.empty],

    mkStstdaddrqCase "underflow/empty" #[],
    mkStstdaddrqCase "underflow/one-builder" #[.builder Builder.empty],
    mkStstdaddrqCase "underflow/one-slice" #[.slice validStdSlice0],
    mkStstdaddrqCase "type/top-not-builder" #[.slice validStdSlice0, .null],
    mkStstdaddrqCase "type/second-not-slice" #[.null, .builder Builder.empty],
    mkStstdaddrqCase "type/both-wrong" #[intV 2, intV 1],

    mkStstdaddrqCase "gas/exact-cost-succeeds" #[.slice validStdSlice0, .builder Builder.empty]
      #[.pushInt (.num ststdaddrqSetGasExact), .tonEnvOp .setGasLimit, ststdaddrqInstr],
    mkStstdaddrqCase "gas/exact-minus-one-out-of-gas" #[.slice validStdSlice0, .builder Builder.empty]
      #[.pushInt (.num ststdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ststdaddrqInstr],

    mkStstdaddrqProgramCase "quiet-cellov/full-builder-program" #[.slice validStdSlice0] quietOverflowProgram,
    mkStstdaddrqProgramCase "quiet-cellov/full-builder-program-alt" #[.slice validStdSliceWc255] quietOverflowProgram,
    mkStstdaddrqProgramCase "quiet-cellov/full-builder-program-deep" #[.null, .slice validStdSlice1] quietOverflowProgram
  ]
  fuzz := #[
    { seed := 2026021016
      count := 320
      gen := genStstdaddrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.STSTDADDRQ
