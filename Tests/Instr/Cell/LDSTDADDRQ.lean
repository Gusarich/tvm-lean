import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSTDADDRQ

/-
LDSTDADDRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean`
    (`.tonEnvOp (.ldStdAddr quiet)`, `skipStdMessageAddr`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean`
    (`LDSTDADDR`/`LDSTDADDRQ` encode as `0xfa48`/`0xfa49`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean`
    (`0xfa48`/`0xfa49` decode to `.tonEnvOp (.ldStdAddr false/true)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_std_message_addr`, `util::load_std_msg_addr_q`, `skip_std_message_addr`).

Branch map used for this suite (`quiet = true`):
- handler match (`.tonEnvOp (.ldStdAddr _)`) vs dispatch fallback to `next`;
- hard pre-guard on stack top (`popSlice`: underflow/type are not softened by quiet mode);
- std-address parser guard sequence:
  `tag=10`, `anycast=0`, enough payload bits `8+256`;
- quiet success pushes `[addr_slice, remainder_slice, -1]` (C++ `push_bool(true)`);
- quiet failure restores original slice and pushes status `0` (C++ `push_bool(false)`).

Key risk areas:
- quiet mode only softens decode failures, not stack underflow/type failures;
- invalid shape variants (bad tag, anycast=1, short payload, short prefix) must all map to quiet status `0`;
- consumed prefix is exactly 267 bits; tail bits/refs must remain in the remainder slice;
- opcode mapping must stay aligned with `0xfa49` for `LDSTDADDRQ`.
-/

private def ldstdaddrqId : InstrId := { name := "LDSTDADDRQ" }

private def ldstdaddrqInstr : Instr :=
  .tonEnvOp (.ldStdAddr true)

private def ldstdaddrInstr : Instr :=
  .tonEnvOp (.ldStdAddr false)

private def mkLdstdaddrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldstdaddrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldstdaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdstdaddrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ldstdaddrqInstr stack

private def runLdstdaddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ldstdaddrInstr stack

private def runLdstdaddrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 949)) stack

private def ldstdaddrqSetGasExact : Int :=
  computeExactGasBudget ldstdaddrqInstr

private def ldstdaddrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldstdaddrqInstr

private def mkStdAddrBits (wc : Nat) (addr : Nat) : BitString :=
  natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits (wc % 256) 8 ++ natToBits addr 256

private def mkStdAddrSlice (wc : Nat) (addr : Nat) (tailBits : BitString := #[]) : Slice :=
  mkSliceFromBits (mkStdAddrBits wc addr ++ tailBits)

private def mkStdAddrSliceWithRefs
    (wc : Nat)
    (addr : Nat)
    (refs : Array Cell)
    (tailBits : BitString := #[]) : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkStdAddrBits wc addr ++ tailBits) refs)

private def stdAddrBitsLen : Nat :=
  (mkStdAddrBits 0 0).size

private def tailBits5 : BitString := natToBits 0b10101 5

private def tailBits9 : BitString := natToBits 341 9

private def tailBits13 : BitString := natToBits 4242 13

private def validStdSlice0 : Slice :=
  mkStdAddrSlice 0 0

private def validStdSliceWc255 : Slice :=
  mkStdAddrSlice 255 1

private def validStdSliceWc17 : Slice :=
  mkStdAddrSlice 17 65535

private def validStdSliceTail9 : Slice :=
  mkStdAddrSlice 42 4660 tailBits9

private def validStdSliceTail13 : Slice :=
  mkStdAddrSlice 0 9 tailBits13

private def validStdSliceRefs1 : Slice :=
  mkStdAddrSliceWithRefs 1 7 #[Cell.empty]

private def validStdSliceTail5Refs1 : Slice :=
  mkStdAddrSliceWithRefs 2 8 #[Cell.empty] tailBits5

private def invalidEmptySlice : Slice :=
  mkSliceFromBits #[]

private def invalidOneBitSlice : Slice :=
  mkSliceFromBits #[true]

private def invalidTag00Slice : Slice :=
  mkSliceFromBits (natToBits 0b00 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def invalidTag01Slice : Slice :=
  mkSliceFromBits (natToBits 0b01 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def invalidTag11Slice : Slice :=
  mkSliceFromBits (natToBits 0b11 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def invalidMissingAnycastSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2)

private def invalidAnycastOneSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 1 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def invalidShortSlice266 : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 255)

private def validSlicePool : Array (String × Slice) :=
  #[
    ("wc0-addr0", validStdSlice0),
    ("wc255-addr1", validStdSliceWc255),
    ("wc17-addr65535", validStdSliceWc17),
    ("wc42-addr4660-tail9", validStdSliceTail9),
    ("wc0-addr9-tail13", validStdSliceTail13),
    ("wc1-addr7-refs1", validStdSliceRefs1),
    ("wc2-addr8-tail5-refs1", validStdSliceTail5Refs1)
  ]

private def invalidSlicePool : Array (String × Slice) :=
  #[
    ("empty", invalidEmptySlice),
    ("one-bit", invalidOneBitSlice),
    ("tag-00", invalidTag00Slice),
    ("tag-01", invalidTag01Slice),
    ("tag-11", invalidTag11Slice),
    ("missing-anycast-bit", invalidMissingAnycastSlice),
    ("anycast-1", invalidAnycastOneSlice),
    ("short-266", invalidShortSlice266)
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
  pickSliceFromPool invalidSlicePool ("tag-00", invalidTag00Slice) rng

private def pickNoise (rng : StdGen) : Value × StdGen :=
  let (pick, rng') := randNat rng 0 2
  let noise : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 73
    else .cell Cell.empty
  (noise, rng')

private def genLdstdaddrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 15
  if shape = 0 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/ok/direct/{label}" #[.slice cs], rng2)
  else if shape = 1 then
    let ((label, cs), rng2) := pickValidSlice rng1
    let (noise, rng3) := pickNoise rng2
    (mkLdstdaddrqCase s!"fuzz/ok/deep/{label}" #[noise, .slice cs], rng3)
  else if shape = 2 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/ok/deep-null/{label}" #[.null, .slice cs], rng2)
  else if shape = 3 then
    let ((label, cs), rng2) := pickInvalidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/quiet-invalid/{label}" #[.slice cs], rng2)
  else if shape = 4 then
    let ((label, cs), rng2) := pickInvalidSlice rng1
    let (noise, rng3) := pickNoise rng2
    (mkLdstdaddrqCase s!"fuzz/quiet-invalid/deep/{label}" #[noise, .slice cs], rng3)
  else if shape = 5 then
    (mkLdstdaddrqCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 6 then
    (mkLdstdaddrqCase "fuzz/type/top-not-slice/null" #[.null], rng1)
  else if shape = 7 then
    (mkLdstdaddrqCase "fuzz/type/top-not-slice/int" #[intV 1], rng1)
  else if shape = 8 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/type/deep-top-not-slice/{label}" #[.slice cs, .cell Cell.empty], rng2)
  else if shape = 9 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/gas/exact/{label}" #[.slice cs]
      #[.pushInt (.num ldstdaddrqSetGasExact), .tonEnvOp .setGasLimit, ldstdaddrqInstr], rng2)
  else if shape = 10 then
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/gas/exact-minus-one/{label}" #[.slice cs]
      #[.pushInt (.num ldstdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldstdaddrqInstr], rng2)
  else if shape = 11 then
    (mkLdstdaddrqCase "fuzz/quiet-invalid/missing-anycast" #[.slice invalidMissingAnycastSlice], rng1)
  else if shape = 12 then
    (mkLdstdaddrqCase "fuzz/quiet-invalid/short-266" #[.slice invalidShortSlice266], rng1)
  else if shape = 13 then
    (mkLdstdaddrqCase "fuzz/quiet-invalid/anycast-1" #[.slice invalidAnycastOneSlice], rng1)
  else if shape = 14 then
    (mkLdstdaddrqCase "fuzz/quiet-invalid/tag-11" #[.slice invalidTag11Slice], rng1)
  else
    let ((label, cs), rng2) := pickValidSlice rng1
    (mkLdstdaddrqCase s!"fuzz/ok/direct-alt/{label}" #[.slice cs], rng2)

def suite : InstrSuite where
  id := ldstdaddrqId
  unit := #[
    { name := "unit/direct/success-status-and-remainder"
      run := do
        let rem0 := validStdSlice0.advanceBits stdAddrBitsLen
        expectOkStack "ok/exact-267-bits"
          (runLdstdaddrqDirect #[.slice validStdSlice0])
          #[.slice (mkStdAddrSlice 0 0), .slice rem0, intV (-1)]

        let remTail := validStdSliceTail9.advanceBits stdAddrBitsLen
        expectOkStack "ok/with-tail-bits-preserved"
          (runLdstdaddrqDirect #[.slice validStdSliceTail9])
          #[.slice (mkStdAddrSlice 42 4660), .slice remTail, intV (-1)]

        let remRefs := validStdSliceTail5Refs1.advanceBits stdAddrBitsLen
        expectOkStack "ok/with-refs-and-tail-remainder-preserved"
          (runLdstdaddrqDirect #[.slice validStdSliceTail5Refs1])
          #[.slice (mkStdAddrSlice 2 8), .slice remRefs, intV (-1)]

        let remDeep := validStdSliceWc255.advanceBits stdAddrBitsLen
        expectOkStack "ok/deep-stack-preserve-below"
          (runLdstdaddrqDirect #[.cell Cell.empty, .slice validStdSliceWc255])
          #[.cell Cell.empty, .slice (mkStdAddrSlice 255 1), .slice remDeep, intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-guarantees"
      run := do
        expectErr "underflow/empty" (runLdstdaddrqDirect #[]) .stkUnd
        expectErr "type/top-not-slice/null" (runLdstdaddrqDirect #[.null]) .typeChk
        expectErr "type/top-not-slice/int" (runLdstdaddrqDirect #[intV 3]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdstdaddrqDirect #[.slice validStdSlice0, .cell Cell.empty]) .typeChk }
    ,
    { name := "unit/direct/quiet-invalid-shape-status0"
      run := do
        for entry in invalidSlicePool do
          let label := entry.1
          let cs := entry.2
          expectOkStack s!"quiet-invalid/{label}"
            (runLdstdaddrqDirect #[.slice cs])
            #[.slice cs, intV 0]

        expectOkStack "quiet-invalid/deep-stack-preserve-below"
          (runLdstdaddrqDirect #[intV 11, .slice invalidAnycastOneSlice])
          #[intV 11, .slice invalidAnycastOneSlice, intV 0] }
    ,
    { name := "unit/direct/nonquiet-baseline-cellund"
      run := do
        for entry in invalidSlicePool do
          let label := entry.1
          let cs := entry.2
          expectErr s!"nonquiet-invalid/{label}"
            (runLdstdaddrDirect #[.slice cs]) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let quietCode ←
          match assembleCp0 [ldstdaddrqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble quiet failed: {e}")
        if quietCode.bits = natToBits 0xfa49 16 then
          pure ()
        else
          throw (IO.userError s!"ldstdaddrq encode mismatch: got bits {quietCode.bits}")

        let nonQuietCode ←
          match assembleCp0 [ldstdaddrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble non-quiet failed: {e}")
        if nonQuietCode.bits = natToBits 0xfa48 16 then
          pure ()
        else
          throw (IO.userError s!"ldstdaddr encode mismatch: got bits {nonQuietCode.bits}")

        let program : Array Instr :=
          #[ldstdaddrqInstr, ldstdaddrInstr, (.tonEnvOp (.ldOptStdAddr true)), .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldstdaddrq" s0 ldstdaddrqInstr 16
        let s2 ← expectDecodeStep "decode/ldstdaddr" s1 ldstdaddrInstr 16
        let s3 ← expectDecodeStep "decode/ldoptstdaddrq" s2 (.tonEnvOp (.ldOptStdAddr true)) 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdstdaddrqDispatchFallback #[.null])
          #[.null, intV 949] }
  ]
  oracle := #[
    mkLdstdaddrqCase "ok/wc0-addr0" #[.slice validStdSlice0],
    mkLdstdaddrqCase "ok/wc255-addr1" #[.slice validStdSliceWc255],
    mkLdstdaddrqCase "ok/wc17-addr65535" #[.slice validStdSliceWc17],
    mkLdstdaddrqCase "ok/wc42-addr4660-tail9" #[.slice validStdSliceTail9],
    mkLdstdaddrqCase "ok/wc0-addr9-tail13" #[.slice validStdSliceTail13],
    mkLdstdaddrqCase "ok/wc1-addr7-refs1" #[.slice validStdSliceRefs1],
    mkLdstdaddrqCase "ok/wc2-addr8-tail5-refs1" #[.slice validStdSliceTail5Refs1],
    mkLdstdaddrqCase "ok/deep-stack-null" #[.null, .slice validStdSlice0],
    mkLdstdaddrqCase "ok/deep-stack-int" #[intV 5, .slice validStdSliceWc255],
    mkLdstdaddrqCase "ok/deep-stack-cell" #[.cell Cell.empty, .slice validStdSliceTail9],

    mkLdstdaddrqCase "quiet-invalid/empty" #[.slice invalidEmptySlice],
    mkLdstdaddrqCase "quiet-invalid/one-bit" #[.slice invalidOneBitSlice],
    mkLdstdaddrqCase "quiet-invalid/tag-00" #[.slice invalidTag00Slice],
    mkLdstdaddrqCase "quiet-invalid/tag-01" #[.slice invalidTag01Slice],
    mkLdstdaddrqCase "quiet-invalid/tag-11" #[.slice invalidTag11Slice],
    mkLdstdaddrqCase "quiet-invalid/missing-anycast-bit" #[.slice invalidMissingAnycastSlice],
    mkLdstdaddrqCase "quiet-invalid/anycast-1" #[.slice invalidAnycastOneSlice],
    mkLdstdaddrqCase "quiet-invalid/short-266" #[.slice invalidShortSlice266],
    mkLdstdaddrqCase "quiet-invalid/deep-stack" #[.null, .slice invalidAnycastOneSlice],

    mkLdstdaddrqCase "underflow/empty" #[],
    mkLdstdaddrqCase "type/top-not-slice-null" #[.null],
    mkLdstdaddrqCase "type/top-not-slice-int" #[intV 3],
    mkLdstdaddrqCase "type/deep-top-not-slice" #[.slice validStdSlice0, .cell Cell.empty],

    mkLdstdaddrqCase "gas/exact-cost-succeeds" #[.slice validStdSlice0]
      #[.pushInt (.num ldstdaddrqSetGasExact), .tonEnvOp .setGasLimit, ldstdaddrqInstr],
    mkLdstdaddrqCase "gas/exact-minus-one-out-of-gas" #[.slice validStdSlice0]
      #[.pushInt (.num ldstdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldstdaddrqInstr]
  ]
  fuzz := #[
    { seed := 2026021018
      count := 320
      gen := genLdstdaddrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSTDADDRQ
