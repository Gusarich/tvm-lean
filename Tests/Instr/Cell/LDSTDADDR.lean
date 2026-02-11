import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDSTDADDR

/-
LDSTDADDR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.tonEnvOp (.ldStdAddr false)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDSTDADDR` encode: `0xfa48`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa48` decode to `.tonEnvOp (.ldStdAddr false)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (no `LDSTDADDR{Q}` handler/opcode in current tree)
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`skip_std_message_addr`, `util::load_std_msg_addr_q`, `exec_load_std_message_addr`,
     opcode registrations `0xfa48/0xfa49`).

Branch map used for this suite (`quiet=false`, i.e. LDSTDADDR):
- Lean LDSTDADDR path: 7 branch sites / 8 terminal outcomes
  (dispatch guard; `popSlice` underflow/type; std-tag guard;
   anycast guard; payload-availability guard; success split/push; non-quiet throw on failure).
- C++ LDSTDADDR path: 6 branch sites / 7 aligned outcomes
  (`pop_cellslice`; `skip_std_message_addr`; `cell_und` on failure; success push of loaded addr + remainder).

Key risk areas:
- output ordering is `... addr remainder` (remainder on top);
- non-quiet mode propagates all parse failures as `cellUnd`;
- only `addr_std$10` with `anycast = 0` is accepted;
- payload must contain at least `8 + 256` bits after the 3-bit header;
- unlike store-side checks, LDSTDADDR does not require zero refs in the source slice.
-/

private def ldstdaddrId : InstrId := { name := "LDSTDADDR" }

private def ldstdaddrInstr : Instr :=
  .tonEnvOp (.ldStdAddr false)

private def ldstdaddrqInstr : Instr :=
  .tonEnvOp (.ldStdAddr true)

private def mkLdstdaddrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldstdaddrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldstdaddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdstdaddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ldstdaddrInstr stack

private def runLdstdaddrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 648)) stack

private def ldstdaddrSetGasExact : Int :=
  computeExactGasBudget ldstdaddrInstr

private def ldstdaddrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldstdaddrInstr

private def stdAddrBitsConsumed : Nat := 267

private def mkStdAddrBits (workchainByte : Nat) (addr256 : Nat) : BitString :=
  natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits (workchainByte % 256) 8 ++ natToBits addr256 256

private def mkStdAddrCell
    (workchainByte : Nat)
    (addr256 : Nat)
    (tailBits : BitString := #[])
    (refs : Array Cell := #[]) : Cell :=
  Cell.mkOrdinary (mkStdAddrBits workchainByte addr256 ++ tailBits) refs

private def mkStdAddrSlice
    (workchainByte : Nat)
    (addr256 : Nat)
    (tailBits : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkStdAddrCell workchainByte addr256 tailBits refs)

private def mkShortStdPayloadSlice (payloadBits : Nat) : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ #[false] ++ natToBits 0 payloadBits)

private def expectedLoadOut (s : Slice) : Array Value :=
  let rem := s.advanceBits stdAddrBitsConsumed
  let addr := Slice.ofCell (Slice.prefixCell s rem)
  #[.slice addr, .slice rem]

private def tailBits33 : BitString := natToBits 0x1ABCDE 33

private def stdSliceZero : Slice := mkStdAddrSlice 0 0

private def stdSliceMaxWc : Slice := mkStdAddrSlice 255 65535

private def stdSliceSample : Slice := mkStdAddrSlice 17 0xABCD

private def stdSliceTail7 : Slice := mkStdAddrSlice 9 77 tailBits7

private def stdSliceTail33 : Slice := mkStdAddrSlice 128 65535 tailBits33

private def stdSliceWithRef : Slice := mkStdAddrSlice 31 999 #[] #[Cell.empty]

private def stdSliceWithRefTail : Slice := mkStdAddrSlice 63 555 tailBits7 #[Cell.empty]

private def shiftedStdSlice : Slice :=
  (Slice.ofCell (Cell.mkOrdinary (natToBits 0b101 3 ++ mkStdAddrBits 23 314159 ++ tailBits7) #[])).advanceBits 3

private def shiftedStdSliceWithRef : Slice :=
  (Slice.ofCell (Cell.mkOrdinary (natToBits 0b11 2 ++ mkStdAddrBits 29 271828 ++ tailBits7) #[Cell.empty])).advanceBits 2

private def invalidTagSlice00 : Slice :=
  mkSliceFromBits (natToBits 0b00 2 ++ natToBits 0 265)

private def invalidTagSlice01 : Slice :=
  mkSliceFromBits (natToBits 0b01 2 ++ natToBits 0 265)

private def invalidTagSlice11 : Slice :=
  mkSliceFromBits (natToBits 0b11 2 ++ natToBits 0 265)

private def invalidAnycastSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ #[true] ++ natToBits 0 264)

private def shortPrefix0Slice : Slice := mkSliceFromBits #[]

private def shortPrefix1Slice : Slice := mkSliceFromBits #[true]

private def shortStdTagOnlySlice : Slice := mkSliceFromBits (natToBits 0b10 2)

private def shortStdHeaderOnlySlice : Slice := mkSliceFromBits (natToBits 0b10 2 ++ #[false])

private def shortStdPayload266Slice : Slice := mkShortStdPayloadSlice 263

private def stdWorkchainPool : Array Nat :=
  #[0, 1, 2, 17, 31, 63, 127, 128, 255]

private def stdAddrPool : Array Nat :=
  #[0, 1, 2, 3, 7, 15, 31, 255, 256, 1024, 65535]

private def invalidTagPool : Array Nat :=
  #[0b00, 0b01, 0b11]

private def shortPrefixBitsPool : Array Nat :=
  #[0, 1, 2]

private def shortPayloadBitsPool : Array Nat :=
  #[0, 1, 7, 8, 63, 127, 255, 263]

private def tailBitsPool : Array (String × BitString) :=
  #[
    ("tail0", #[]),
    ("tail1", natToBits 1 1),
    ("tail2", natToBits 2 2),
    ("tail3", natToBits 5 3),
    ("tail7", tailBits7),
    ("tail8", natToBits 170 8),
    ("tail11", natToBits 1337 11),
    ("tail12", natToBits 2730 12)
  ]

private def pickNatFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickTailBitsFromPool (rng : StdGen) : (String × BitString) × StdGen :=
  let (idx, rng') := randNat rng 0 (tailBitsPool.size - 1)
  (tailBitsPool[idx]!, rng')

private def pickWorkchainMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 5 then
    pickNatFromPool stdWorkchainPool rng1
  else
    randNat rng1 0 255

private def pickAddrMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 5 then
    pickNatFromPool stdAddrPool rng1
  else
    randNat rng1 0 65535

private def pickValidStdSlice (rng0 : StdGen) : (String × Slice) × StdGen :=
  let (wc, rng1) := pickWorkchainMixed rng0
  let (addr, rng2) := pickAddrMixed rng1
  let ((tailLabel, tailBits), rng3) := pickTailBitsFromPool rng2
  ((s!"wc{wc}-a{addr}-{tailLabel}", mkStdAddrSlice wc addr tailBits), rng3)

private def pickValidStdSliceWithRefs (rng0 : StdGen) : (String × Slice) × StdGen :=
  let (wc, rng1) := pickWorkchainMixed rng0
  let (addr, rng2) := pickAddrMixed rng1
  let ((tailLabel, tailBits), rng3) := pickTailBitsFromPool rng2
  ((s!"wc{wc}-a{addr}-{tailLabel}-ref", mkStdAddrSlice wc addr tailBits #[Cell.empty]), rng3)

private def pickInvalidTagSlice (rng0 : StdGen) : (String × Slice) × StdGen :=
  let (tag, rng1) := pickNatFromPool invalidTagPool rng0
  let ((tailLabel, tailBits), rng2) := pickTailBitsFromPool rng1
  let s := mkSliceFromBits (natToBits tag 2 ++ natToBits 0 265 ++ tailBits)
  ((s!"tag{tag}-{tailLabel}", s), rng2)

private def pickShortPrefixSlice (rng0 : StdGen) : (String × Slice) × StdGen :=
  let (prefixBits, rng1) := pickNatFromPool shortPrefixBitsPool rng0
  ((s!"prefix-{prefixBits}", mkSliceFromBits (natToBits 0 prefixBits)), rng1)

private def pickShortPayloadSlice (rng0 : StdGen) : (String × Slice) × StdGen :=
  let (payloadBits, rng1) := pickNatFromPool shortPayloadBitsPool rng0
  ((s!"payload-{payloadBits}", mkShortStdPayloadSlice payloadBits), rng1)

private def pickLdstdaddrNoise (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 5
  if pick = 0 then
    (.null, rng1)
  else if pick = 1 then
    let (n, rng2) := randNat rng1 0 127
    (intV (Int.ofNat n - 64), rng2)
  else if pick = 2 then
    (.cell Cell.empty, rng1)
  else if pick = 3 then
    (.tuple #[], rng1)
  else if pick = 4 then
    (.builder Builder.empty, rng1)
  else
    let ((_, s), rng2) := pickValidStdSlice rng1
    (.slice s, rng2)

private def genLdstdaddrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  if shape = 0 then
    let ((label, s), rng2) := pickValidStdSlice rng1
    (mkLdstdaddrCase s!"fuzz/ok/top/{label}" #[.slice s], rng2)
  else if shape = 1 then
    let ((label, s), rng2) := pickValidStdSlice rng1
    let (noise, rng3) := pickLdstdaddrNoise rng2
    (mkLdstdaddrCase s!"fuzz/ok/deep/{label}" #[noise, .slice s], rng3)
  else if shape = 2 then
    let ((label, s), rng2) := pickValidStdSliceWithRefs rng1
    (mkLdstdaddrCase s!"fuzz/ok/with-refs/{label}" #[.slice s], rng2)
  else if shape = 3 then
    let ((label, s), rng2) := pickValidStdSliceWithRefs rng1
    let (noise, rng3) := pickLdstdaddrNoise rng2
    (mkLdstdaddrCase s!"fuzz/ok/with-refs/deep/{label}" #[noise, .slice s], rng3)
  else if shape = 4 then
    let ((label, s), rng2) := pickInvalidTagSlice rng1
    (mkLdstdaddrCase s!"fuzz/cellund/invalid-tag/{label}" #[.slice s], rng2)
  else if shape = 5 then
    let ((tailLabel, tailBits), rng2) := pickTailBitsFromPool rng1
    let s := mkSliceFromBits (natToBits 0b10 2 ++ #[true] ++ natToBits 0 264 ++ tailBits)
    (mkLdstdaddrCase s!"fuzz/cellund/anycast-set/{tailLabel}" #[.slice s], rng2)
  else if shape = 6 then
    let ((label, s), rng2) := pickShortPrefixSlice rng1
    (mkLdstdaddrCase s!"fuzz/cellund/short-prefix/{label}" #[.slice s], rng2)
  else if shape = 7 then
    let ((label, s), rng2) := pickShortPayloadSlice rng1
    (mkLdstdaddrCase s!"fuzz/cellund/short-payload/{label}" #[.slice s], rng2)
  else if shape = 8 then
    (mkLdstdaddrCase "fuzz/underflow/empty" #[], rng1)
  else if shape = 9 then
    (mkLdstdaddrCase "fuzz/type/top-null" #[.null], rng1)
  else if shape = 10 then
    (mkLdstdaddrCase "fuzz/type/top-int" #[intV 9], rng1)
  else if shape = 11 then
    let ((label, s), rng2) := pickValidStdSlice rng1
    (mkLdstdaddrCase s!"fuzz/type/deep-top-not-slice/{label}" #[.slice s, intV 3], rng2)
  else if shape = 12 then
    let ((label, s), rng2) := pickValidStdSlice rng1
    (mkLdstdaddrCase s!"fuzz/gas/exact/{label}"
      #[.slice s]
      #[.pushInt (.num ldstdaddrSetGasExact), .tonEnvOp .setGasLimit, ldstdaddrInstr], rng2)
  else if shape = 13 then
    let ((label, s), rng2) := pickValidStdSlice rng1
    (mkLdstdaddrCase s!"fuzz/gas/minus-one/{label}"
      #[.slice s]
      #[.pushInt (.num ldstdaddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldstdaddrInstr], rng2)
  else if shape = 14 then
    (mkLdstdaddrCase "fuzz/ok/boundary/wc255-addr65535"
      #[.slice (mkStdAddrSlice 255 65535)], rng1)
  else if shape = 15 then
    (mkLdstdaddrCase "fuzz/cellund/tag-var-11" #[.slice invalidTagSlice11], rng1)
  else if shape = 16 then
    (mkLdstdaddrCase "fuzz/cellund/missing-anycast-bit" #[.slice shortStdTagOnlySlice], rng1)
  else if shape = 17 then
    (mkLdstdaddrCase "fuzz/ok/long-tail33" #[.slice stdSliceTail33], rng1)
  else if shape = 18 then
    (mkLdstdaddrCase "fuzz/ok/ref-and-tail" #[.slice stdSliceWithRefTail], rng1)
  else
    (mkLdstdaddrCase "fuzz/cellund/header-only-100" #[.slice shortStdHeaderOnlySlice], rng1)

def suite : InstrSuite where
  id := ldstdaddrId
  unit := #[
    { name := "unit/direct/success-order-and-remainder"
      run := do
        expectOkStack "ok/std-zero/no-tail"
          (runLdstdaddrDirect #[.slice stdSliceZero])
          (expectedLoadOut stdSliceZero)

        expectOkStack "ok/std-tail7"
          (runLdstdaddrDirect #[.slice stdSliceTail7])
          (expectedLoadOut stdSliceTail7)

        expectOkStack "ok/std-with-ref/remainder-keeps-ref"
          (runLdstdaddrDirect #[.slice stdSliceWithRef])
          (expectedLoadOut stdSliceWithRef)

        expectOkStack "ok/shifted-start-bitpos"
          (runLdstdaddrDirect #[.slice shiftedStdSlice])
          (expectedLoadOut shiftedStdSlice)

        expectOkStack "ok/shifted-start-with-ref"
          (runLdstdaddrDirect #[.slice shiftedStdSliceWithRef])
          (expectedLoadOut shiftedStdSliceWithRef)

        expectOkStack "ok/deep-stack-preserve-below"
          (runLdstdaddrDirect #[.null, .slice stdSliceSample])
          (#[.null] ++ expectedLoadOut stdSliceSample) }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdstdaddrDirect #[]) .stkUnd
        expectErr "type/top-null" (runLdstdaddrDirect #[.null]) .typeChk
        expectErr "type/top-int" (runLdstdaddrDirect #[intV 1]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdstdaddrDirect #[.slice stdSliceZero, .null]) .typeChk
        expectErr "type/deep-top-builder"
          (runLdstdaddrDirect #[.slice stdSliceZero, .builder Builder.empty]) .typeChk }
    ,
    { name := "unit/direct/invalid-shape-and-range-cellund"
      run := do
        expectErr "cellund/tag-none-00"
          (runLdstdaddrDirect #[.slice invalidTagSlice00]) .cellUnd
        expectErr "cellund/tag-extern-01"
          (runLdstdaddrDirect #[.slice invalidTagSlice01]) .cellUnd
        expectErr "cellund/tag-var-11"
          (runLdstdaddrDirect #[.slice invalidTagSlice11]) .cellUnd
        expectErr "cellund/anycast-set"
          (runLdstdaddrDirect #[.slice invalidAnycastSlice]) .cellUnd
        expectErr "cellund/short-prefix-0"
          (runLdstdaddrDirect #[.slice shortPrefix0Slice]) .cellUnd
        expectErr "cellund/short-prefix-1"
          (runLdstdaddrDirect #[.slice shortPrefix1Slice]) .cellUnd
        expectErr "cellund/short-tag-only-10"
          (runLdstdaddrDirect #[.slice shortStdTagOnlySlice]) .cellUnd
        expectErr "cellund/short-header-only-100"
          (runLdstdaddrDirect #[.slice shortStdHeaderOnlySlice]) .cellUnd
        expectErr "cellund/short-payload-266"
          (runLdstdaddrDirect #[.slice shortStdPayload266Slice]) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let canonicalOnly ←
          match assembleCp0 [ldstdaddrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble canonical failed: {e}")
        if canonicalOnly.bits = natToBits 0xfa48 16 then
          pure ()
        else
          throw (IO.userError s!"ldstdaddr canonical encode mismatch: got bits {canonicalOnly.bits}")

        let quietOnly ←
          match assembleCp0 [ldstdaddrqInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble quiet failed: {e}")
        if quietOnly.bits = natToBits 0xfa49 16 then
          pure ()
        else
          throw (IO.userError s!"ldstdaddrq encode mismatch: got bits {quietOnly.bits}")

        let program : Array Instr :=
          #[ldstdaddrInstr, ldstdaddrqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble decode-seq failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldstdaddr-fa48" s0 ldstdaddrInstr 16
        let s2 ← expectDecodeStep "decode/ldstdaddrq-fa49" s1 ldstdaddrqInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ldstdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdstdaddrDispatchFallback #[.null])
          #[.null, intV 648] }
  ]
  oracle := #[
    mkLdstdaddrCase "ok/std-zero"
      #[.slice stdSliceZero],
    mkLdstdaddrCase "ok/std-max-workchain"
      #[.slice stdSliceMaxWc],
    mkLdstdaddrCase "ok/std-sample"
      #[.slice stdSliceSample],
    mkLdstdaddrCase "ok/std-tail7"
      #[.slice stdSliceTail7],
    mkLdstdaddrCase "ok/std-tail33"
      #[.slice stdSliceTail33],
    mkLdstdaddrCase "ok/std-with-ref"
      #[.slice stdSliceWithRef],
    mkLdstdaddrCase "ok/std-with-ref-tail"
      #[.slice stdSliceWithRefTail],
    mkLdstdaddrCase "ok/deep-preserve-null"
      #[.null, .slice stdSliceZero],
    mkLdstdaddrCase "ok/deep-preserve-int"
      #[intV (-5), .slice stdSliceSample],
    mkLdstdaddrCase "ok/deep-preserve-cell"
      #[.cell Cell.empty, .slice stdSliceTail7],

    mkLdstdaddrCase "cellund/tag-none-00"
      #[.slice invalidTagSlice00],
    mkLdstdaddrCase "cellund/tag-extern-01"
      #[.slice invalidTagSlice01],
    mkLdstdaddrCase "cellund/tag-var-11"
      #[.slice invalidTagSlice11],
    mkLdstdaddrCase "cellund/anycast-set"
      #[.slice invalidAnycastSlice],
    mkLdstdaddrCase "cellund/short-prefix-0"
      #[.slice shortPrefix0Slice],
    mkLdstdaddrCase "cellund/short-prefix-1"
      #[.slice shortPrefix1Slice],
    mkLdstdaddrCase "cellund/short-tag-only-10"
      #[.slice shortStdTagOnlySlice],
    mkLdstdaddrCase "cellund/short-header-only-100"
      #[.slice shortStdHeaderOnlySlice],
    mkLdstdaddrCase "cellund/short-payload-266"
      #[.slice shortStdPayload266Slice],

    mkLdstdaddrCase "underflow/empty" #[],
    mkLdstdaddrCase "type/top-null" #[.null],
    mkLdstdaddrCase "type/top-int" #[intV 3],
    mkLdstdaddrCase "type/deep-top-builder"
      #[.slice stdSliceZero, .builder Builder.empty],

    mkLdstdaddrCase "gas/exact-cost-succeeds"
      #[.slice stdSliceSample]
      #[.pushInt (.num ldstdaddrSetGasExact), .tonEnvOp .setGasLimit, ldstdaddrInstr],
    mkLdstdaddrCase "gas/exact-minus-one-out-of-gas"
      #[.slice stdSliceSample]
      #[.pushInt (.num ldstdaddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldstdaddrInstr]
  ]
  fuzz := #[
    { seed := 2026021048
      count := 320
      gen := genLdstdaddrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDSTDADDR
