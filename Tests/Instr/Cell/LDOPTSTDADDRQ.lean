import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDOPTSTDADDRQ

/-
LDOPTSTDADDRQ branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.tonEnvOp (.ldOptStdAddr true)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDOPTSTDADDRQ` encode: `0xfa51`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa51` decode to `.tonEnvOp (.ldOptStdAddr true)`)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_opt_std_message_addr`, `util::load_std_msg_addr_q`, `skip_std_message_addr`)
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp`
    (no LDOPTSTDADDR/LDOPTSTDADDRQ implementation; TON op is in `tonops.cpp`).

Branch map used for this suite (quiet LDOPTSTDADDRQ path):
- handler dispatch (`.ldOptStdAddr _` vs fallthrough to `next`);
- hard pop guard (`popSlice`: underflow/type before quiet behavior);
- short-tag guard (`haveBits 2`): quiet fail returns original slice + status `0`;
- tag split:
  - `00` (`addr_none`) success pushes `null`, remainder, status `-1`;
  - otherwise parse as std address via `skipStdMessageAddr`;
- std parse guard terminals (quiet):
  - invalid tag (`01` / `11`) → original slice + `0`;
  - missing anycast bit / anycast=`1` / short payload → original slice + `0`;
  - valid std (`10 0 wc:int8 addr:bits256`) → parsed prefix slice + remainder + `-1`.

Key risk areas:
- quiet status polarity (`-1` success, `0` failure) must match C++ `push_bool(true/false)`;
- quiet failures must preserve the original input slice exactly;
- `addr_none$00` must consume exactly 2 bits and not inspect refs;
- decode/asm must keep `LDOPTSTDADDRQ` (`0xfa51`) distinct from `LDOPTSTDADDR` (`0xfa50`).
-/

private def ldoptstdaddrqId : InstrId := { name := "LDOPTSTDADDRQ" }

private def ldoptstdaddrqInstr : Instr := .tonEnvOp (.ldOptStdAddr true)

private def ldoptstdaddrInstr : Instr := .tonEnvOp (.ldOptStdAddr false)

private def ldstdaddrqInstr : Instr := .tonEnvOp (.ldStdAddr true)

private def mkLdoptstdaddrqCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldoptstdaddrqInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldoptstdaddrqId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdoptstdaddrqDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ldoptstdaddrqInstr stack

private def runLdoptstdaddrqDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 959)) stack

private def ldoptstdaddrqSetGasExact : Int :=
  computeExactGasBudget ldoptstdaddrqInstr

private def ldoptstdaddrqSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldoptstdaddrqInstr

private def mkCellWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Cell :=
  { (Builder.empty.storeBits bits) with refs := refs }.finalize

private def mkSliceWithBitsAndRefs (bits : BitString) (refs : Array Cell := #[]) : Slice :=
  Slice.ofCell (mkCellWithBitsAndRefs bits refs)

private def mkStdAddrBits (wc : Nat) (addr : Nat) : BitString :=
  natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits wc 8 ++ natToBits addr 256

private def mkOptNoneSlice (tail : BitString := #[]) (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b00 2 ++ tail) refs

private def mkOptStdSlice
    (wc : Nat)
    (addr : Nat)
    (tail : BitString := #[])
    (refs : Array Cell := #[]) : Slice :=
  mkSliceWithBitsAndRefs (mkStdAddrBits wc addr ++ tail) refs

private def mkTag01Slice (tail : BitString := #[]) : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b01 2 ++ tail)

private def mkTag11Slice (tail : BitString := #[]) : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b11 2 ++ tail)

private def mkAnycast1Slice
    (wc : Nat)
    (addr : Nat)
    (tail : BitString := #[]) : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b10 2 ++ natToBits 1 1 ++ natToBits wc 8 ++ natToBits addr 256 ++ tail)

private def mkShortStdSlice (wc : Nat) (addr : Nat) : Slice :=
  mkSliceWithBitsAndRefs (natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits wc 8 ++ natToBits addr 255)

private def shortTag0Slice : Slice := mkSliceWithBitsAndRefs #[]

private def shortTag1Slice : Slice := mkSliceWithBitsAndRefs #[true]

private def tag10NoAnycastBitSlice : Slice := mkSliceWithBitsAndRefs (natToBits 0b10 2)

private def tailBits5 : BitString := natToBits 0b10101 5

private def tailBits9 : BitString := natToBits 0b101001011 9

private def tailBits13 : BitString := natToBits 6699 13

private def validNoneEmpty : Slice := mkOptNoneSlice

private def validNoneTail : Slice := mkOptNoneSlice tailBits5

private def validNoneTailRefs : Slice := mkOptNoneSlice tailBits9 #[Cell.empty]

private def validStd0 : Slice := mkOptStdSlice 0 0

private def validStd1 : Slice := mkOptStdSlice 1 1

private def validStdWc255 : Slice := mkOptStdSlice 255 65535

private def validStdTail : Slice := mkOptStdSlice 17 4660 tailBits13

private def validStdTailRefs : Slice := mkOptStdSlice 33 12345 tailBits9 #[Cell.empty]

private def validStdBoundaryA : Slice := mkOptStdSlice 128 4095

private def validStdBoundaryB : Slice := mkOptStdSlice 254 257

private def invalidTag01 : Slice := mkTag01Slice

private def invalidTag11 : Slice := mkTag11Slice

private def invalidAnycast1 : Slice := mkAnycast1Slice 0 0

private def invalidShortStd : Slice := mkShortStdSlice 0 0

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

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 0 20
  if width = 0 then
    (#[], rng1)
  else
    let maxVal : Nat := (1 <<< width) - 1
    let (v, rng2) := randNat rng1 0 maxVal
    (natToBits v width, rng2)

private def pickRemainderRefs (rng0 : StdGen) : Array Cell × StdGen :=
  let (mode, rng1) := randNat rng0 0 2
  if mode = 0 then
    (#[], rng1)
  else if mode = 1 then
    (#[Cell.empty], rng1)
  else
    (#[Cell.empty, mkCellWithBitsAndRefs (natToBits 0b101 3)], rng1)

private def pickNoiseValue (rng0 : StdGen) : Value × StdGen :=
  let (pick, rng1) := randNat rng0 0 2
  let v : Value :=
    if pick = 0 then .null
    else if pick = 1 then intV 17
    else .cell Cell.empty
  (v, rng1)

private def pickInvalidSlice (rng0 : StdGen) : Slice × String × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  let (wc, rng2) := pickWcMixed rng1
  let (addr, rng3) := pickAddrMixed rng2
  let (tail, rng4) := pickTailBits rng3
  if shape = 0 then
    let (bits, rng5) := randNat rng4 0 1
    if bits = 0 then
      (shortTag0Slice, "short-tag-0", rng5)
    else
      (shortTag1Slice, "short-tag-1", rng5)
  else if shape = 1 then
    (mkTag01Slice tail, "tag01", rng4)
  else if shape = 2 then
    (mkTag11Slice tail, "tag11", rng4)
  else if shape = 3 then
    (mkAnycast1Slice wc addr tail, "anycast-1", rng4)
  else if shape = 4 then
    (mkShortStdSlice wc addr, "short-266", rng4)
  else
    (tag10NoAnycastBitSlice, "tag10-no-anycast", rng4)

private def genLdoptstdaddrqFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 19
  let (wc, rng2) := pickWcMixed rng1
  let (addr, rng3) := pickAddrMixed rng2
  let (tail, rng4) := pickTailBits rng3
  let (refs, rng5) := pickRemainderRefs rng4
  let noneSlice := mkOptNoneSlice tail refs
  let stdSlice := mkOptStdSlice wc addr tail refs
  if shape = 0 then
    (mkLdoptstdaddrqCase "fuzz/ok/none-empty" #[.slice validNoneEmpty], rng5)
  else if shape = 1 then
    (mkLdoptstdaddrqCase s!"fuzz/ok/none/tail-{tail.size}" #[.slice noneSlice], rng5)
  else if shape = 2 then
    (mkLdoptstdaddrqCase s!"fuzz/ok/std/wc-{wc}/addr-{addr}" #[.slice (mkOptStdSlice wc addr)], rng3)
  else if shape = 3 then
    (mkLdoptstdaddrqCase s!"fuzz/ok/std-tail/wc-{wc}/addr-{addr}/tail-{tail.size}"
      #[.slice (mkOptStdSlice wc addr tail)], rng4)
  else if shape = 4 then
    (mkLdoptstdaddrqCase s!"fuzz/ok/std-tail-refs/wc-{wc}/addr-{addr}/refs-{refs.size}"
      #[.slice stdSlice], rng5)
  else if shape = 5 then
    let (noise, rng6) := pickNoiseValue rng5
    (mkLdoptstdaddrqCase s!"fuzz/ok/deep/wc-{wc}/addr-{addr}" #[noise, .slice stdSlice], rng6)
  else if shape = 6 then
    let (bad, tag, rng6) := pickInvalidSlice rng5
    (mkLdoptstdaddrqCase s!"fuzz/quiet-invalid/{tag}" #[.slice bad], rng6)
  else if shape = 7 then
    (mkLdoptstdaddrqCase "fuzz/quiet-invalid/tag01" #[.slice (mkTag01Slice tail)], rng4)
  else if shape = 8 then
    (mkLdoptstdaddrqCase "fuzz/quiet-invalid/tag11" #[.slice (mkTag11Slice tail)], rng4)
  else if shape = 9 then
    (mkLdoptstdaddrqCase "fuzz/quiet-invalid/tag10-no-anycast" #[.slice tag10NoAnycastBitSlice], rng5)
  else if shape = 10 then
    (mkLdoptstdaddrqCase s!"fuzz/quiet-invalid/anycast/wc-{wc}/addr-{addr}"
      #[.slice (mkAnycast1Slice wc addr tail)], rng4)
  else if shape = 11 then
    (mkLdoptstdaddrqCase s!"fuzz/quiet-invalid/short-266/wc-{wc}/addr-{addr}"
      #[.slice (mkShortStdSlice wc addr)], rng3)
  else if shape = 12 then
    let (noise, rng6) := pickNoiseValue rng5
    let (bad, tag, rng7) := pickInvalidSlice rng6
    (mkLdoptstdaddrqCase s!"fuzz/quiet-invalid/deep/{tag}"
      #[noise, .slice bad], rng7)
  else if shape = 13 then
    (mkLdoptstdaddrqCase "fuzz/underflow/empty" #[], rng5)
  else if shape = 14 then
    (mkLdoptstdaddrqCase "fuzz/type/top-int" #[intV 3], rng5)
  else if shape = 15 then
    (mkLdoptstdaddrqCase "fuzz/type/top-null-deep" #[.slice stdSlice, .null], rng5)
  else if shape = 16 then
    (mkLdoptstdaddrqCase "fuzz/gas/exact" #[.slice stdSlice]
      #[.pushInt (.num ldoptstdaddrqSetGasExact), .tonEnvOp .setGasLimit, ldoptstdaddrqInstr], rng5)
  else if shape = 17 then
    (mkLdoptstdaddrqCase "fuzz/gas/exact-minus-one" #[.slice stdSlice]
      #[.pushInt (.num ldoptstdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldoptstdaddrqInstr], rng5)
  else if shape = 18 then
    (mkLdoptstdaddrqCase s!"fuzz/ok/boundary/wc-{wc}/addr-{addr}" #[.slice (mkOptStdSlice wc addr)], rng3)
  else
    (mkLdoptstdaddrqCase "fuzz/ok/none-with-refs" #[.slice (mkOptNoneSlice tail #[Cell.empty])], rng4)

def suite : InstrSuite where
  id := ldoptstdaddrqId
  unit := #[
    { name := "unit/direct/success-status-and-stack-order"
      run := do
        let noneInput := validNoneTailRefs
        let noneRem := noneInput.advanceBits 2
        expectOkStack "ok/none/tail-and-refs"
          (runLdoptstdaddrqDirect #[.slice noneInput])
          #[.null, .slice noneRem, intV (-1)]

        let stdInput := validStdTail
        let stdRem := stdInput.advanceBits 267
        let stdAddr := Slice.ofCell (Slice.prefixCell stdInput stdRem)
        expectOkStack "ok/std/tail"
          (runLdoptstdaddrqDirect #[.slice stdInput])
          #[.slice stdAddr, .slice stdRem, intV (-1)]

        let stdInputRefs := validStdTailRefs
        let stdRemRefs := stdInputRefs.advanceBits 267
        let stdAddrRefs := Slice.ofCell (Slice.prefixCell stdInputRefs stdRemRefs)
        expectOkStack "ok/std/tail-and-refs"
          (runLdoptstdaddrqDirect #[.slice stdInputRefs])
          #[.slice stdAddrRefs, .slice stdRemRefs, intV (-1)]

        expectOkStack "ok/deep-stack-preserve-below"
          (runLdoptstdaddrqDirect #[intV 7, .slice validStd1])
          #[intV 7, .slice (Slice.ofCell (mkCellWithBitsAndRefs (mkStdAddrBits 1 1))), .slice (validStd1.advanceBits 267), intV (-1)] }
    ,
    { name := "unit/direct/underflow-and-type-guards"
      run := do
        expectErr "underflow/empty"
          (runLdoptstdaddrqDirect #[]) .stkUnd

        expectErr "type/top-int"
          (runLdoptstdaddrqDirect #[intV 3]) .typeChk
        expectErr "type/top-not-slice-deep"
          (runLdoptstdaddrqDirect #[.slice validStd0, intV 1]) .typeChk
        expectErr "type/top-null-deep"
          (runLdoptstdaddrqDirect #[.slice validNoneEmpty, .null]) .typeChk }
    ,
    { name := "unit/direct/quiet-invalid-shape-and-range-status"
      run := do
        let invalidCases : Array (String × Slice) :=
          #[
            ("short-tag-0", shortTag0Slice),
            ("short-tag-1", shortTag1Slice),
            ("tag01", invalidTag01),
            ("tag11", invalidTag11),
            ("tag10-no-anycast", tag10NoAnycastBitSlice),
            ("anycast-enabled", invalidAnycast1),
            ("short-266", invalidShortStd)
          ]
        for entry in invalidCases do
          let label := entry.1
          let s := entry.2
          expectOkStack s!"quiet-invalid/{label}"
            (runLdoptstdaddrqDirect #[.slice s])
            #[.slice s, intV 0]

        expectOkStack "quiet-invalid/deep-stack-preserve-below"
          (runLdoptstdaddrqDirect #[intV 99, .slice invalidAnycast1])
          #[intV 99, .slice invalidAnycast1, intV 0] }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let program : Array Instr := #[ldoptstdaddrqInstr, ldoptstdaddrInstr, ldstdaddrqInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldoptstdaddrq" s0 ldoptstdaddrqInstr 16
        let s2 ← expectDecodeStep "decode/ldoptstdaddr" s1 ldoptstdaddrInstr 16
        let s3 ← expectDecodeStep "decode/ldstdaddrq" s2 ldstdaddrqInstr 16
        let s4 ← expectDecodeStep "decode/tail-add" s3 .add 8
        if s4.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s4.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-stdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdoptstdaddrqDispatchFallback #[.null])
          #[.null, intV 959] }
  ]
  oracle := #[
    mkLdoptstdaddrqCase "ok/none-empty" #[.slice validNoneEmpty],
    mkLdoptstdaddrqCase "ok/none-tail" #[.slice validNoneTail],
    mkLdoptstdaddrqCase "ok/none-tail-refs" #[.slice validNoneTailRefs],
    mkLdoptstdaddrqCase "ok/std-wc0-addr0" #[.slice validStd0],
    mkLdoptstdaddrqCase "ok/std-wc1-addr1" #[.slice validStd1],
    mkLdoptstdaddrqCase "ok/std-wc255-addr65535" #[.slice validStdWc255],
    mkLdoptstdaddrqCase "ok/std-tail" #[.slice validStdTail],
    mkLdoptstdaddrqCase "ok/std-tail-refs" #[.slice validStdTailRefs],
    mkLdoptstdaddrqCase "ok/std-boundary-wc128-addr4095" #[.slice validStdBoundaryA],
    mkLdoptstdaddrqCase "ok/std-boundary-wc254-addr257" #[.slice validStdBoundaryB],
    mkLdoptstdaddrqCase "ok/deep-stack-preserve-below" #[.null, .slice validStd1],

    mkLdoptstdaddrqCase "quiet-invalid/short-tag-0" #[.slice shortTag0Slice],
    mkLdoptstdaddrqCase "quiet-invalid/short-tag-1" #[.slice shortTag1Slice],
    mkLdoptstdaddrqCase "quiet-invalid/tag01" #[.slice invalidTag01],
    mkLdoptstdaddrqCase "quiet-invalid/tag11" #[.slice invalidTag11],
    mkLdoptstdaddrqCase "quiet-invalid/tag10-no-anycast" #[.slice tag10NoAnycastBitSlice],
    mkLdoptstdaddrqCase "quiet-invalid/anycast-enabled" #[.slice invalidAnycast1],
    mkLdoptstdaddrqCase "quiet-invalid/short-266" #[.slice invalidShortStd],
    mkLdoptstdaddrqCase "quiet-invalid/deep-stack" #[intV 77, .slice invalidAnycast1],

    mkLdoptstdaddrqCase "underflow/empty" #[],
    mkLdoptstdaddrqCase "type/top-int" #[intV 9],
    mkLdoptstdaddrqCase "type/top-not-slice-deep" #[.slice validStd0, .null],

    mkLdoptstdaddrqCase "gas/exact-cost-succeeds" #[.slice validStd1]
      #[.pushInt (.num ldoptstdaddrqSetGasExact), .tonEnvOp .setGasLimit, ldoptstdaddrqInstr],
    mkLdoptstdaddrqCase "gas/exact-minus-one-out-of-gas" #[.slice validStd1]
      #[.pushInt (.num ldoptstdaddrqSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldoptstdaddrqInstr]
  ]
  fuzz := #[
    { seed := 2026021017
      count := 320
      gen := genLdoptstdaddrqFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDOPTSTDADDRQ
