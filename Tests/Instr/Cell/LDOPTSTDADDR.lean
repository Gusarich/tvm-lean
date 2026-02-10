import Tests.Harness.Registry
import Tests.Harness.Gen.Arith
import Tests.Harness.Gen.Cell
import TvmLean.Spec.Index

open TvmLean
open Tests
open Tests.Harness.Gen.Arith
open Tests.Harness.Gen.Cell

namespace Tests.Instr.Cell.LDOPTSTDADDR

/-
LDOPTSTDADDR branch-mapping notes (Lean + C++ reference):
- Lean analyzed files:
  - `TvmLean/Semantics/Exec/TonEnv/StdAddr.lean` (`.tonEnvOp (.ldOptStdAddr false)`)
  - `TvmLean/Model/Instr/Asm/Cp0.lean` (`LDOPTSTDADDR`: `0xfa50`, `LDOPTSTDADDRQ`: `0xfa51`)
  - `TvmLean/Model/Instr/Codepage/Cp0.lean` (`0xfa50/0xfa51` decode)
- C++ analyzed files:
  - `/Users/daniil/Coding/ton/crypto/vm/cellops.cpp` (no `LDOPTSTDADDR{Q}` handler/opcode)
  - `/Users/daniil/Coding/ton/crypto/vm/tonops.cpp`
    (`exec_load_opt_std_message_addr`, `util::load_std_msg_addr_q`,
     `skip_std_message_addr`, opcode registration `0xfa50/0xfa51`).

Branch map used for this suite (`quiet = false`, i.e. LDOPTSTDADDR):
- Lean LDOPTSTDADDR path: 7 branch sites / 8 terminal outcomes
  (pop slice underflow/type; 2-bit tag-availability; `00` vs non-`00`;
   std-tag guard (`10` only); anycast bit guard (`0` only); remaining 264-bit payload guard;
   success pushes `(null|addrSlice)` plus advanced remainder).
- C++ LDOPTSTDADDR path: aligned behavior in `exec_load_opt_std_message_addr`
  (`pop_cellslice`; `have(2)` tag gate; `tag==00` fast-path;
   fallback through `load_std_msg_addr_q`/`skip_std_message_addr`;
   non-quiet failures map to `cell_und`).

Key risk areas:
- result order is always `... (null|addrSlice) remainderSlice` (no status flag in non-quiet form);
- invalid tags `01` / `11` are shape failures (`cellUnd`), not type failures;
- `addr_none$00` consumes exactly 2 bits;
- `addr_std$10` accepts extra trailing bits/refs (they stay in the returned remainder slice);
- opcode identity must stay distinct from `LDOPTSTDADDRQ` (`0xfa51`) and `LDSTDADDR{Q}`.
-/

private def ldOptStdAddrId : InstrId := { name := "LDOPTSTDADDR" }

private def ldOptStdAddrInstr : Instr :=
  .tonEnvOp (.ldOptStdAddr false)

private def ldOptStdAddrQInstr : Instr :=
  .tonEnvOp (.ldOptStdAddr true)

private def mkLdOptStdAddrCase
    (name : String)
    (stack : Array Value)
    (program : Array Instr := #[ldOptStdAddrInstr])
    (gasLimits : OracleGasLimits := {})
    (fuel : Nat := 1_000_000) : OracleCase :=
  { name := name
    instr := ldOptStdAddrId
    program := program
    initStack := stack
    gasLimits := gasLimits
    fuel := fuel }

private def runLdOptStdAddrDirect (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirect execInstrTonEnvStdAddr ldOptStdAddrInstr stack

private def runLdOptStdAddrDispatchFallback (stack : Array Value) : Except Excno (Array Value) :=
  runHandlerDirectWithNext execInstrTonEnvStdAddr .add (VM.push (intV 450)) stack

private def stdAddrTotalBits : Nat := 267

private def mkStdAddrBits (workchain : Nat) (addr : Nat) : BitString :=
  natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits workchain 8 ++ natToBits addr 256

private def mkStdAddrSlice (workchain : Nat) (addr : Nat) : Slice :=
  mkSliceFromBits (mkStdAddrBits workchain addr)

private def mkOptNoneSlice (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (natToBits 0b00 2 ++ tail)

private def mkOptStdSlice (workchain : Nat) (addr : Nat) (tail : BitString := #[]) : Slice :=
  mkSliceFromBits (mkStdAddrBits workchain addr ++ tail)

private def tailBits7 : BitString := natToBits 93 7

private def tailBits11 : BitString := natToBits 1337 11

private def validStdWc0Addr0 : Slice := mkStdAddrSlice 0 0

private def validStdWc1Addr255 : Slice := mkStdAddrSlice 1 255

private def validStdWc42Addr4660 : Slice := mkStdAddrSlice 42 4660

private def validStdWc255Addr65535 : Slice := mkStdAddrSlice 255 65535

private def emptyBitsSlice : Slice := mkSliceFromBits #[]

private def oneBitSlice : Slice := mkSliceFromBits #[true]

private def invalidTag01Slice : Slice :=
  mkSliceFromBits (natToBits 0b01 2 ++ natToBits 0 9)

private def invalidTag11Slice : Slice :=
  mkSliceFromBits (natToBits 0b11 2 ++ natToBits 0 9)

private def shortTag10OnlySlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2)

private def anycastOneSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 1 1 ++ natToBits 0 8 ++ natToBits 0 256)

private def shortStd266Slice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits 0 8 ++ natToBits 0 255)

private def shortAfterAnycastSlice : Slice :=
  mkSliceFromBits (natToBits 0b10 2 ++ natToBits 0 1 ++ natToBits 0 7)

private def stdWithTailAndRefSlice : Slice :=
  Slice.ofCell (Cell.mkOrdinary (mkStdAddrBits 5 42 ++ tailBits7) #[Cell.empty])

private def ldOptStdAddrSetGasExact : Int :=
  computeExactGasBudget ldOptStdAddrInstr

private def ldOptStdAddrSetGasExactMinusOne : Int :=
  computeExactGasBudgetMinusOne ldOptStdAddrInstr

private def wcPool : Array Nat := #[0, 1, 2, 17, 42, 127, 128, 255]

private def addrPool : Array Nat := #[0, 1, 2, 3, 7, 15, 31, 255, 256, 4095, 65535]

private def pickFromPool (pool : Array Nat) (rng : StdGen) : Nat × StdGen :=
  let (idx, rng') := randNat rng 0 (pool.size - 1)
  (pool[idx]!, rng')

private def pickWcMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickFromPool wcPool rng1
  else
    randNat rng1 0 255

private def pickAddrMixed (rng0 : StdGen) : Nat × StdGen :=
  let (mode, rng1) := randNat rng0 0 9
  if mode ≤ 3 then
    pickFromPool addrPool rng1
  else
    randNat rng1 0 65535

private def pickNoise (rng0 : StdGen) : Value × StdGen :=
  let (k, rng1) := randNat rng0 0 2
  if k = 0 then
    (.null, rng1)
  else if k = 1 then
    let (u, rng2) := randNat rng1 0 127
    (intV (Int.ofNat u - 64), rng2)
  else
    (.cell Cell.empty, rng1)

private def pickTailBits (rng0 : StdGen) : BitString × StdGen :=
  let (width, rng1) := randNat rng0 1 12
  let maxVal : Nat := (1 <<< width) - 1
  let (v, rng2) := randNat rng1 0 maxVal
  (natToBits v width, rng2)

private def pickInvalidSlice (rng0 : StdGen) : String × Slice × StdGen :=
  let (shape, rng1) := randNat rng0 0 5
  if shape = 0 then
    ("tag01", invalidTag01Slice, rng1)
  else if shape = 1 then
    ("tag11", invalidTag11Slice, rng1)
  else if shape = 2 then
    ("tag10-no-anycast", shortTag10OnlySlice, rng1)
  else if shape = 3 then
    ("tag10-anycast1", anycastOneSlice, rng1)
  else if shape = 4 then
    ("tag10-short-266", shortStd266Slice, rng1)
  else
    ("tag10-short-after-anycast", shortAfterAnycastSlice, rng1)

private def genLdOptStdAddrFuzzCase (rng0 : StdGen) : OracleCase × StdGen :=
  let (shape, rng1) := randNat rng0 0 16
  let (wc, rng2) := pickWcMixed rng1
  let (addr, rng3) := pickAddrMixed rng2
  let stdInput := mkOptStdSlice wc addr
  if shape = 0 then
    (mkLdOptStdAddrCase "fuzz/ok/none/no-tail" #[.slice (mkOptNoneSlice #[])], rng3)
  else if shape = 1 then
    (mkLdOptStdAddrCase s!"fuzz/ok/std/no-tail/wc-{wc}/addr-{addr}" #[.slice stdInput], rng3)
  else if shape = 2 then
    let (tail, rng4) := pickTailBits rng3
    (mkLdOptStdAddrCase s!"fuzz/ok/std/with-tail/wc-{wc}/addr-{addr}"
      #[.slice (mkOptStdSlice wc addr tail)], rng4)
  else if shape = 3 then
    let (tail, rng4) := pickTailBits rng3
    (mkLdOptStdAddrCase "fuzz/ok/none/with-tail" #[.slice (mkOptNoneSlice tail)], rng4)
  else if shape = 4 then
    let (noise, rng4) := pickNoise rng3
    (mkLdOptStdAddrCase s!"fuzz/ok/deep/std/wc-{wc}/addr-{addr}"
      #[noise, .slice stdInput], rng4)
  else if shape = 5 then
    let (noise, rng4) := pickNoise rng3
    (mkLdOptStdAddrCase "fuzz/ok/deep/none"
      #[noise, .slice (mkOptNoneSlice #[])], rng4)
  else if shape = 6 then
    (mkLdOptStdAddrCase "fuzz/underflow/empty" #[], rng3)
  else if shape = 7 then
    (mkLdOptStdAddrCase "fuzz/type/top-not-slice-null" #[.null], rng3)
  else if shape = 8 then
    (mkLdOptStdAddrCase "fuzz/type/deep-top-not-slice"
      #[.slice stdInput, intV 0], rng3)
  else if shape = 9 then
    let (prefixBits, rng4) := randNat rng3 0 1
    (mkLdOptStdAddrCase s!"fuzz/cellund/tag-short-{prefixBits}"
      #[.slice (mkSliceFromBits (Array.replicate prefixBits false))], rng4)
  else if shape = 10 then
    let (tag, bad, rng4) := pickInvalidSlice rng3
    (mkLdOptStdAddrCase s!"fuzz/cellund/{tag}" #[.slice bad], rng4)
  else if shape = 11 then
    (mkLdOptStdAddrCase "fuzz/cellund/tag10-anycast1" #[.slice anycastOneSlice], rng3)
  else if shape = 12 then
    (mkLdOptStdAddrCase "fuzz/cellund/tag10-short-266" #[.slice shortStd266Slice], rng3)
  else if shape = 13 then
    (mkLdOptStdAddrCase "fuzz/cellund/tag10-short-after-anycast" #[.slice shortAfterAnycastSlice], rng3)
  else if shape = 14 then
    (mkLdOptStdAddrCase s!"fuzz/gas/exact/wc-{wc}/addr-{addr}"
      #[.slice stdInput]
      #[.pushInt (.num ldOptStdAddrSetGasExact), .tonEnvOp .setGasLimit, ldOptStdAddrInstr], rng3)
  else if shape = 15 then
    (mkLdOptStdAddrCase "fuzz/gas/exact-minus-one"
      #[.slice (mkOptNoneSlice #[])]
      #[.pushInt (.num ldOptStdAddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldOptStdAddrInstr], rng3)
  else
    (mkLdOptStdAddrCase "fuzz/ok/std-with-tail-and-ref" #[.slice stdWithTailAndRefSlice], rng3)

def suite : InstrSuite where
  id := ldOptStdAddrId
  unit := #[
    { name := "unit/direct/success-order-and-remainder"
      run := do
        let noneInput := mkOptNoneSlice tailBits7
        let noneRem := noneInput.advanceBits 2
        expectOkStack "ok/none-with-tail"
          (runLdOptStdAddrDirect #[.slice noneInput])
          #[.null, .slice noneRem]

        let stdInput := mkOptStdSlice 42 4660 tailBits11
        let stdRem := stdInput.advanceBits stdAddrTotalBits
        expectOkStack "ok/std-with-tail"
          (runLdOptStdAddrDirect #[.slice stdInput])
          #[.slice validStdWc42Addr4660, .slice stdRem]

        let stdBoundaryInput := mkOptStdSlice 0 0
        let stdBoundaryRem := stdBoundaryInput.advanceBits stdAddrTotalBits
        expectOkStack "ok/std-exact-267-no-tail"
          (runLdOptStdAddrDirect #[.slice stdBoundaryInput])
          #[.slice validStdWc0Addr0, .slice stdBoundaryRem]

        let stdRefRem := stdWithTailAndRefSlice.advanceBits stdAddrTotalBits
        expectOkStack "ok/std-with-tail-and-refs-remaining"
          (runLdOptStdAddrDirect #[.slice stdWithTailAndRefSlice])
          #[.slice (mkStdAddrSlice 5 42), .slice stdRefRem]

        expectOkStack "ok/deep-stack-preserve-below"
          (runLdOptStdAddrDirect #[intV 17, .slice noneInput])
          #[intV 17, .null, .slice noneRem] }
    ,
    { name := "unit/direct/underflow-and-type-order"
      run := do
        expectErr "underflow/empty" (runLdOptStdAddrDirect #[]) .stkUnd
        expectErr "type/top-not-slice-null" (runLdOptStdAddrDirect #[.null]) .typeChk
        expectErr "type/top-not-slice-int" (runLdOptStdAddrDirect #[intV 1]) .typeChk
        expectErr "type/deep-top-not-slice"
          (runLdOptStdAddrDirect #[.slice (mkOptNoneSlice #[]), .null]) .typeChk
        expectErr "type/order-before-shape-check"
          (runLdOptStdAddrDirect #[.slice invalidTag01Slice, intV 0]) .typeChk }
    ,
    { name := "unit/direct/invalid-shape-and-range-cellund"
      run := do
        expectErr "cellund/no-tag-bits-0"
          (runLdOptStdAddrDirect #[.slice emptyBitsSlice]) .cellUnd
        expectErr "cellund/no-tag-bits-1"
          (runLdOptStdAddrDirect #[.slice oneBitSlice]) .cellUnd
        expectErr "cellund/tag01-external-not-accepted"
          (runLdOptStdAddrDirect #[.slice invalidTag01Slice]) .cellUnd
        expectErr "cellund/tag11-var-not-accepted"
          (runLdOptStdAddrDirect #[.slice invalidTag11Slice]) .cellUnd
        expectErr "cellund/tag10-no-anycast-bit"
          (runLdOptStdAddrDirect #[.slice shortTag10OnlySlice]) .cellUnd
        expectErr "cellund/tag10-anycast-one"
          (runLdOptStdAddrDirect #[.slice anycastOneSlice]) .cellUnd
        expectErr "cellund/tag10-short-266"
          (runLdOptStdAddrDirect #[.slice shortStd266Slice]) .cellUnd
        expectErr "cellund/tag10-short-after-anycast"
          (runLdOptStdAddrDirect #[.slice shortAfterAnycastSlice]) .cellUnd }
    ,
    { name := "unit/opcode/decode-and-assembler"
      run := do
        let nonQuietOnly ←
          match assembleCp0 [ldOptStdAddrInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble non-quiet failed: {e}")
        if nonQuietOnly.bits = natToBits 0xfa50 16 then
          pure ()
        else
          throw (IO.userError s!"ldoptstdaddr encode mismatch: got bits {nonQuietOnly.bits}")

        let quietOnly ←
          match assembleCp0 [ldOptStdAddrQInstr] with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble quiet failed: {e}")
        if quietOnly.bits = natToBits 0xfa51 16 then
          pure ()
        else
          throw (IO.userError s!"ldoptstdaddrq encode mismatch: got bits {quietOnly.bits}")

        let program : Array Instr := #[ldOptStdAddrInstr, ldOptStdAddrQInstr, .add]
        let code ←
          match assembleCp0 program.toList with
          | .ok cell => pure cell
          | .error e => throw (IO.userError s!"assemble sequence failed: {e}")
        let s0 := Slice.ofCell code
        let s1 ← expectDecodeStep "decode/ldoptstdaddr" s0 ldOptStdAddrInstr 16
        let s2 ← expectDecodeStep "decode/ldoptstdaddrq" s1 ldOptStdAddrQInstr 16
        let s3 ← expectDecodeStep "decode/tail-add" s2 .add 8
        if s3.bitsRemaining = 0 then
          pure ()
        else
          throw (IO.userError s!"decode/end: expected exhausted slice, got {s3.bitsRemaining} bits remaining") }
    ,
    { name := "unit/dispatch/non-ldoptstdaddr-falls-through"
      run := do
        expectOkStack "dispatch/fallback"
          (runLdOptStdAddrDispatchFallback #[.null])
          #[.null, intV 450] }
  ]
  oracle := #[
    mkLdOptStdAddrCase "ok/none-empty" #[.slice (mkOptNoneSlice #[])],
    mkLdOptStdAddrCase "ok/none-with-tail-7" #[.slice (mkOptNoneSlice tailBits7)],
    mkLdOptStdAddrCase "ok/std-wc0-addr0" #[.slice (mkOptStdSlice 0 0)],
    mkLdOptStdAddrCase "ok/std-wc1-addr255" #[.slice (mkOptStdSlice 1 255)],
    mkLdOptStdAddrCase "ok/std-wc42-addr4660" #[.slice (mkOptStdSlice 42 4660)],
    mkLdOptStdAddrCase "ok/std-wc255-addr65535" #[.slice (mkOptStdSlice 255 65535)],
    mkLdOptStdAddrCase "ok/std-with-tail-11" #[.slice (mkOptStdSlice 17 12345 tailBits11)],
    mkLdOptStdAddrCase "ok/std-with-tail-and-ref" #[.slice stdWithTailAndRefSlice],
    mkLdOptStdAddrCase "ok/deep-stack-none" #[intV 7, .slice (mkOptNoneSlice tailBits7)],
    mkLdOptStdAddrCase "ok/deep-stack-std" #[.cell Cell.empty, .slice (mkOptStdSlice 7 42 tailBits7)],

    mkLdOptStdAddrCase "underflow/empty" #[],
    mkLdOptStdAddrCase "type/top-not-slice-null" #[.null],
    mkLdOptStdAddrCase "type/top-not-slice-int" #[intV 1],
    mkLdOptStdAddrCase "type/deep-top-not-slice" #[.slice (mkOptNoneSlice #[]), .null],

    mkLdOptStdAddrCase "cellund/no-tag-bits-0" #[.slice emptyBitsSlice],
    mkLdOptStdAddrCase "cellund/no-tag-bits-1" #[.slice oneBitSlice],
    mkLdOptStdAddrCase "cellund/tag01" #[.slice invalidTag01Slice],
    mkLdOptStdAddrCase "cellund/tag11" #[.slice invalidTag11Slice],
    mkLdOptStdAddrCase "cellund/tag10-no-anycast-bit" #[.slice shortTag10OnlySlice],
    mkLdOptStdAddrCase "cellund/tag10-anycast-one" #[.slice anycastOneSlice],
    mkLdOptStdAddrCase "cellund/tag10-short-266" #[.slice shortStd266Slice],
    mkLdOptStdAddrCase "cellund/tag10-short-after-anycast" #[.slice shortAfterAnycastSlice],

    mkLdOptStdAddrCase "gas/exact-cost-succeeds" #[.slice (mkOptNoneSlice #[])]
      #[.pushInt (.num ldOptStdAddrSetGasExact), .tonEnvOp .setGasLimit, ldOptStdAddrInstr],
    mkLdOptStdAddrCase "gas/exact-minus-one-out-of-gas" #[.slice (mkOptNoneSlice #[])]
      #[.pushInt (.num ldOptStdAddrSetGasExactMinusOne), .tonEnvOp .setGasLimit, ldOptStdAddrInstr]
  ]
  fuzz := #[
    { seed := 2026021020
      count := 320
      gen := genLdOptStdAddrFuzzCase }
  ]

initialize registerSuite suite

end Tests.Instr.Cell.LDOPTSTDADDR
